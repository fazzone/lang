(ns lang.cg2compiler
  (:require
   [lang.cg2 :as cg]
   [clojure.core.match :refer [match]]
   [clojure.java.io :as io]
   [clojure.string :as string]
   [clojure.set :as set]
   [lang.compiler :as lc]
   [lang.module :as lm]
   [lang.name-resolution :as nr]
   [lang.parser :as parser]
   [lang.type-checker :as tc])
  (:import [org.objectweb.asm Label Opcodes]))

;; lang types to java types

(defn specialize-type
  ([t] (specialize-type t {}))
  ([{:keys [ast/type primitive variable body domain return injectors operator] :as t} vars]
   (case type
     :recur (recur body vars)
     :forall (do
               (when-not (:id variable)
                 (throw (ex-info "No ID" variable)))
               (recur body (assoc vars (:id variable) {:ast/type :primitive :primitive :object})))
     :function (assoc t
                      :domain (specialize-type domain vars)
                      :return (specialize-type return vars))
     :named t
     :primitive t
     :universal-variable (do
                           (when-not (:id t)
                             (throw (ex-info "No ID" t)))
                           (or (get vars (:id t))
                               (do #_(prn "bad universal?")
                                   {:ast/type :primitive :primitive :object})))
     :existential-variable {:ast/type :primitive :primitive :object}
     :application operator
     :variant (assoc t :injectors
                     (into {}
                           (for [[inj inj-type] injectors]
                             [inj (when inj-type (specialize-type inj-type))]))))))

(defn nth-return-type
  [{:keys [return] :as type} n]
  (if (= 0 n)
    type
    (recur return (dec n))))

(defn resolve-type*
  [current-context context-stack nt]
  (when-not current-context
    (throw (ex-info "Cannot resolve type" {:type nt})))
  (or (some-> current-context :type-scope (get nt))
      (recur (first context-stack) (next context-stack) nt)))

(defn resolve-named-type
  [{:keys [current-context context-stack] :as state} nt]
  (resolve-type* current-context context-stack nt))

(defn type->class-name
  [state {:keys [ast/type primitive domain return element] :as t}]

  (case type
    :primitive
    (case primitive
      :object "Ljava/lang/Object;"
      :integer "Ljava/math/BigInteger;"
      :string "Ljava/lang/String;"
      :array (str "[" (type->class-name state element))
      :int "I"
      :boolean "B"
      :unit "V")

    :function
    (str "L" (cg/functional-interface-class
              (type->class-name state return)
              [(type->class-name state domain)])
         ";")
    
    :named
    (resolve-named-type state (:name t))

    (throw (ex-info "can't make java type" t))))

(defn function-arity
  ([state type] (function-arity state type 0))
  ([state type arity]
   (match type
          {:ast/type :primitive} arity
          {:ast/type :function :return r} (recur state r (inc arity))
          {:ast/type :named} (recur state (resolve-named-type state (:name type)) arity)
          (s :guard string?) arity)))

;; ast-tree-seq

(defn ast-tree-seq
  [term]
  (cons term
        (match term
               {:ast/term :lambda :argument arg :body body}
               (lazy-seq (ast-tree-seq body))
               
               {:ast/term :application :function func :arguments args}
               (concat (lazy-seq (ast-tree-seq func))
                       (map ast-tree-seq args))
               
               {:ast/term :match :body body :branches branches}
               (concat (lazy-seq (ast-tree-seq body))
                       (map ast-tree-seq branches))
               
               {:ast/term :sequence :operations body}
               (mapcat ast-tree-seq body)

               {:ast/term :atom :atom atom}
               nil

               {:ast/term :symbol :symbol sym}
               nil

               {:ast/term :variant :variant {:value v}}
               (lazy-seq (ast-tree-seq v)))))

(defn ast-postwalk
  [f root]
  (letfn [(walk-seq [fs] (mapv walk fs))
          (walk [{:keys [ast/term] :as t}]
            (f (case term
                 (:atom :symbol) t
                 :application    (-> t (update :function walk) (update :arguments walk-seq))
                 :sequence       (-> t (update :operations walk-seq))
                 :lambda         (-> t (update :argument walk) (update :body walk))
                 :match          (-> t
                                     (update :body walk)
                                     (assoc :branches (vec (for [b (:branches t)] (update b :action walk)))))
                 :variant        (-> t (update-in [:variant :value] walk))
                 :recur          (-> t (update :body walk))
                 t)))]
    (walk root)))

(defmacro langpar
  [& fs]
  `(-> (string/join " " (map pr-str (quote ~fs)))
       (string/replace "," "")
       (parser/parse-string)
       (nr/run)
       (tc/run)))

(defn ref-set-walker
  [{:keys [ast/term] :as t}]
  (case term
    :symbol      (assoc t :ref-set #{(:symbol t)})
    :application (assoc t :ref-set (into (:ref-set (:function t))
                                         (map :ref-set (:arguments t))))
    :sequence    (assoc t :ref-set (reduce into #{} (map :ref-set (:body t))))
    :lambda      (assoc t :ref-set (disj (:ref-set (:body t)) (:argument t)))
    :match       (assoc t :ref-set (reduce into (:ref-set (:body t))
                                           (map (comp :ref-set :action) (:branches t))))
    :variant     (assoc t :ref-set (-> t :value :ref-set))
    :recur       (assoc t :ref-set (-> t :body :ref-set))
    t))

(defn analyze-captures [ast]
  (ast-postwalk ast ref-set-walker))

(comment
  (defn uncurry-function-type
    ([type] (uncurry-function-type type 0))
    ([type arity]
     (match type
            {:ast/type :function :domain d :return r}
            (recur r (inc arity))
            _
            {:return-type type :arity arity}))))

(defn uncurry-function-type
  ([type arity] (uncurry-function-type type arity []))
  ([type arity argv]
   (if (= 0 arity)
     {:return-type type :arguments argv}
     (match type
            {:ast/type :function :domain d :return r}
            (recur r (dec arity) (conj argv d))
            _
            (throw (ex-info "Not a function!" {:type type}))))))

(defn ensure-lambda-context
  [state]
  ;; if the current context is a definition context,
  (if (= :definition (-> state :current-context :context-type))
    ;; update it to be a lambda context without pushing a new context, so that
    ;; we don't lose the naming information from the definition context
    (assoc-in state [:current-context :context-type] :lambda)
    ;; otherwise, we should push a new lambda context for our anonymous fn
    (cg/push-context state {:context-type :lambda})))

(declare emit)

(defn emit-lambda
  [state {:keys [type-checker.term/type argument body] :as term}]
  (let [[lambda-spine [innermost-body]] (->> (ast-tree-seq term)
                                             (split-with (comp #{:lambda} :ast/term)))
        arg-names (map :argument lambda-spine)
        arg-types (for [l lambda-spine]
                    (->> l :type-checker.term/type (specialize-type) :domain (type->class-name state)))
        return-type (type->class-name state (specialize-type (:type-checker.term/type innermost-body)))
        is-def (some-> state :current-context :context-type (= :definition))
        mc (promise)]
    (-> state
        (ensure-lambda-context)
        (cg/update-method-context {:return-type return-type})
        (cg/introduce-arguments arg-names arg-types)
        (emit innermost-body)
        (cg/out-method)
        ;; read the finished method information before we pop-context 
        (cg/<-method-context mc)
        (cg/pop-context)
        (cond->
            is-def       (cg/add-top-level-binding (:method-reference @mc) (:invoker @mc))
            #_(not is-def) #_(cg/add-pending (:invoker @mc)))
        (cg/add-pending (:invoker @mc)))))

(defn atom-comparison-emitter
  [atom-type]
  (case atom-type
    :integer (cg/invokevirtual-emitter "java/math/BigInteger" "compareTo" "(Ljava/math/BigInteger;)I")
    :string (cg/invokevirtual-emitter "java/lang/String" "compareTo" "(Ljava/lang/String;)I")
    :boolean (cg/invokevirtual-emitter "java/lang/Boolean" "compareTo" "(Ljava/lang/Boolean;)I")))

(defn emit-one-pattern
  [state {:keys [type-checker.pattern/type] :as pattern} body-emitter me next]
  (match pattern
         {:ast/pattern :wildcard}
         (cg/add-pending state (cg/visit-label-emitter me))
         
         {:ast/pattern :symbol :symbol sym}
         (let [var (promise)
               type (type->class-name state type)]
           (-> state
               (cg/<-local-var var type)
               (cg/add-pending (cg/and-then (cg/visit-label-emitter me)
                                            body-emitter
                                            (cg/local-var-store-emitter @var)))
               (cg/add-typed-binding sym type (cg/local-var-load-emitter @var))))
         
         {:ast/pattern :atom :atom atom}
         (-> state
             (cg/add-pending (cg/and-then (cg/visit-label-emitter me)
                                          (cg/atom-emitter atom)
                                          body-emitter
                                          (atom-comparison-emitter (:atom atom))
                                          (cg/jump-emitter :ifne next))))))

(defn emit-patterns-list
  ;; creates linked jump/label structure made of pattern comparisons
  [state [pattern & more-patterns :as aa] body-emitter me next-branch]
  (let [next-label (if-not more-patterns next-branch (Label.))]
    (-> state
        (emit-one-pattern pattern body-emitter me next-label)
        (cond-> more-patterns (recur more-patterns body-emitter next-label next-branch)))))

(defn emit-pattern-branches
  ;; creates linked jump/label structure made of match branches
  [state [{:keys [patterns action]} & more-branches :as aa] body-emitter me success failure]
  (let [next-label (if-not more-branches failure (Label.))]
    (-> state
        (emit-patterns-list patterns body-emitter me next-label)
        (emit action)
        (cg/add-pending (cg/jump-emitter :goto success))
        (cond-> more-branches (recur more-branches body-emitter next-label success failure)))))

(defn emit-pattern
  [state {:keys [body branches] :as term}]
  (let [body-type (specialize-type (:type-checker.term/type body))
        body-var (promise)
        success (Label.)
        failure (Label.)]
    (-> state
        ;; Create a new local variable, evaluate the match body, store in that var
        (cg/<-local-var body-var (type->class-name state body-type))
        (emit body)
        (cg/add-pending (cg/local-var-store-emitter @body-var))
        ;; emit the pattern branches.  A label will be created before any matching but we don't care
        (emit-pattern-branches branches (cg/local-var-load-emitter @body-var) (Label.) success failure)
        (cg/add-pending (cg/and-then (cg/visit-label-emitter failure)
                                     (cg/throw-emitter "java/lang/IllegalArgumentException" "No match")
                                     (cg/visit-label-emitter success))))))

(defn emit
  [state {:keys [type-checker.term/type] :as term}]
  (match term
         {:ast/term :recur :reference ref :body body}
         (-> state
             (cg/push-context {:context-type :definition})
             (cg/in-method {:method-reference ref :method-name (:name ref)})
             (emit body))

         {:ast/term :lambda}
         (emit-lambda state term)
         
         {:ast/term :application :function func :arguments args}
         (let [function-type (specialize-type (:type-checker.term/type func))
               {:keys [return-type arguments]} (uncurry-function-type function-type (count args))]
           (-> (reduce emit (emit state func) args)
               (cg/add-pending (cg/fni-invoker-emitter
                                (type->class-name state return-type)
                                (for [t arguments]
                                  (type->class-name state t)))
                               #_(cg/fn-invoker-emitter 1))))
         
         {:ast/term :match}
         (-> state
             (cg/dup-context)
             (emit-pattern term)
             (cg/pop-lexical))
         
         ;; e.g. [:none]
         {:ast/term :variant :variant {:injector inj :value nil}}
         (let [injector-class (resolve-named-type state inj)]
           (cg/add-pending state (cg/and-then (cg/new-object-emitter injector-class)
                                              (cg/constructor-call-emitter injector-class "()V"))))
         
         ;; e.g. [:some "ok"]
         {:ast/term :variant :variant {:injector inj :value value}}
         (let [injector-class (resolve-named-type state inj)]
           (-> state
               (cg/add-pending (cg/new-object-emitter injector-class))
               (emit value)
               (cg/add-pending (cg/constructor-call-emitter injector-class "(Ljava/lang/Object;)V"))))
         
         
         {:ast/term :sequence :operations body}
         (reduce emit state body)

         {:ast/term :atom :atom atom}
         (cg/add-pending state (cg/atom-emitter atom))

         {:ast/term :symbol :symbol sym}
         (cg/reference-variable state sym)))


(defn <-class-ident
  [s p]
  (cg/<-get-in s p [:current-context :class-context :class-ident]))

(defn <-method-desc
  [s]
  (cg/<-get-in [:current-context :method-context :method-descriptor]))

(defn emit-variant-definition
  [state {:keys [name] :as reference} type]
  (let [{:keys [class-ident]} (cg/get-class-context state)
        subclass-context (promise)]
    (-> state
        (cg/push-context)
        (cg/in-inner-class name class-ident)
        ;; do not emit inner field for no-arg injectors
        (cond-> type (cg/add-instance-field "e" (type->class-name state type)))
        (cg/add-constructor class-ident "()V")
        (cg/<-class-context subclass-context)
        (cg/out-class)
        (cg/pop-context)
        ;; not needed?
        (cg/add-top-level-type reference (:class-ident @subclass-context)))))

(defn emit-type-definition
  [state type]
  (match type
         {:ast/type :variant :injectors inj-types-map}
         (reduce-kv emit-variant-definition state inj-types-map)))

(defn ee
  [state {:keys [type-checker.term/type] :as term}]
  (match term
         {:ast/definition :module :name {:name [name]} :definitions defs}
         (-> state
             (cg/in-top-level-class name)
             (cg/push-context)
             (cg/in-method {:method-name "<clinit>" :return-type "V" :access [:static]})
             (match st (reduce ee st defs))
             (cg/out-method)
             (cg/pop-context)
             (cg/out-class))

         {:ast/definition :constant :body body :name name}
         (let [desc (type->class-name state (specialize-type type))
               {:keys [class-ident]} (cg/get-class-context state)]
           (-> state
               (cg/add-static-field! (:name name) desc identity )
               (emit body)
               (cg/add-pending (cg/field-insn-emitter Opcodes/PUTSTATIC class-ident (:name name) desc))))

         {:ast/definition :type :name name :body body}
         (let [typename (:name name)
               class-ident (promise)]
           (-> state
               (cg/push-context)
               (cg/in-inner-class typename "java/lang/Object")
               (cg/add-constructor "java/lang/Object" "()V")
               (cg/define-class!)
               (emit-type-definition (specialize-type body))
               (<-class-ident class-ident)
               (cg/out-class)
               (cg/pop-context)
               (cg/add-top-level-type name (str "L" @class-ident ";"))))))

(defn compile-module
  [module]
  (let [nst (cg/new-compile-state)]
    (-> nst
        #_(assoc :class-visitor-mapper cg/pcv)
        (assoc-in [:current-context :type-scope]
                  (into {}
                        (for [[ref type] lm/builtins
                              :when (not= "Array" (:name ref))]
                          [ref (type->class-name nst (specialize-type type))])))
        (ee module))))

