(ns lang.cg3
  (:require
   [clojure.string :as string]
   [lang.name-resolution :as nr]
   [lang.module :as lm]
   [clojure.java.io :as io]
   [lang.type-checker :as tc]
   [lang.parser :as parser]
   [clojure.core.match :refer [match]]
   [lang.jnsn :as jnsn])
  (:import
   [org.objectweb.asm ClassVisitor ClassWriter MethodVisitor Opcodes Handle Type Label]
   [java.lang.invoke CallSite LambdaMetafactory MethodHandle MethodHandles$Lookup MethodType]
   [clojure.lang DynamicClassLoader]))

(defrecord MethodInfo [access name desc emit
                       local-var-index])
(defn new-method-info
  ([] (->MethodInfo [] nil nil [] nil))
  ([m] (map->MethodInfo (merge (new-method-info) m))))

(defrecord ClassInfo [access name fields methods])
(defn new-class-info
  ([] (->ClassInfo [] nil [] []))
  ([m] (map->ClassInfo (merge (new-class-info) m))))

(defrecord Typed [type insns nocapture])
(defrecord TypeBinding [type
                        injector-class injector-field injector-ctor
                        record-class record-fields record-ctor])

(defn new-value-binding
  [java-type]
  (->TypeBinding java-type nil nil nil nil nil nil))

;; each context is either class or method
(defrecord CompileContext [class method value-scope type-scope])

(defn new-compile-context
  ([] (->CompileContext nil nil {} {}))
  ([m] (map->CompileContext (merge (new-compile-context) m))))

(defrecord CompileState [context-stack anon-fn-counter class-loader
                         fni-cache])

(defn new-compile-state
  ([] (->CompileState [] 0 (clojure.lang.DynamicClassLoader.) {}))
  ([m] (map->CompileState (merge (new-compile-state) m))))

(defn push-context
  [state new-context]
  (update state :context-stack conj new-context))

(defn get-context
  [{:keys [context-stack]}]
  (peek context-stack))

(defn dup-context
  [state]
  (update state :context-stack conj (peek (:context-stack state))))

(defn pop-context
  [state]
  (update state :context-stack pop))

(defn pop-lexical
  [{:keys [context-stack] :as state}]
  (let [[here prev] (rseq context-stack)
        {:keys [value-scope type-scope]} prev]
    (assoc state :context-stack
           (conj (subvec context-stack 0 (- (count context-stack) 2))
                 (assoc here
                        :type-scope type-scope
                        :value-scope value-scope)))))

(defn push-class
  [state m]
  (push-context state (new-compile-context {:class (new-class-info m)})))

(defn push-method
  [state m]
  (push-context state (new-compile-context {:method (new-method-info m)})))

(defn define-class!
  [state]
  (let [{:keys [name] :as cc} (:class (get-context state))
        _ (when-not cc (throw (ex-info "Class context expected" {})))
        _ (when-not name (throw (ex-info "Name is required!" {})))
        java-name (string/replace name "/" ".")
        class-bytes (jnsn/create-class cc)]
    #_(io/copy class-bytes (io/file (str java-name ".class")))
    #_(prn 'Defined java-name 'wrote (str java-name ".class"))
    (.defineClass ^DynamicClassLoader (:class-loader state) java-name class-bytes nil)
    state))

(defn pop-class
  [state]
  (-> state
      (define-class!)
      (pop-context)))

(defn update-current-context
  ([{:keys [context-stack] :as state} k f]
   (assoc state :context-stack
          (conj (pop context-stack) (update (peek context-stack) k f))))
  ([{:keys [context-stack] :as state} k f & more]
   (assoc state :context-stack
          (conj (pop context-stack) (apply update (peek context-stack) k f more)))))

(defn update-context
  ([s ct f & more] (update-context s ct #(apply f % more)))
  ([{:keys [context-stack] :as state} context-type func]
   
   (loop [[current & up] (rseq context-stack)
          down []
          left (count context-stack)]
     (cond
       (nil? current)
       (throw (ex-info "no such context" {:context-type context-type}))

       (nil? (get current context-type))
       (recur up (conj down current) (dec left))

       :else
       (assoc state :context-stack
              (into (conj (subvec context-stack 0 (dec left))
                          (update current context-type func))
                    (rseq down)) )))))

(defn pop-method
  [state]
  (let [mc (:method (get-context state))
        _ (when-not mc (throw (ex-info "Method context expected!" (get-context state))))]
    (-> state
        (update-context :class #(update % :methods conj mc))
        (pop-context))))

(defn new-local-var!
  [state var-type  p]
  (let [mc (:method (get-context state))
        _ (when-not mc (throw (ex-info "Method context expected!" (get-context state))))
        idx (:local-var-index mc)
        _ (when-not mc (throw (ex-info "Need to know local-var-index of method!" {:name (:name mc)} )))
        size (case var-type
               ("J" "D") 2
               1)]
    (deliver p idx)
    (update-context state :method update :local-var-index inc)))

(defn emit
  ([state v] (update-context state :method #(update % :emit into v)))
  ([state v & vs] (emit state (reduce into v vs))))

(defn emit1
  [state v]
  (update-context state :method #(update % :emit conj v)))

(defn add-field
  [state field]
  (update-context state :class #(update % :fields conj field)))

(defn resolver
  ([state func] (resolver state func nil))
  ([{:keys [context-stack] :as state} func error-func]
   (or (some func (rseq context-stack))
       (and error-func (error-func))
       (throw (ex-info "could not resolve" {})))))

(defn resolve-type
  [state type-name]
  (resolver state
            #(-> % :type-scope (get type-name))
            #(throw (ex-info "Could not resolve type" {:type type-name}))))

(defn resolve-var
  [state var-name]
  (resolver state
            #(-> % :value-scope (get var-name))
            #(throw (ex-info "Could not resolve var" {:var var-name}))))

(defn current-class-name
  [state]
  (resolver state #(-> % :class :name)))

(defn add-binding
  ([state name type insns]
   (update-context state :value-scope #(assoc % name (->Typed type insns nil))))
  ([state name type insns m]
   (let [d {:name name :type type :insns insns}]
     (update-context state :value-scope #(assoc % name (map->Typed (merge d m)))))))

(defn add-bindings
  [state bindings]
  (update-current-context state :value-scope into bindings))

(defn add-top-level-type
  [state type-name binding]
  (update state :context-stack update 0 update :type-scope assoc type-name binding))

;; functional interface generation

(defn munge-type
  [s]
  (case (subs s 0 1)
    "L" "O"
    ;; replace [ with A so the method name is legal
    "[" (str "A" (munge-type (subs s 1)))
    s))

(defn ^String erase-method-desc
  [desc]
  ;; turn all reference types into object
  (string/replace desc #"L.*?;" "Ljava/lang/Object;"))

(defn functional-interface-class
  [return-type arg-types]
  (str "lang/fni/fn" (apply str (map munge-type (cons return-type arg-types)))))

(defn generate-functional-interface!
  [state fni-name method-desc]
  (-> state
      (push-class {:name fni-name
                   :access [:public :abstract :interface]
                   :methods [{:name "apply"
                              :access [:public :abstract]
                              :desc method-desc}]})
      (pop-class)
      (update :fni-cache assoc fni-name true)))

(defn ^String make-method-descriptor
  [return-type arguments]
  (str "(" (apply str arguments) ")" return-type))

(defn ensure-functional-interface
  [{:keys [fni-cache] :as state} return-type arg-types]
  (let [fni (functional-interface-class return-type arg-types)]
    (cond
      (contains? fni-cache fni) state
      (try (Class/forName fni) (catch Exception e nil)) state
      :else 
      (generate-functional-interface!
       state fni
       (erase-method-desc (make-method-descriptor return-type arg-types))))))

;; types

(defn specialize-type
  ([t] (specialize-type t {}))
  ([{:keys [ast/type primitive variable body domain return injectors fields operator] :as t} vars]
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
                             [inj (when inj-type (specialize-type inj-type))])))
     :record (assoc t :fields
                    (into {}
                          (for [[n t] fields]
                            [n (specialize-type t)]))))))

(defn class->ref-type
  [c]
  (str "L" c ";"))

(defn ref-type->class
  [s]
  (case (subs s 0 1)
    "L" (subs s 1 (dec (count s)))
    (throw (ex-info "Expected reference type" {:type s}))))

(defn type->class-name
  [state {:keys [ast/type primitive domain return element fields] :as t}]
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
    (class->ref-type (functional-interface-class
                      (type->class-name state return)
                      [(type->class-name state domain)]))
    
    :named
    (:type (resolve-type state (:name t)))
    
    :record
    (let [record-key (set (keys fields))]
      (:type (resolve-type state record-key)))
    (throw (ex-info "can't make java type" t))))

;; pre-processing

(defn ast-postwalk
  [f root]
  (letfn [(walk-seq [fs] (mapv walk fs))
          (walk [{:keys [ast/term] :as t}]
            (f (case term
                 (:atom :symbol) t
                 :application (-> t (update :function walk) (update :arguments walk-seq))
                 :sequence (-> t (update :operations walk-seq))
                 :lambda (-> t (update :argument walk) (update :body walk))
                 :variant (-> t (update-in [:variant :value] walk))
                 :recur (-> t (update :body walk))
                 :match (-> t
                            (update :body walk)
                            (assoc :branches (vec (for [b (:branches t)] (update b :action walk)))))
                 :record (-> t (assoc :fields (into {}
                                                    (for [[f v] (:fields t)]
                                                      [f (walk v)]))))
                 :access (match t
                                {:object obj :field {:ast/term :application :arguments args}}
                                (-> t (update-in [:field :arguments] walk-seq)
                                    (update :object walk)))
                 (cond
                   (:reference t) t
                   (nil? t) nil
                   :else (throw (ex-info "Unhandled term" {:t t}))))))]
    (walk root)))

(defn pattern-bindings
  [pat]
  (match pat
         {:ast/pattern :wildcard} #{}
         {:ast/pattern :atom} #{}
         {:ast/pattern :symbol :symbol s} #{s}
         {:ast/pattern :variant :variant {:value vpat}} (if vpat (recur vpat) #{})
         {:ast/pattern :variant} #{}

         {:ast/pattern :record :fields fields}
         (reduce into (map pattern-bindings (vals fields)))

         [& pats]
         (reduce into (map pattern-bindings pats))))

(defn ref-set-walker
  [{:keys [ast/term type-checker.term/type] :as t}]
  (case term
    :symbol      (assoc t :ref-set {(:symbol t) type})
    :application (assoc t :ref-set (into (:ref-set (:function t))
                                         (map :ref-set (:arguments t))))
    :sequence    (assoc t :ref-set (reduce merge (map :ref-set (:operations t))))
    :lambda      (assoc t :ref-set (dissoc (:ref-set (:body t))
                                           ;; remove type annotation 
                                           (dissoc (:argument t) :type)))
    :match       (assoc t :ref-set (reduce merge (:ref-set (:body t))
                                           (for [{:keys [patterns action]} (:branches t)]
                                             (apply dissoc (:ref-set action) (pattern-bindings patterns)))))
    :record      (assoc t :ref-set (reduce merge (map :ref-set (vals (:fields t)))))
    :access      (assoc t :ref-set (reduce merge (:ref-set (:object t))
                                           (map :ref-set (:arguments (:field t)))))
    :variant     (assoc t :ref-set (some-> t :variant :value :ref-set))
    :recur       (assoc t :ref-set (-> t :body :ref-set))
    t))

(defn analyze-captures
  [ast]
  (ast-postwalk ref-set-walker ast))

;; 

(defn atom-insns
  [{:keys [atom value]}]
  (case atom
    :integer
    [[:new "java/math/BigInteger"]
     [:dup]
     [:ldc value]
     [:invokespecial "java/math/BigInteger" "<init>" "(Ljava/lang/String;)V" false]]

    :string
    [[:ldc value]]

    :boolean
    [[:ldc (case value true 1 false 0)]
     [:invokestatic "java/lang/Boolean" "valueOf" "(Ljava/lang/String;)Ljava/lang/Boolean;"]]))

;; emit-lambda

(def lambda-metafactory-handle
  (Handle. Opcodes/H_INVOKESTATIC "java/lang/invoke/LambdaMetafactory" "metafactory"
           "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;"))

(defn arg-bindings
  [arg-names arg-java-types]
  (map (fn [idx name  java-type]
         [name (->Typed java-type [[:aload idx]] nil)])
       (range)
       arg-names
       arg-java-types))

(declare emit-term)

(defn ref-set->captures
  [state ref-set]
  (into {}
   (for [[r t] ref-set
         :when (not (:nocapture (resolve-var state r)))]
     [r (type->class-name state (specialize-type t))])))

(defn return-insns
  [return-type]
  (let [rt (or return-type "V")]
    (case (subs rt 0 1)
      "L" [[:checkcast (subs return-type 1 (dec (count return-type)))]
           [:areturn]]
      "V" [[:return]]
      "I" [[:ireturn]])))

(defn emit-lambda
  [state {:keys [type-checker.term/type body argument ref-set] :as term} recur-name]
  (let [argument (dissoc argument :type)
        spec-type (specialize-type type)
        arg-type (->> spec-type :domain (type->class-name state))
        return-type (->> spec-type :return (type->class-name state))
        method-name (or recur-name (str (gensym "fn")))
        captures (ref-set->captures state ref-set)
        static-method-desc (make-method-descriptor return-type (concat (vals captures) [arg-type]))
        lambda-method-desc (make-method-descriptor return-type [arg-type])
        lambda-type (class->ref-type (functional-interface-class return-type [arg-type]))]
    (-> state
        (ensure-functional-interface return-type [arg-type])
        (push-method {:access [:public :static]
                      :name method-name
                      :desc static-method-desc
                      ;; inc accounts for our single argument
                      :local-var-index (inc (count captures))})
        (add-bindings (arg-bindings (concat (keys captures) [argument])
                                    (concat (vals captures) [arg-type])))
        (emit-term body)
        (emit (return-insns return-type))
        (pop-method)
        (emit (vec (mapcat :insns (for [v (keys captures)]
                                    (resolve-var state v))))
              [[:invokedynamic "apply"
                (make-method-descriptor lambda-type (vals captures))
                lambda-metafactory-handle
                [(Type/getType (erase-method-desc lambda-method-desc))
                 (Handle. Opcodes/H_INVOKESTATIC (current-class-name state) method-name static-method-desc)
                 (Type/getType lambda-method-desc)]]]))))

;; patterns

(defn atom-comparison-insns
  [atom-type]
  (case atom-type
    :integer [[:invokevirtual "java/math/BigInteger" "compareTo" "(Ljava/math/BigInteger;)I" false]]
    :string [[:invokevirtual "java/lang/String" "compareTo" "(Ljava/lang/String;)I" false]]
    :boolean [[:invokevirtual "java/lang/Boolean" "compareTo" "(Ljava/lang/Boolean;)I" false]]))

(defn emit-one-pattern
  [state {:keys [type-checker.pattern/type] :as pattern} body-insns me next]
  (match pattern
         {:ast/pattern :wildcard}
         (emit1 state [:label me])

         {:ast/pattern :symbol :symbol sym}
         (let [var (promise)
               type (type->class-name state (specialize-type type))]
           (-> state
               (new-local-var! type var)
               (emit [[:label me]]
                     body-insns
                     [[:astore @var]])
               (add-binding sym type [[:aload @var]])))

         {:ast/pattern :atom :atom atom}
         (emit state
               [[:label me]]
               (atom-insns atom)
               body-insns
               (atom-comparison-insns (:atom atom))
               [[:ifne next]])

         {:ast/pattern :record :fields fields}
         (let [t (type->class-name state (specialize-type type))
               record-key (set (keys fields))
               {:keys [type record-class record-fields]} (resolve-type state record-key)]
           (reduce (fn [state [field fpat]]
                     (let [field-type (get record-fields (:name field))
                           field-var (promise)]
                       (-> state
                           (new-local-var! field-type field-var)
                           (emit body-insns
                                 [[:getfield record-class (:name field) field-type]
                                  [:astore @field-var]])
                           (emit-one-pattern fpat [[:aload @field-var]] (Label.) next))))
                   (emit1 state [:label me])
                   fields))
         
         {:ast/pattern :variant :variant {:injector inj :value vpat}}
         (let [{:keys [type injector-class injector-field]} (resolve-type state inj)
               match-outer (vec (concat [[:label me]]
                                        body-insns
                                        [[:instanceof injector-class]
                                         [:ifeq next]]))]
           (if-not vpat
             (emit state match-outer)
             (let [inner-var (promise)]
               (-> state
                   (new-local-var! injector-field inner-var)
                   (emit match-outer
                         body-insns
                         [[:checkcast injector-class]
                          [:getfield injector-class "e" injector-field]
                          [:astore @inner-var]])
                   (emit-one-pattern vpat [[:aload @inner-var]] (Label.) next)))))))

(defn emit-patterns-list
  ;; creates linked jump/label structure made of pattern comparisons
  [state [pattern & more-patterns :as aa] body-insns me next-branch]
  (let [next-label (if-not more-patterns next-branch (Label.))]
    (-> state
        (emit-one-pattern pattern body-insns me next-label)
        (cond-> more-patterns (recur more-patterns body-insns next-label next-branch)))))

(defn emit-pattern-branches
  ;; creates linked jump/label structure made of match branches
  [state [{:keys [patterns action]} & more-branches :as aa] body-insns me success failure]
  (let [next-label (if-not more-branches failure (Label.))]
    (-> state
        (emit-patterns-list patterns body-insns me next-label)
        (emit-term action)
        (emit1 [:goto success])
        (cond-> more-branches (recur more-branches body-insns next-label success failure)))))

(defn emit-pattern-or-failure
  [state {:keys [body branches] :as term} body-insns]
  (let [success (Label.)
        failure (Label.)]
    (-> state
        (emit-pattern-branches branches body-insns (Label.) success failure)
        (emit [[:label failure]
               [:new "java/lang/IllegalArgumentException"]
               [:dup]
               [:ldc "No match"]
               [:invokespecial "java/lang/IllegalArgumentException" "<init>" "(Ljava/lang/String;)V" false]
               [:athrow]
               [:label success]]))))

(defn emit-pattern
  [state {:keys [body branches] :as term}]
  (let [body-type (specialize-type (:type-checker.term/type body))
        body-var (promise)
        success (Label.)
        failure (Label.)]
    (-> state
        (new-local-var! body-type body-var)
        (emit-term body)
        (emit [[:astore @body-var]])
        (emit-pattern-or-failure term [[:aload @body-var]]))))

;; emit-term

(defn signature->desc
  [sig]
  (let [return-type (peek sig)
        arg-types (pop sig)]
    (make-method-descriptor
     (class->ref-type (string/replace return-type "." "/"))
     (for [a arg-types]
       (class->ref-type (string/replace a "." "/"))))))

(defn apply-curried
  [state [arg & more]]
  (if-not arg
    state
    (-> state
        (emit-term arg)
        (emit1 [:invokeinterface "lang/fni/fnOO" "apply" "(Ljava/lang/Object;)Ljava/lang/Object;" true])
        (recur more))))

(defn emit-term
  ([state term] (emit-term state term nil))
  ([state {:keys [type-checker.term/type] :as term} recur-name]
   (match term
          {:ast/term :symbol :symbol sym}
          (emit state (:insns (resolve-var state sym)))

          {:ast/term :sequence :operations body}
          (reduce emit-term state body)

          {:ast/term :atom :atom atom}
          (emit state (atom-insns atom))

          {:ast/term :recur :reference recur-ref :body body}
          (emit-term state body (:name recur-ref))

          {:ast/term :lambda}
          (emit-lambda state term recur-name)

          {:ast/term :application :function func :arguments args}
          (apply-curried (emit-term state func) args)

          {:ast/term :match}
          (-> state
              (dup-context)
              (emit-pattern term)
              (pop-lexical))
          
          {:ast/term :variant :variant {:injector inj :value value}}
          (let [{:keys [injector-class injector-ctor]} (resolve-type state inj)]
            (-> state
                (emit [[:new injector-class]
                       [:dup]])
                (cond-> value (emit-term value))
                (emit1 [:invokespecial injector-class "<init>" injector-ctor false])))

          {:ast/term :record :fields fields}
          (let [record-key (set (keys fields))
                {:keys [type record-class record-fields record-ctor]} (resolve-type state record-key)
                fvals (zipmap (map :name (keys fields)) (vals fields))]
            (-> (reduce-kv (fn [state field ftype]
                             (emit-term state (get fvals field)))
                           (emit state [[:new record-class]
                                        [:dup]])
                           ;; push the args in the order the ctor expects (not the order given)
                           record-fields)
                (emit [[:invokespecial record-class "<init>" record-ctor false]])))

          {:ast/term :access :object obj :field {:ast/term :application :function func :arguments args}}
          (-> (reduce emit-term (emit-term state obj) args)
              (emit1 [:invokevirtual
                      (string/join "/" (:name (:in (:symbol func))))
                      (:name (:symbol func))
                      (signature->desc (:signature (:type-checker.term/type func)))
                      false])))))

;; emit-type

(declare emit-type)
(defn emit-injectors
  ([state inj-types-map]
   (reduce-kv emit-injectors state inj-types-map))
  ([state0 {:keys [name] :as reference} arg-type]
   (let [state (if-not arg-type state0 (emit-type state0 {:name (str name "$inner")} arg-type))
         variant-super (current-class-name state)
         class-name (str variant-super "$" name)
         field-name "e"
         field-desc (when arg-type (type->class-name state arg-type))
         ctor-desc (make-method-descriptor "V" (some-> field-desc list))]
     (-> state
         (push-class {:name class-name
                      :superclass variant-super
                      :access [:public]
                      :fields (when arg-type
                                [{:name field-name
                                  :access [:public :final]
                                  :desc field-desc}])})
         (push-method {:name "<init>"
                       :access [:public]
                       :desc ctor-desc})
         (emit [[:aload 0]
                [:invokespecial variant-super "<init>" "()V" false]]
               (when arg-type
                 [[:aload 0]
                  [:aload 1]
                  [:putfield class-name field-name field-desc]])
               [[:return]])
         (pop-method)
         (pop-class)
         (add-top-level-type reference
                             (map->TypeBinding {:type (class->ref-type class-name)
                                                :injector-class class-name
                                                :injector-field field-desc
                                                :injector-ctor ctor-desc}))))))

(defn emit-type
  [state name type]
  (let [current-class (current-class-name state)
        type-name (:name name)
        class-name (str current-class "$" type-name)]
    (match type
           {:ast/type :primitive}
           state
           
           {:ast/type :variant :injectors inj-types-map}
           (-> state
               (push-class {:name class-name
                            :access [:public]
                            :methods [{:name "<init>"
                                       :access [:public]
                                       :desc "()V"
                                       :emit [[:aload 0]
                                              [:invokespecial "java/lang/Object" "<init>" "()V" false]
                                              [:return]]}]})
               (define-class!)
               (add-top-level-type name {:type (class->ref-type class-name)})
               (emit-injectors inj-types-map)
               (pop-context))
           
           {:ast/type :record :fields fields}
           (let [record-key (set (keys fields))
                 java-fields (into {}
                                   (for [[n t] fields]
                                     [(:name n) (type->class-name state (specialize-type t))]))
                 value-type (class->ref-type class-name)
                 ctor-desc (make-method-descriptor "V" (vals java-fields))]
             (-> state
                 (add-top-level-type record-key (map->TypeBinding {:type value-type
                                                                   :record-class class-name
                                                                   :record-fields java-fields
                                                                   :record-ctor ctor-desc}))
                 (push-class {:name class-name
                              :access [:public]
                              :fields (for [[n t] java-fields]
                                        {:access [:public :final]
                                         :name n
                                         :desc t})})
                 (push-method {:name "<init>" :access [:public] :desc ctor-desc})
                 (emit [[:aload 0]
                        [:invokespecial "java/lang/Object" "<init>" "()V" false]]
                       (-> (fn [i [n t]]
                             [[:aload 0]
                              [:aload (inc i)]
                              [:putfield class-name n t]])
                           (mapcat (range) java-fields))
                       [[:return]])
                 (pop-method)
                 (pop-class))))))

;; emit-toplevel

(def builtin-types
  (into {}
        (for [[ref type] lm/builtins
              :when (not= "Array" (:name ref))]
          [ref (new-value-binding (type->class-name nil (specialize-type type)))])))

(defn emit-toplevel
  [state {:keys [type-checker.term/type] :as term}]
  (match term
         {:ast/definition :module :name {:name name-parts} :definitions defs}
         (let [name (string/join "/" name-parts)]
           (-> state
               (push-class {:name name :access [:public]})
               (update-current-context :type-scope into builtin-types)
               (push-method {:name "<clinit>"
                             :desc "()V"
                             :access [:static]})
               (match st (reduce emit-toplevel st defs))
               (emit1 [:return])
               (pop-method)
               (pop-class)))
         
         {:ast/definition :constant :body body :name name}
         (let [current-class (current-class-name state)
               field-name (:name name)
               field-type (type->class-name state (specialize-type type))]
           (-> state
               (add-field {:access [:public :static :final]
                           :name field-name
                           :desc field-type})
               (add-binding name field-type [[:getstatic current-class field-name field-type]] {:nocapture true})
               (emit-term (analyze-captures body))
               (emit [[:checkcast (ref-type->class field-type)]                      
                      [:putstatic current-class field-name field-type]])))

         {:ast/definition :type :body body :name name}
         (emit-type state name (specialize-type body))))

(defn compile-module
  [module]
  (-> (new-compile-state)
      (emit-toplevel module)))

