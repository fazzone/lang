(ns lang.cg2
  (:require [clojure.java.io :as io]
            [clojure.string :as string])
  (:import
   [org.objectweb.asm ClassVisitor ClassWriter MethodVisitor Opcodes Handle Type Label]
   [java.lang.invoke CallSite LambdaMetafactory MethodHandle MethodHandles$Lookup MethodType]
   [clojure.lang DynamicClassLoader]))

(set! *warn-on-reflection* true)

(comment
  (->> (for [m (.getDeclaredMethods ClassVisitor)]

         (list (symbol (.getName m)) (vec (for [v (.getParameterTypes m)]
                                            (pr-str v)))))
       (sort-by first)
       (run! prn)))

#_(defonce reverse-opcode-map
  (into {}
        (for [f (.getDeclaredFields Opcodes)]
          [(.get f nil)
           (-> @(.getName f)
               string/lower-case
               (string/replace "_" "-")
               keyword)])))

(defonce iface
  (definterface Cg2DebugInfo
    (disasm [])))

(defn pmv
  [^MethodVisitor mv info]
  (let [acc (atom [])]
    (proxy [MethodVisitor clojure.lang.IMeta] [Opcodes/ASM7]
      (meta [] (assoc info :info/bytecode @acc))
      (visitFieldInsn [opcode owner name desc]
        (swap! acc conj [(reverse-opcode-map opcode) owner name desc])
        (.visitFieldInsn mv opcode owner name desc))
      (visitIincInsn [var increment]
        (swap! acc conj [:iinc var increment])
        (.visitIincInsn mv var increment))
      (visitInsn [opcode]
        (swap! acc conj (reverse-opcode-map opcode))
        (.visitInsn mv opcode))
      (visitIntInsn [opcode operand]
        (swap! acc conj [(reverse-opcode-map opcode) operand])
        (.visitIntInsn mv opcode operand))
      (visitInvokeDynamicInsn [name desc bsm bsm-args]
        (swap! acc conj [:invokedynamic name desc bsm bsm-args])
        (.visitInvokeDynamicInsn mv name desc bsm bsm-args))
      (visitJumpInsn [opcode label]
        (swap! acc conj [(reverse-opcode-map opcode) label])
        (.visitJumpInsn mv opcode label))
      (visitLabel [label]
        (swap! acc conj [:label (label)])
        (.visitLabel mv label))
      (visitLdcInsn [constant]
        (swap! acc conj [:ldc constant])
        (.visitLdcInsn mv constant))
      (visitMethodInsn [opcode owner name desc is-interface]
        (swap! acc conj [(reverse-opcode-map opcode) owner name desc is-interface])
        (.visitMethodInsn mv opcode owner name desc is-interface))
      (visitMultiANewArrayInsn [desc dim]
        (swap! acc conj [:amultinewarray desc dim])
        (.visitMultiANewArrayInsn mv desc dim))
      (visitTableSwitchInsn [min max default labels]
        (swap! acc conj [:tableswitch min max default (vec labels)])
        (.visitTableSwitchInsn mv min max default labels))
      (visitTypeInsn [opcode type]
        (swap! acc conj [(reverse-opcode-map opcode) type])
        (.visitTypeInsn mv opcode type))
      (visitVarInsn [opcode var]
        (swap! acc conj [(reverse-opcode-map opcode) var])
        (.visitVarInsn mv opcode var)))))

(defn pcv
  [^ClassVisitor cv]
  (let [info (atom {})]
    (proxy [ClassWriter clojure.lang.IMeta] [Opcodes/ASM7]
      (meta [] @info)
      (visit [version access name signature super-name interfaces]
        (swap! info merge {:info/name name :info/super-name super-name})
        (.visit cv version access name signature super-name interfaces))
      (visitField [access name desc signature value]
        (swap! info update-in [:info/fields name] assoc {:desc desc :value value})
        (.visitField cv access name desc signature value))
      #_(visitInnerClass [name outer-name inner-name access])
      (visitMethod [access name desc signature exceptions]
        (pmv (.visitMethod cv access name desc signature exceptions)
             {:info/name name :info/desc desc}))
      (visitOuterClass [owner name desc]
        (swap! info assoc :outer-class {:owner owner :name name :desc desc})
        (.visitOuterClass cv owner name desc)))))

(defrecord MethodContext
    [
     method-name           ; actual java method name, generated if nil
     method-reference      ; lang-level method name
     access                ; e.g. [:public, :static]
     return-type           ; java return type
     formal-arguments      ; maps identifier to emitter
     formal-arguments-types             ; maps identifier to java type
     captured-arguments                 ; maps identifier to emitter
     captured-arguments-types           ; maps identifier to java type
     local-variables                    ; vector of emitter, generated
     local-variables-types              ; vector of java-type
     method-descriptor      ; actual java method descriptor, generated
     method-visitor  ; only created upon exiting the method definition
     invoker     ; invokedynamic emitter, calls this method, generated
     pending     ; giant continuation, state->state
     ])

(defn new-method-context
  ([] (new-method-context {}))
  ([m] (map->MethodContext
        (into m {:pending identity}))))

(defrecord StaticField [name desc emitter])

(defrecord ClassContext
    [class-ident
     ;; remember name and type of fields so we can generate <init> and <clinit>
     instance-fields                    ; vector of string field names
     instance-fields-types              ; vector of type descriptors
     static-fields                      ; vector of StaticField
     class-visitor                      ; created on context creation
     defined-class                      ; Class instance
     ])

(defrecord CompileContext
    [class-context
     method-context
     
     ;; :top-level (default for created contexts)
     ;; :definition (hack for remembering what we should name our defs)
     ;; :lambda (for defining static methods for use with LambdaMetafactory)
     context-type
     
     value-scope
     type-scope
     
     anon-fn-counter
     ])

(defn new-compile-context
  ([] (new-compile-context {}))
  ([m] (map->CompileContext (merge {:anon-fn-counter 0} m))))

(defrecord CompileState
    [current-context
     context-stack
     class-loader
     fni-cache])

(defn new-compile-state
  []
  (map->CompileState
   {:current-context (new-compile-context {:context-type :top-level})
    :class-loader (DynamicClassLoader.)}))

;; getters

(defn get-class-context
  [{:keys [current-context context-stack] :as state}]
  (or (:class-context current-context)
      (some :class-context context-stack)))

(defn ^ClassVisitor get-class-visitor
  [state]
  (-> state get-class-context :class-visitor))

(defn ^MethodVisitor get-method-visitor
  [state]
  (or (some-> state :current-context :method-context :method-visitor)
      (throw (ex-info "no method visitor" state))))

;; <- functions use promises to poorly imitate the <- in do-notation

(defn <-get-in
  [state vpromise path]
  (deliver vpromise (get-in state path))
  state)

(defn <-method-context
  [{:keys [current-context] :as state} p]
  (deliver p (:method-context current-context))
  state)

(defn <-class-context
  [state p]
  (deliver p (get-class-context state))
  state)

;; push/pop

(defn push-context 
  ([state] (push-context state {}))
  ([{:keys [current-context context-stack] :as state} m]
   (assoc state
          :current-context (new-compile-context m)
          :context-stack (cons current-context context-stack))))

(defn pop-context
  [{:keys [context-stack] :as state}]
  #_(println "POP CONTEXT")
  #_(clojure.pprint/pprint
   (deep-remove-keys-with-nil-values
    (disasm-context
     (:current-context state))))
  (assoc state
         :current-context (first context-stack)
         :context-stack (next context-stack)))

;; lexical scope

(defn dup-context
  [{:keys [current-context context-stack] :as state}]
  (assoc state :context-stack (cons current-context context-stack)))

(defn pop-lexical
  ;; Restores ONLY value/type scopes from the context stack
  [{:keys [current-context context-stack] :as state}]
  (let [[{:keys [value-scope type-scope]} & new-stack] context-stack]
    (assoc state
           :current-context (assoc current-context
                                   :value-scope value-scope
                                   :type-scope type-scope)
           :context-stack new-stack)))

;; class-context

(defn new-class-context
  [{:keys [class-visitor-mapper]} {:keys [name superclass access]}]
  (let [cv (cond-> (ClassWriter. (bit-or ClassWriter/COMPUTE_MAXS ClassWriter/COMPUTE_FRAMES))
             class-visitor-mapper (class-visitor-mapper))]
    (map->ClassContext
     {:class-ident name
      :class-visitor
      (doto ^ClassVisitor cv
        (.visit Opcodes/V1_8 (or (some-> access access->flags) Opcodes/ACC_PUBLIC)
                name nil
                (or superclass "java/lang/Object") nil))})))

(defn in-top-level-class
  [{:keys [current-context] :as state} class-ident]
  (assoc state :current-context
         (assoc current-context :class-context (new-class-context state {:name class-ident}))))

(defn in-class
  [state m]
  (assoc-in state [:current-context :class-context] (new-class-context state m)))

(defn out-class
  [state]
  (let [{:keys [defined-class]} (-> state :current-context :class-context)]
   (-> state
       (cond-> (nil? defined-class) (define-class!))
       (assoc-in [:current-context :class-context] nil))))

(def ^:dynamic *write-class-files* false)
(defn define-class!
  [{:keys [current-context ^DynamicClassLoader class-loader] :as state}]
  (let [{:keys [method-context class-context]} current-context
        {:keys [class-ident ^ClassWriter class-visitor]} (:class-context current-context)]
    (when method-context (throw (ex-info "Do not close class with pending method context!" {})))
    (when-not class-visitor (throw (ex-info "No class visitor!" {})))
    (.visitEnd class-visitor)
    (let [class-bytes (.toByteArray class-visitor)]
      (when *write-class-files*
        (io/copy class-bytes (io/file (str class-ident ".class"))))
      (update-in state [:current-context :class-context] assoc
                 :class-visitor nil
                 :defined-class (.defineClass class-loader class-ident class-bytes nil)))))

;; emitters

(defn and-then
  ;; backwards `comp`
  ([a b] (fn [s] (-> s a b)))
  ([a b c] (fn [s] (-> s a b c)))
  ([a b c d] (fn [s] (-> s a b c d)))
  ([a b c d e] (fn [s] (-> s a b c d e)))
  ([a b c d e f] (fn [s] (-> s a b c d e f)))
  ([a b c d e f g] (fn [s] (-> s a b c d e f g)))
  ([a b c d e f g h] (fn [s] (-> s a b c d e f g h)))
  ([a b c d e f g h i] (fn [s] (-> s a b c d e f g h i))))

(defn context-add-pending
  [{:keys [method-context] :as current-context} emitter]
  (let [{:keys [pending]} method-context]
    (assoc current-context :method-context
           (assoc method-context :pending (and-then pending emitter)))))

(defn add-pending
  [state emitter]
  (update state :current-context context-add-pending emitter))

(defn var-reference-emitter
  [reference]
  ;; note late binding
  (fn [state]
    ((-> state :current-context :value-scope (get reference)) state)))

(defn aload-emitter
  [index]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitVarInsn Opcodes/ALOAD index))
    state))

(defn atom-emitter
  [{:keys [atom value]}]
  (fn [state]
    (case atom
      :integer
      (doto (get-method-visitor state)
        (.visitTypeInsn Opcodes/NEW "java/math/BigInteger")
        (.visitInsn Opcodes/DUP)
        (.visitLdcInsn value)
        (.visitMethodInsn Opcodes/INVOKESPECIAL "java/math/BigInteger" "<init>" "(Ljava/lang/String;)V" false))
      :string
      (doto (get-method-visitor state)
        (.visitLdcInsn value)))
    state))

(defn invokeinterface-emitter
  [owner name desc]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitMethodInsn Opcodes/INVOKEINTERFACE owner name desc true))
    state))

(defn invokevirtual-emitter
  [owner name desc]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitMethodInsn Opcodes/INVOKEVIRTUAL owner name desc false))
    state))

(defn ^String make-method-descriptor
  [return-type arguments]
  (str "(" (apply str arguments) ")" return-type))

(def applyN-descriptor
  (memoize
   (fn [arity]
     (make-method-descriptor "Ljava/lang/Object;" (repeat arity "Ljava/lang/Object;")))))

(defn fni-invoker-emitter
  [return-type arguments]
  (let [fni (functional-interface-class return-type arguments)
        desc (erase-method-desc (make-method-descriptor return-type arguments))]
   (invokeinterface-emitter fni "apply" desc)))

(def lambda-metafactory-handle
  (Handle. Opcodes/H_INVOKESTATIC "java/lang/invoke/LambdaMetafactory" "metafactory"
           "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;"))

(defn add-top-level-binding
  [{:keys [current-context context-stack] :as state} reference emitter]
  (if (= :top-level (:context-type current-context))
    (assoc-in state [:current-context :value-scope reference] emitter)
    (assoc state
           :context-stack (for [{:keys [context-type] :as c} context-stack]
                            (if-not (= :top-level context-type)
                              c
                              (update c :value-scope assoc reference emitter))))))

(defn add-top-level-type
  [{:keys [current-context context-stack] :as state} reference class-name]
  (if (= :top-level (:context-type current-context))
    (assoc-in state [:current-context :type-scope reference] class-name)
    (assoc state
           :context-stack (for [{:keys [context-type] :as c} context-stack]
                            (if-not (= :top-level context-type)
                              c
                              (update c :type-scope assoc reference class-name))))))

;; lazy functional interface generation

(defn munge-type
  [s]
  (case (subs s 0 1)
    "L" "O"
    ;; replace [ with A so the method name is legal
    "[" (str "A" (munge-type (subs s 1)))
    s))

(defn functional-interface-class
  [return-type arg-types]
  (str "fn" (apply str (map munge-type (cons return-type arg-types)))))

(defn ^String erase-method-desc
  [desc]
  ;; turn all reference types into object
  (string/replace desc #"L.*?;" "Ljava/lang/Object;"))

(defn generate-functional-interface!
  [state fni-name method-desc]
  (-> state
      (push-context)
      (in-class {:name fni-name
                 :access [:public :abstract :interface]})
      (push-context)
      (in-method {:method-name "apply"
                  :method-descriptor method-desc
                  :access [:public :abstract]})
      (out-method)
      (pop-context)
      (out-class)
      (pop-context)
      (update :fni-cache assoc fni-name true)))

(defn ensure-functional-interface
  [{:keys [fni-cache] :as state} return-type arg-types]
  (let [fni (functional-interface-class return-type arg-types)]
    (if (contains? fni-cache fni)
      state
      (generate-functional-interface!
       state fni
       (erase-method-desc (make-method-descriptor return-type arg-types))))))

;; invokedynamic

(defn invokedynamic-emitter
  [{:keys [current-context] :as state}]
  (let [{:keys [class-ident]} (get-class-context state)
        {:keys [method-context]} current-context
        {:keys [method-name return-type method-descriptor formal-arguments-types captured-arguments-types]} method-context
        arity (count formal-arguments-types)
        runtime-method-desc (make-method-descriptor return-type formal-arguments-types)]
    (fn [state1]
      (doto (get-method-visitor state1)
        (.visitInvokeDynamicInsn
         "apply"
         (make-method-descriptor (str "L" (functional-interface-class return-type formal-arguments-types) ";")
                                 captured-arguments-types)
         lambda-metafactory-handle
         (object-array [(Type/getType (erase-method-desc runtime-method-desc))
                        (Handle. Opcodes/H_INVOKESTATIC class-ident method-name method-descriptor)
                        (Type/getType runtime-method-desc)])))
      (-> state1
          (ensure-functional-interface return-type formal-arguments-types)))))

;; in-method

(defn in-method
  ([state] (in-method state {}))
  ([state m]
   (assoc-in state [:current-context :method-context] (new-method-context m))))

(defn update-method-context
  [state params]
  (update-in state [:current-context :method-context] (fnil merge (new-method-context)) params))

;; out-method

(defn add-formal-arguments
  ;; add aload-emitters for formal arguments list, starting at `index`
  [scope [formal-arg & more] index]
  (if-not formal-arg
    scope
    (recur (assoc scope formal-arg (aload-emitter index)) more (inc index))))

(defn load-opcode
  [type]
  (case type
    "I" Opcodes/ILOAD
    "J" Opcodes/LLOAD
    "F" Opcodes/FLOAD
    "D" Opcodes/DLOAD
    Opcodes/ALOAD))

(defn store-opcode
  [type]
  (case type
    "I" Opcodes/ISTORE
    "J" Opcodes/LSTORE
    "F" Opcodes/FSTORE
    "D" Opcodes/DSTORE
    Opcodes/ASTORE))

(defn method-context-resolve-local-vars
  [{:keys [local-variables-types] :as method-context} n-method-args]
  (->> (for [t local-variables-types]
         (case t ("J" "D") 2 1))
       (reductions + n-method-args)
       (vec)
       (assoc method-context :local-variables)))

(defn finalize-method-scope
  ;; set up the value-scope to account for formal arguments once we know what their indexes will be
  [{:keys [current-context] :as state}]
  (let [{:keys [method-context value-scope]} current-context
        {:keys [captured-arguments formal-arguments]} method-context
        n-captured-args (count captured-arguments)
        n-method-args (+ n-captured-args (count formal-arguments))]
    (assoc state :current-context
           (assoc current-context
                  :value-scope (add-formal-arguments value-scope formal-arguments n-captured-args)
                  :method-context (method-context-resolve-local-vars method-context n-method-args)))))

(defn get-method-descriptor
  [{:keys [return-type formal-arguments-types captured-arguments-types] :as method-context}]
  (or (:method-descriptor method-context)
      (make-method-descriptor return-type (concat captured-arguments-types formal-arguments-types))))

(defn access->flags
  [access-list]
  (->> (for [a access-list]
         (case a
           :public Opcodes/ACC_PUBLIC
           :static Opcodes/ACC_STATIC
           :final Opcodes/ACC_FINAL
           :interface Opcodes/ACC_INTERFACE
           :abstract Opcodes/ACC_ABSTRACT))
       (reduce bit-or)))

(defn create-method-visitor
  [{:keys [current-context context-stack method-visitor-mapper] :as state}]
  (let [{:keys [class-context method-context]} current-context
        method-desc (get-method-descriptor method-context)
        access (or (some-> method-context :access)
                   [:public :static])
        ^MethodVisitor mv (-> (get-class-visitor state)
                              (.visitMethod (access->flags access) (:method-name method-context) method-desc nil (into-array String []))
                              (cond-> method-visitor-mapper (method-visitor-mapper)))]
    (when-not (some #(= % :abstract) access)
      (.visitCode mv))
    (-> state
        (update-in [:current-context :method-context]
                   assoc
                   :method-descriptor method-desc
                   :method-visitor mv))))

(defn apply-pending-emitters
  [state]
  ((-> state :current-context :method-context :pending) state))

(defn return-from-method
  [state]
  (let [{:keys [access method-visitor return-type]} (-> state :current-context :method-context)
        ^MethodVisitor mv method-visitor]
    (when-not (some #(= % :abstract) access)
      (case (subs return-type 0 1)
        "L" (doto mv
              (.visitTypeInsn Opcodes/CHECKCAST (subs return-type 1 (dec (count return-type))))
              (.visitInsn Opcodes/ARETURN))
        "V" (.visitInsn mv Opcodes/RETURN)
        "I" (.visitInsn mv Opcodes/IRETURN))
      (doto mv
        (.visitMaxs 0 0)
        (.visitEnd))))
  state)

(defn enclosing-method-name
  [cs]
  (or (some-> (first cs) :method-context :method-name)
      (recur (next cs))))

(defn ensure-method-name
  [{:keys [current-context context-stack] :as state}]
  (if (some-> current-context :method-context :method-name)
    state
    (let [{:keys [anon-fn-counter]} current-context]
     (-> state
         (assoc-in [:current-context :anon-fn-counter] (inc anon-fn-counter))
         (assoc-in [:current-context :method-context :method-name]
                   (str (or (enclosing-method-name context-stack) "$root")
                        "$fn"
                        anon-fn-counter))))))

(defn add-invoker
  [state]
  (assoc-in state [:current-context :method-context :invoker] (invokedynamic-emitter state)))

(defn out-method
  [state]
  (-> state
      (finalize-method-scope)
      (ensure-method-name)
      (create-method-visitor)
      (apply-pending-emitters)
      (return-from-method)
      (add-invoker)
      #_(assoc-in [:current-context :method-context] nil)))

;; variable referencing

(defn reference-variable-current-context?
  [{:keys [value-scope] :as current-context} reference]
  (when-let [emitter (get value-scope reference)]
    ;; Push a copy of the bound emitter for the reference onto the pending vector.
    (context-add-pending current-context emitter)))

(defn bind-captured-variable
  [{:keys [method-context] :as current-context} reference type]
  (let [{:keys [captured-arguments captured-arguments-types]} method-context]
    (-> current-context
        ;; we know what the arg index will be so we can aload directly
        (assoc-in [:value-scope reference] (aload-emitter (count captured-arguments)))
        (assoc-in [:type-scope reference] type)
        (assoc :method-context
               (assoc method-context
                      :captured-arguments (conj captured-arguments reference)
                      :captured-arguments-types (conj captured-arguments-types type))))))

(defn capture-from-enclosing-context
  [[current-context & context-stack] reference]
  ;; proceed upwards in the context stack until we find our variable
  (if-let [new-context (reference-variable-current-context? current-context reference)]
    (cons new-context context-stack) 
    (cons current-context (capture-from-enclosing-context context-stack reference))))

(defn find-context-for-variable
  [[{:keys [value-scope] :as context} & more] reference]
  (cond
    (nil? context)                    (throw (ex-info "var not in any outer scope" reference))
    (contains? value-scope reference) context
    :else                             (recur more reference)))

(defn add-typed-binding
  [state reference type emitter]
  (-> state
      (assoc-in [:current-context :value-scope reference] emitter)
      (assoc-in [:current-context :type-scope reference] type)))

(defn reference-variable
  [{:keys [current-context context-stack] :as state} reference]
  ;; try to reference the variable from our immediate context
  (if-let [new-context (reference-variable-current-context? current-context reference)]
    ;; it worked, nothing more to do
    (assoc state :current-context new-context)
    ;; it didn't work, we have to search upwards in the context stack
    (let [{:keys [value-scope type-scope method-context] :as cfv} (find-context-for-variable context-stack reference)
          emitter (get value-scope reference)
          type (get type-scope reference)]
      ;; we found the variable in some enclosing context.
      (if (nil? method-context)
        ;; the variable comes from outside a method.  copy its emitter into our scope and recur.
        (recur (add-typed-binding state reference type emitter) reference)
        ;; the variable is captured from an enclosing function scope.
        (-> state
            (assoc
             ;; ensure the variable will be pushed in the correct context, ahead of invokedynamic
             :context-stack (for [c context-stack]
                              (cond-> c
                                (identical? c cfv) (context-add-pending emitter)))
             ;; remember the argument index in which the generated static method will receive the captured var
             :current-context (bind-captured-variable current-context reference type))
            (recur reference))))))

;; introduce-arguments

(defn introduce-arguments*
  [{:keys [type-scope value-scope] :as context} [arg-name & more-names] [arg-type & more-types]]
  (cond
    (and (nil? arg-name) (nil? arg-type))
    context
    
    (or (nil? arg-name) (nil? arg-type))
    (throw (ex-info "mismatched number of arg names/types" {}))
    
    :else
    (-> context
        (assoc :value-scope (assoc value-scope arg-name (var-reference-emitter arg-name))
               :type-scope (assoc type-scope arg-name arg-type))
        (recur more-names more-types))))

(defn introduce-arguments
  [{:keys [current-context] :as state} arg-names arg-types]
  (assoc state :current-context
         (-> current-context
             (introduce-arguments* arg-names arg-types)
             (update :method-context assoc
                     :formal-arguments arg-names
                     :formal-arguments-types arg-types))))

;; Labels and jumps

(defn visit-label-emitter
  [^Label label]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitLabel label))
    state))

(defn jump-emitter
  [jump-type ^Label label]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitJumpInsn (case jump-type
                        :ifeq Opcodes/IFEQ
                        :ifne Opcodes/IFNE
                        :goto Opcodes/GOTO)
                      label))
    state))

;; Local variables

(defn <-local-var
  [state var-promise java-type]
  (let [var-index (-> state :current-context :method-context :local-variables-types count)]
    (when (realized? var-promise)
      (throw (ex-info "This promise was already realized!" {})))
    (deliver var-promise var-index)
    (update-in state [:current-context :method-context :local-variables-types] (fnil conj []) java-type)))

(defn local-var-load-store-emitter
  [virtual-index type->opcode]
  (fn [{:keys [current-context] :as state}]
    (let [{:keys [method-context]} current-context
          {:keys [local-variables local-variables-types]} method-context
          var-index (nth local-variables virtual-index)
          var-type (nth local-variables-types virtual-index)
          opcode (type->opcode var-type)
          mv (get-method-visitor state)]
      (.visitVarInsn mv opcode var-index)
      (case var-type
        ("J" "D") (.visitVarInsn mv opcode (inc var-index))
        nil)
      state)))

(defn local-var-load-emitter
  [virtual-index]
  (local-var-load-store-emitter virtual-index load-opcode))

(defn local-var-store-emitter
  [virtual-index]
  (local-var-load-store-emitter virtual-index store-opcode))

(defn throw-emitter
  [exception-type message]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitTypeInsn Opcodes/NEW exception-type)
      (.visitInsn Opcodes/DUP)
      (.visitLdcInsn message)
      (.visitMethodInsn Opcodes/INVOKESPECIAL exception-type "<init>" "(Ljava/lang/String;)V" false)
      (.visitInsn Opcodes/ATHROW))
    state))

(defn print-emitter
  [message]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitFieldInsn Opcodes/GETSTATIC "java/lang/System" "out" "Ljava/io/PrintStream;")
      (.visitLdcInsn message) 
      (.visitMethodInsn Opcodes/INVOKEVIRTUAL "java/io/PrintStream" "println" "(Ljava/lang/String;)V" false))
    state))

(defn dup-print-emitter
  [t]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitInsn Opcodes/DUP)
      (.visitFieldInsn Opcodes/GETSTATIC "java/lang/System" "out" "Ljava/io/PrintStream;")
      (.visitInsn Opcodes/SWAP)
      (.visitMethodInsn Opcodes/INVOKEVIRTUAL "java/io/PrintStream" "println" (str "(" t ")V") false))
    state))

(defn print1-emitter
  [t]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitFieldInsn Opcodes/GETSTATIC "java/lang/System" "out" "Ljava/io/PrintStream;")
      (.visitInsn Opcodes/SWAP)
      (.visitMethodInsn Opcodes/INVOKEVIRTUAL "java/io/PrintStream" "println" (str "(" t ")V") false))
    state))

(defn in-inner-class
  [state inner-class-name superclass]
  (let [{:keys [class-ident ^ClassVisitor class-visitor]} (get-class-context state)
        inner-class-ident (str class-ident "$" inner-class-name)
        ncc (new-class-context state {:name inner-class-ident :superclass superclass})]
    ;; information about the outer class, in the inner class, is probably required
    (doto ^ClassVisitor (:class-visitor ncc)
      (.visitOuterClass class-ident nil nil))
    ;; information about inner classes, in the outer class, is purely advisory
    #_(doto class-visitor
        (.visitInnerClass inner-class-ident class-ident inner-class-name Opcodes/ACC_PUBLIC))
    (assoc-in state [:current-context :class-context] ncc)))

(defn add-instance-field
  [{:keys [current-context] :as state} name desc]
  (let [{:keys [class-context]} current-context
        {:keys [class-visitor instance-fields instance-fields-types]} class-context]
    (doto ^ClassVisitor class-visitor
      (.visitField Opcodes/ACC_PUBLIC name desc nil nil))
    (update-in state [:current-context :class-context]
               assoc
               :instance-fields ((fnil conj []) instance-fields name)
               :instance-fields-types ((fnil conj []) instance-fields-types desc))))

(defn field-insn-emitter
  [opcode owner name desc]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitFieldInsn opcode owner name desc))
    state))

(defn constructor-body
  [state class-ident [field & more-fields] [type & more-types]]
  (if (and (nil? field) (nil? type))
    state
    (-> state
        (reference-variable field)
        (add-pending (field-insn-emitter Opcodes/PUTFIELD class-ident field type))
        (recur class-ident more-fields more-types))))

(defn constructor-body-emitter
  [class-ident index [field & more-fields] [type & more-types]]
  (if (and (nil? field) (nil? type))
    identity
    (and-then (aload-emitter 0)
              (aload-emitter index)
              (field-insn-emitter Opcodes/PUTFIELD class-ident field type)
              (constructor-body-emitter class-ident (inc index) more-fields more-types))))

(defn constructor-prolog-emitter
  [superclass ctor-desc]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitVarInsn Opcodes/ALOAD 0)
      (.visitMethodInsn Opcodes/INVOKESPECIAL superclass "<init>" ctor-desc false))
    state))

(defn add-constructor
  [{:keys [current-context] :as state} superclass ctor-desc]
  (let [{:keys [class-ident instance-fields instance-fields-types]} (get-class-context state)]
    (-> state
        (push-context)
        (in-method {:method-name "<init>" :return-type "V" :access [:public]})
        (introduce-arguments instance-fields instance-fields-types)
        (add-pending (and-then
                      (constructor-prolog-emitter superclass ctor-desc)
                      (constructor-body-emitter class-ident 1 instance-fields instance-fields-types)))
        (out-method)
        (pop-context))))

(defn new-object-emitter
  [class-ident]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitTypeInsn Opcodes/NEW class-ident)
      (.visitInsn Opcodes/DUP))
    state))

(defn constructor-call-emitter
  [class-ident ctor-desc]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitMethodInsn Opcodes/INVOKESPECIAL class-ident "<init>" ctor-desc false))
    state))

(defn add-static-field
  [{:keys [current-context] :as state} name desc emitter]
  (let [{:keys [class-context]} current-context
        {:keys [class-visitor static-fields]} class-context]
    (doto ^ClassVisitor class-visitor
      (.visitField (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_STATIC Opcodes/ACC_FINAL) name desc nil nil))
    (update-in state [:current-context :class-context]
               assoc :static-fields (conj (or static-fields []) (->StaticField name desc emitter)))))

(defn add-static-field!
  [state name desc emitter]
  (let [{:keys [class-visitor]} (get-class-context state)]
    (doto ^ClassVisitor class-visitor
      (.visitField (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_STATIC Opcodes/ACC_FINAL) name desc nil nil))
    state))

(defn add-clinit
  [{:keys [current-context] :as state}]
  (let [{:keys [class-ident static-fields]} (get-class-context state)]
    (-> state
        (push-context)
        (in-method {:method-name "<clinit>" :return-type "V" :access [:static]})
        (add-pending (reduce and-then (for [{:keys [name desc emitter]} static-fields]
                                        (and-then emitter
                                                  (field-insn-emitter Opcodes/PUTSTATIC class-ident name desc)))))
        (out-method)
        (pop-context))))



(defn ldc
  [c]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitLdcInsn c))
    state))

(defn disasm-context
  ([context] (disasm-context context merge))
  ([{:keys [class-context method-context] :as context} merge-fn]
   (let [{:keys [class-visitor]} class-context
         {:keys [method-visitor]} method-context]
     (cond-> context
       (meta method-visitor) (update :method-context merge-fn (meta method-visitor))
       (meta class-visitor) (update :class-context merge-fn (meta class-visitor))))))

(defn disasm
  [{:keys [current-context context-stack] :as state}]
  (-> state
      (update :current-context disasm-context (fn [a b] b))
      (assoc :context-stack (map disasm-context context-stack))))

(defn deep-remove-keys-with-nil-values
  [e]
  (->> e
       (clojure.walk/prewalk
        (fn [m]
          (if-not (map? m)
            m
            (into (sorted-map-by (fn [ka kb]
                                   (.compareTo (str ka) (str kb))))
                  (for [[k v] m :when k] [k v])))))))

(let [af (-> (new-compile-state)
               (assoc :class-visitor-mapper pcv)
               (in-top-level-class "Whatever")
               (push-context {:context-type :definition})
               (in-method {:method-name "test" :return-type "Ljava/lang/Object;"})
               (introduce-arguments ["param"] ["Ljava/lang/Object;"])
               (push-context)
               (in-method {:method-name "othermethod" :return-type "Ljava/lang/Object;"})
               (add-typed-binding "x" "Ljava/lang/Object;" (ldc "Hello"))
               (reference-variable "x")
               (out-method)
               (disasm)
    
               #_(pop-context)

               #_(out-method)
               #_(pop-context)
               #_(out-class))]
    (->> af (clojure.walk/prewalk
             #(cond->> % (map? %)
                       (reduce-kv (fn [a k v] (cond-> a v (assoc k v))) {})))))

