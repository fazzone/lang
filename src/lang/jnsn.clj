(ns lang.jnsn
  (:require [clojure.string :as string]
            [clojure.core.match :refer [match]])

  (:import
   [org.objectweb.asm ClassVisitor ClassWriter MethodVisitor Opcodes Handle Type Label]
   [java.lang.invoke CallSite LambdaMetafactory MethodHandle MethodHandles$Lookup MethodType]
   [clojure.lang IDeref DynamicClassLoader]))

;; macro magic

(defn op->sym
  ;; e.g. :ifeq -> 'Opcodes/IFEQ
  [op-keyword]
  (symbol "Opcodes" (string/upper-case (string/replace (name op-keyword) "-" "_"))))

(def asm-functions-opcodes-map
  {'.visitIincInsn {:args [:int :int]
                    :ops [:iinc]}
   '.visitInsn {:args [:opcode]
                :ops [:nop :aconst-null :iconst-m1 :iconst-0 :iconst-1 :iconst-2 :iconst-3 :iconst-4 :iconst-5
                      :lconst-0 :lconst-1 :fconst-0 :fconst-1 :fconst-2 :dconst-0 :dconst-1
                      :iaload :laload :faload :daload :aaload :baload :caload :saload
                      :iastore :lastore :fastore :dastore :aastore :bastore :castore :sastore
                      :pop :pop2 :dup :dup-x1 :dup-x2 :dup2 :dup2-x1 :dup2-x2 :swap
                      :iadd :ladd :fadd :dadd :isub :lsub :fsub :dsub :imul :lmul :fmul :dmul :idiv :ldiv :fdiv :ddiv
                      :irem :lrem :frem :drem :ineg :lneg :fneg :dneg :ishl :lshl :ishr :lshr :iushr :lushr
                      :iand :land :ior :lor :ixor
                      :lxor :i2l :i2f :i2d :l2i :l2f :l2d :f2i :f2l :f2d :d2i :d2l :d2f :i2b :i2c :i2s
                      :lcmp :fcmpl :fcmpg :dcmpl :dcmpg
                      :ireturn :lreturn :freturn :dreturn :areturn :return
                      :arraylength :athrow :monitorenter :monitorexit]}
   '.visitVarInsn {:args [:opcode :int]
                   :ops [:iload :lload :fload :dload :aload :istore :lstore :fstore :dstore :astore :ret]}
   '.visitIntInsn {:args [:opcode :int]
                   :ops [:bipush :sipush :newarray]}
   '.visitTypeInsn {:args [:opcode :id]
                    :ops [:new :anewarray :checkcast :instanceof]}
   '.visitFieldInsn {:args [:opcode :id :id :id]
                     :ops [:getfield :putfield :getstatic :putstatic]}
   '.visitMethodInsn {:args [:opcode :id :id :id :id]
                      :ops [:invokevirtual :invokespecial :invokestatic :invokeinterface]}
   '.visitInvokeDynamicInsn {:args [:id :id :id [:array 'Object]]
                             :ops [:invokedynamic]}
   '.visitJumpInsn {:args [:opcode :id]
                    :ops [:ifeq :ifne :iflt :ifge :ifgt :ifle
                          :if-icmpeq :if-icmpne :if-icmplt :if-icmpge :if-icmpgt :if-icmple :if-acmpeq :if-acmpne
                          :goto :jsr :ifnull :ifnonnull]}
   '.visitLabel {:args [:id]
                 :ops [:label]}
   '.visitLdcInsn {:args [:id]
                   :ops [:ldc]}
   '.visitTableSwitchInsn {:args [:int :int :id [:array 'Label]]
                           :ops [:tableswitch]}
   '.visitLookupSwitchInsn {:args [:id [:array :int] [:array 'Label]]
                            :ops [:lookupswitch]}
   '.visitMultiANewArrayInsn {:args [:id :int]
                              :ops [:multianewarray]}
   '.visitTryCatchBlock {:args [:id :id :id :id]
                         :ops [:try-catch]}})

(defn build-match-branch*
  ;; build a single [pattern action] pair e.g.
  ;;  [[:ifeq arg1]
  ;;   (.visitJumpInsn mv Opcodes/IFEQ arg1)]
  [mv-expr method-sym opcode args]
  (let [match-vars (mapv (fn [i] (symbol (str "arg" i)))
                         (range (count args)))
        method-args (-> (fn [s a]
                          (match a
                                 :id s
                                 :opcode (op->sym opcode)
                                 :int (list 'unchecked-int s)
                                 [:array :int] (list 'int-array s)
                                 [:array t] (list 'into-array t s)))
                        (map match-vars args))]
    [(vec (cons opcode
                (match args
                       [:opcode & xs] (rest match-vars)
                       _ match-vars)))
     (list* method-sym mv-expr method-args)]))

(defn build-insn-match-expr*
  ;; build a giant `match` expression which handles all insns
  [mv-expr insn-expr]
  (list* `match insn-expr
         (list* '[:push-type _] nil
                '[:pop-type]  nil
                (for [[method-sym {:keys [args ops]}] asm-functions-opcodes-map
                      opcode ops
                      part (build-match-branch* mv-expr method-sym opcode args)]
                  part))))

(comment
  (build-insn-match-expr* 'mv 'insn))
(defmacro insn-match
  [mv insn]
  (build-insn-match-expr* mv insn))

;; end macro magic

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

(defn visit-field
  [^ClassVisitor cv {:keys [access name desc default-value]}]
  (.visitField cv (access->flags access) name desc nil default-value))

(defn visit-method
  [^ClassVisitor cv {:keys [access name desc fields emit] :as mc}]
  (when-not name (throw (ex-info "Name required" mc)))
  (when-not desc (throw (ex-info "Desc required" mc)))
  (let [^MethodVisitor mv (.visitMethod cv (access->flags access) name desc nil nil)]
    (.visitCode mv)
    (doseq [iv emit]
      (insn-match mv iv))
    (doto mv
      (.visitMaxs 0 0)
      (.visitEnd))))

(defn create-class
  [{:keys [access name fields methods superclass]}]
  (let [^ClassWriter cw (ClassWriter. (bit-or ClassWriter/COMPUTE_MAXS ClassWriter/COMPUTE_FRAMES))
        flags (or (some-> access not-empty access->flags)
                  Opcodes/ACC_PUBLIC)]
    (.visit cw Opcodes/V1_8 flags name nil (or superclass "java/lang/Object") nil)
    (doseq [f fields]
      (visit-field cw f))
    (doseq [m methods]
      (visit-method cw m))
    (.visitEnd cw)
    (.toByteArray cw)))


