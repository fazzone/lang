(ns lang.cg2-test
  (:require [clojure.test :refer [is deftest]]
            [lang.cg2 :refer :all])
  (:import [org.objectweb.asm Opcodes]))

(defn ldc
  [c]
  (fn [state]
    (doto (get-method-visitor state)
      (.visitLdcInsn c))
    state))

(defn isub
  [state]
  (doto (get-method-visitor state)
    (.visitInsn Opcodes/ISUB))
  state)

(deftest lexical-scope
  (-> (new-compile-state)
      (in-top-level-class "LexicalScope")
      (push-context {:context-type :definition})
      (in-method {:method-name "test" :return-type "Ljava/lang/Object;"})
      (add-typed-binding "x" "Ljava/lang/String;" (ldc "Outer scope"))
      ;; Create a new lexical scope
      (dup-context)
      ;; Rebind the same reference to our other local var 
      (add-typed-binding "x" "Ljava/lang/String;" (ldc "Inner scope"))
      ;; Push the current value of scope variable `x`
      (reference-variable "x")
      (pop-lexical)
      (out-method)
      (pop-context)
      (out-class))
  (is (= "Inner scope" (eval '(LexicalScope/test)))))

(deftest local-vars
  (let [a (promise)
        b (promise)]
    (-> (new-compile-state)
        (in-top-level-class "LocalVars")
        (push-context {:context-type :definition})
        (in-method {:method-name "test" :return-type "I"})
        (<-local-var a "I")
        (<-local-var b "I")
        (add-pending (and-then
                      ;; a = 9
                      (ldc (int 9))
                      (local-var-store-emitter @a)
                      ;; b = 1
                      (ldc (int 1))
                      (local-var-store-emitter @b)
                      ;; a - b
                      (local-var-load-emitter @a)
                      (local-var-load-emitter @b)
                      isub))
        (out-method)
        (pop-context)
        (out-class))
    (is (= 8 (eval '(LocalVars/test))))))


(deftest static-init
  (-> (new-compile-state)
      (in-top-level-class "StaticInit")
      (add-static-field "sf" "Ljava/lang/String;" (ldc "My static field"))
      (add-clinit)
      (out-class))
  (is (= "My static field" (eval 'StaticInit/sf))))
