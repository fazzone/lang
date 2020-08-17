(ns lang.cg3-testA
  (:require
   [lang.cg3 :as cg]
   [clojure.string :as string]
   [lang.name-resolution :as nr]
   [lang.type-checker :as tc]
   [lang.parser :as parser]
   [clojure.test :as test :refer [deftest is testing]]))

(defmacro lang
  [& fs]
  `(-> (string/join " " (map pr-str (quote ~fs)))
       (string/replace "," "")
       (parser/parse-string)
       (nr/run)
       (tc/run)
       (cg/compile-module)))

(deftest call-java-method
  (lang
   (defmodule CGTest.java_method)
   (defn +
     [x :$ Integer y :$ Integer]
     (. x (java.math.BigInteger/add y)))
   (def two (+ 1 1))
   (def n137 (+ 1 (+ 30 (+ 6 100)))))
  (is (= 2 (eval '(CGTest.java_method/two))))
  (is (= 137 (eval '(CGTest.java_method/n137)))))

(defn apply-curried
  [f & args]
  (if (empty? args)
    f
    (recur (.apply f (first args)) (next args))))

(deftest captures
  (lang
   (defmodule CGTest.captures)
   (defn capture_spine [a x y]
     (fn [b]
       (fn [c]
         (fn [d]
           (fn [e]
             (fn [f]
               a))))))
   (defn app_spine [a x y b c d e f]
     (capture_spine a x y b c d e f))
   (defn capture_through [a]
     (do "one"
         (fn [b]
           (do "two"
               (fn [c]
                 (do "three"
                     (fn [d] a))))))))
  (is (= :first-arg
         (apply-curried (eval 'CGTest.captures/capture_spine) :first-arg :x :y :b :c :d :e :f)))
  (is (= :first-arg
         (apply-curried (eval 'CGTest.captures/app_spine) :first-arg :x :y :b :c :d :e :f)))
  (is (= :first-arg
         (apply-curried (eval 'CGTest.captures/capture_through) :first-arg :b :c :d))))

(deftest variant-match
  (lang
   (defmodule CGTest.vm)
   (deftype (MyOption T)
       (| [:none]
          [:some T]))
   (defn mk_some [t] [:some t])
   (defn mk_none [i] [:none])
   (defn whatis [o]
     (match o
            [:some t] "a some"
            [:none] "none"))

   (def whatis_some (whatis [:some "hello"]))
   (def whatis_none (whatis [:none]))
   ;; (defn whatis_nest [ooo]
   ;;   (match ooo
   ;;          [:none] "none"
   ;;          [:some oo] (match oo
   ;;                            [:none] "some none"
   ;;                            [:some t] "some some")))
   (defn atoi [a]
     (match a
            "one" 1
            "two" 2
            "three" 3))
   (defn aapp [a]
     (atoi a))

   (defn rec [a]
     (match a
            "one" "we did it"
            "two" (rec "one")
            "three" (rec "two"))))
  
  (is (= "none" (eval 'CGTest.vm/whatis_none)))
  (is (= "a some" (eval 'CGTest.vm/whatis_some)))
  
  (is (= 1 (apply-curried (eval 'CGTest.vm/aapp) "one")))
  (is (= 2 (apply-curried (eval 'CGTest.vm/aapp) "two")))
  (is (= 3 (apply-curried (eval 'CGTest.vm/atoi) "three")))

  (is (= "we did it" (apply-curried (eval 'CGTest.vm/rec) "three")))
  (is (= "we did it" (apply-curried (eval 'CGTest.vm/rec) "two"))))

(deftest variant-record-match-recursion
  (lang
   (defmodule CGTest.vrmr)
   (deftype (List T)
       (| [:nil]
          [:cons {:value T
                  :next (List T)}]))
   (defn list3 [a b c]
     [:cons {:value a :next [:cons {:value b :next [:cons {:value c :next [:nil]}]}]}])
   (defn fold
     [op init list]
     (match list
            [:nil] init
            [:cons {:value n :next tl}] (op (fold op init tl) n)))
   (def the_list (list3 1 2 3))
   (defn +
     [x :$ Integer y :$ Integer]
     (. x (java.math.BigInteger/add y)))
   (def my_sum (fold + 0 the_list)))
  
  (is (= 6 (eval 'CGTest.vrmr/my_sum))))

