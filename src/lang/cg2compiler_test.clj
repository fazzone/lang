(ns lang.cg2compiler-testA
  (:require [clojure.test :refer [is deftest testing]]
            [lang.cg2compiler :refer :all]
            [lang.cg2 :as cg2]
            [lang.name-resolution :as nr]
            [clojure.string :as string]
            [lang.parser :as parser]
            [lang.type-checker :as tc])
  (:import [java.math BigInteger]))

(langpar
 (defmodule P)
 (defn bar [x] x))

(defmacro lang
  [& fs]
  `(-> (string/join " " (map pr-str (quote ~fs)))
       (string/replace "," "")
       (parser/parse-string)
       (nr/run)
       (tc/run)
       (compile-module)
       (cg2/disasm)
       (cg2/deep-remove-keys-with-nil-values)))

(deftest simple
  (lang
   (defmodule Simple)
   (defn id [a] a)
   (defn church_true [a b] a)
   (defn church_false [a b] b))
  (is (= :x (eval '(Simple/id :x))))
  (is (= :a (eval '(Simple/church_true :a :b))))
  (is (= :b (eval '(Simple/church_false :a :b)))))

(deftest simple-capture
  (lang
   (defmodule SimpleCapture)
   (defn capture [a] (fn [b] a)))
  (is (= :captured (eval '(.apply (SimpleCapture/capture :captured) :ignored)))))

(lang
 (defmodule SimpleApplication)
 ;; (defn f [a b] "hello")
 (def f 4))

(comment
  (binding [cg2/*write-class-files* true]
    (lang
     (defmodule SimpleApplication)
     ;; (defn f [a b] "hello")
     (defn g [a] (fn [b] "hello"))))

  (SimpleApplication/g :a))

(deftest simple-application
  (lang
   (defmodule SimpleApplication)
   (defn const [x] "hello")
   (defn const_app [a] (const a))
   (defn two_arg [a b] "two")
   (defn two_arg_apply [a b] (two_arg a b)))
  (is (= "hello" (eval '(SimpleApplication/const_app :ignored))))
  (is (= "two" (eval '(SimpleApplication/two_arg :yeah :ok)))))

(deftest simple-match
  (lang
   (defmodule SimpleMatch)
   (defn num_matcher [a]
     (match a
            2 "two"
            1 "one"))

   (defn string_matcher [a]
     (match a
            "one" 1
            "two" 2))

   (defn wildcard_matcher [a]
     (match a
            _ "whatever"))

   (defn select [which a b c d]
     (match which
            1 a
            2 b
            3 c
            4 d))

   (defn match_scopes [e]
     (match "Outer"
            a (match "Inner"
                     a a)))

   (defn match_scopes_capture [e]
     (match "A"
            a (match "B"
                     a (fn [x] a)))))

  (testing 'num-matcher
    (is (= "one" (eval '(SimpleMatch/num_matcher (BigInteger. "1")))))
    (is (= "two" (eval '(SimpleMatch/num_matcher (BigInteger. "2"))))))

  (testing 'string-matcher
    (is (= 1 (eval '(SimpleMatch/string_matcher "one"))))
    (is (= 2 (eval '(SimpleMatch/string_matcher "two")))))

  (testing 'wildcard-matcher
    (is (= "whatever" (eval '(SimpleMatch/wildcard_matcher nil)))))

  (testing 'select
    (is (= :a (eval '(SimpleMatch/select (BigInteger. "1") :a :b :c :d))))
    (is (= :b (eval '(SimpleMatch/select (BigInteger. "2") :a :b :c :d))))
    (is (= :c (eval '(SimpleMatch/select (BigInteger. "3") :a :b :c :d))))
    (is (= :d (eval '(SimpleMatch/select (BigInteger. "4") :a :b :c :d)))))

  (testing 'match-scopes
    (is (= "Inner" (eval '(SimpleMatch/match_scopes :ignored)))))

  (testing 'match-scopes-capture
    (is (= "B" (-> (eval '(SimpleMatch/match_scopes_capture :ignored))
                   (.apply :ignored))))))

(deftest simple-variant
  (lang
   (defmodule SimpleVariant)
   (deftype (MyOption T)
       (| [:none]
          [:some T]))
   (defn pure [a] [:some a])
   (defn const_none [a] [:none]))
  
  (let [some-class (class (eval '(SimpleVariant/pure :ok)))
        none-class (class (eval '(SimpleVariant/const_none :ok)))]
    (is (= (bases some-class) (bases none-class)))))

(deftest static-fields
  (lang
   (defmodule LStaticFields)
   (def myconst "myconst")
   (def otherconst "otherconst")
   (defn myfunc [x] x))
  
  (is (= "myconst" (eval 'LStaticFields/myconst)))
  (is (= "otherconst" (eval 'LStaticFields/otherconst)))
  (is (= :x (.apply (eval 'LStaticFields/myfunc) :x))))
