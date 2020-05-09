(ns lang.core
  (:gen-class)
  (:require [lang.compiler :as compiler]
            [lang.module :as module]))

(defn -main
  [& args]
  (run!
    (case (first args)
      "signature"
      #(-> %
         (compiler/run #{:parser :dependency-analyzer :type-checker})
         (module/signature)
         (println))

      "compile"
      compiler/run)
    (next args)))
