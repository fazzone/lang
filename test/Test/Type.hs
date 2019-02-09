module Test.Type
  ( tree
  )
where

import qualified Data.Map.Strict               as Map
import           Test.Tasty
import           Test.Tasty.HUnit

import           Error                          ( TypeError(..) )
import qualified Error
import qualified Test.Utils                    as Utils
import qualified Type
import qualified Type.Context                  as Ctx
import           Type.Expression               as Type
import           Type.Types

tree, inference :: TestTree
tree = testGroup "Types" [context, inference]

context =
  let marker = Marker . Var . show
  in  testGroup
        "Context"
        [ testCase "split"
        $   Ctx.split (Context (map marker [1, 2, 3, 4, 5, 6])) (marker 4)
        @?= (Context (map marker [1, 2, 3]), Context (map marker [5, 6]))
        , testCase "drop"
        $   Ctx.drop (Context (map marker [1, 2, 3, 4, 5, 6])) (marker 4)
        @?= Context (map marker [1, 2, 3])
        ]

inference
  = let
      test :: TestName -> Text -> Type -> TestTree
      test name source expectedType = testCase name $ case Type.infer $ Utils.parse source of
        Left  err          -> assertFailure (show err)
        Right inferredType -> inferredType @?= expectedType
      testError :: TestName -> Text -> TypeError -> TestTree
      testError name source expectedError =
        testCase name $ Type.infer (Utils.parse source) @?= Left (Error.Type expectedError)
    in
      testGroup
        "Inference"
        [ testGroup
          "Atoms"
          [ test "unit"    "nil"        Type.unit
          , test "integer" "42"         Type.integer
          , test "boolean" "true"       Type.boolean
          , test "string"  "\"foobar\"" Type.string
          ]
        , testGroup
          "Values"
          [ test "record" "{:foo nil :bar 1}"
            $ Record (Map.fromList [(Utils.kw "foo", Type.unit), (Utils.kw "bar", Type.integer)])
          , test "tuple"  "{1 nil true}"
            $ Tuple (Map.fromList [(1, Type.integer), (2, Type.unit), (3, Type.boolean)])
          , test "variant" "[:foo 1]" $ Variant (Map.singleton (Utils.kw "foo") Type.integer)
          ]
        , testGroup
          "Builtins"
          [ test "addition" "(+ 2 3)" Type.integer
          , testError "addition error" "(+ 2 nil)" (TypeMismatch integer unit)
          ]
        , testGroup
          "Higher order functions"
          [ test "identity function" "(fn [x] x)"
            $ let var = Var "delta"
              in  Forall var Type (Function (UniversalVariable var) (UniversalVariable var))
          , test "constant function" "(fn [x] nil)"
            $ let var = Var "delta" in Forall var Type (Function (UniversalVariable var) Type.unit)
          , test "successor function" "(fn [n] (+ 1 n))" (Function Type.integer Type.integer)
          , test "delayed arguent" "(fn [f] (f nil))"
            $ let var = Var "zeta"
              in  Forall
                    var
                    Type
                    (Function (Function Type.unit (UniversalVariable var)) (UniversalVariable var))
          , test "apply function"  "(fn [f x] (fn [x] (f x)))"
            $ let
                mu     = Var "mu"
                lambda = Var "lambda"
                kappa  = Var "kappa"
              in
                Forall
                  mu
                  Type
                  (Forall
                    lambda
                    Type
                    (Function
                      (Function (UniversalVariable mu) (UniversalVariable lambda))
                      (Forall
                        kappa
                        Type
                        (Function (UniversalVariable kappa)
                                  (Function (UniversalVariable mu) (UniversalVariable lambda))
                        )
                      )
                    )
                  )
          , test "compose function" "(fn [g f] (fn [x] (g (f x))))" $ Forall
            (Var "xi")
            Type
            (Forall
              (Var "nu")
              Type
              (Function
                (Function (UniversalVariable (Var "xi")) (UniversalVariable (Var "nu")))
                (Forall
                  (Var "mu")
                  Type
                  (Function
                    (Function (UniversalVariable (Var "mu")) (UniversalVariable (Var "xi")))
                    (Function (UniversalVariable (Var "mu")) (UniversalVariable (Var "nu")))
                  )
                )
              )
            )
          , test "composed functions"
                 "((fn [g f] (fn [x] (g (f x)))) (fn [n] (+ 1 n)) (fn [m] (* 2 m)))"
                 (Function Type.integer Type.integer)
          ]
        , testGroup
          "Control flow"
          [ test "let binding"             "(let [[foo nil]] foo)"               Type.unit
          , test "complicated let binding" "(let [[foo 1] [bar (+ 1 foo)]] bar)" Type.integer
          , test "if stmt"                 "(if true nil nil)"                   Type.unit
          , test "match stmt"              "(match 1 (2 nil) (1 nil))"           Type.unit
          , test "complicated match stmt"  "(match 1 (2 0) (n (+ n 1)))"         Type.integer
          , testError "if stmt test error"         "(if nil 1 2)"        (TypeMismatch boolean unit)
          , testError "if stmt branch error"       "(if true 1 nil)"     (TypeMismatch integer unit)
          , testError "match stmt prototype error" "(match 1 (nil nil))" (TypeMismatch integer unit)
          , testError "match stmt pattern error"
                      "(match 1 (1 nil) (nil nil))"
                      (TypeMismatch integer unit)
          , testError "match stmt body error" "(match 1 (1 nil) (2 1))" (TypeMismatch unit integer)
          ]
        ]
