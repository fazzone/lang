{-# LANGUAGE DataKinds #-}

module Type.Context
  ( universals
  , existentials
  , existentialSolutions
  , freeExistentialVariables
  , freeUniversalVariables
  , initialize
  , add
  , adds
  , join
  , drop
  , lookup
  , definitions
  , apply
  , substitute
  , split
  , before
  , inject
  , splice
  , isUnsolved
  )
where

import qualified Data.Map.Strict               as Map
import           Data.Sequence                  ( Seq(..)
                                                , (|>)
                                                )
import qualified Data.Sequence                 as Seq
import qualified Data.Set                      as Set

import           Error                          ( TypeError(..) )
import qualified Syntax.Definition             as Def
import qualified Syntax.Reference              as Ref
import           Type.Expression                ( fromSyntax )
import qualified Type.Expression               as Type
import           Type.Monad
import           Type.Types

empty :: Context
empty = Context mempty

initialize :: Map Ref.Type Type -> Map Ref.Value Type -> Context
initialize initialTypedefs initialBindings =
  let
    typedefs =
      concatMap
          (\(n, t) ->
            (map (\exvar -> DeclareExistential exvar Type) $ Set.toList $ existentialVariables t)
              <> [Definition n Type t]
          )
        $ Map.toList initialTypedefs
    bindings = map (\(n, t) -> Binding n t Principal) $ Map.toList initialBindings
  in
    Context $ Seq.fromList $ typedefs <> bindings

add :: Context -> Fact -> Context
add (Context ctx) elt = Context $ ctx |> elt

adds :: Context -> [Fact] -> Context
adds (Context ctx) els = Context $ ctx <> Seq.fromList els

join :: Context -> Context -> Context
join (Context ctx1) (Context ctx2) = Context $ ctx1 <> ctx2

split :: Context -> Fact -> (Context, Context)
split (Context ctx) fact = case Seq.breakr (fact ==) ctx of
  (post, pre :|> _) -> (Context pre, Context post)
  _                 -> error "Failed to split context"

drop :: Context -> Fact -> Context
drop ctx elt = let (pre, _) = split ctx elt in pre

inject :: Context -> Fact -> Context -> Context
inject pre elt post = splice pre [elt] post

splice :: (Foldable t) => Context -> t Fact -> Context -> Context
splice (Context pre) els (Context post) = Context $ mconcat [pre, Seq.fromList $ toList els, post]

before :: Context -> Variable 'Existential -> Variable 'Existential -> Bool
before (Context ctx) predecessor succecessor =
  let matchExvar exvar = \case
        DeclareExistential exvar' _  -> exvar == exvar'
        SolvedExistential exvar' _ _ -> exvar == exvar'
        _                            -> False
      predIndex = Seq.findIndexL (matchExvar predecessor) ctx
      succIndex = Seq.findIndexL (matchExvar succecessor) ctx
  in  predIndex < succIndex

existentials :: Context -> Set (Variable 'Existential, Kind)
existentials gamma =
  let declarations = [ (tv, kind) | DeclareExistential tv kind <- toList $ unContext gamma ]
      solutions    = [ (tv, kind) | SolvedExistential tv kind _ <- toList $ unContext gamma ]
  in  (Set.union `on` Set.fromList) declarations solutions

universals :: Context -> Set (Variable 'Universal, Kind)
universals gamma =
  let declarations = [ (tv, kind) | DeclareUniversal tv kind <- toList $ unContext gamma ]
      solutions    = [ (tv, undefined) | SolvedUniversal tv _ <- toList $ unContext gamma ] -- FIXME
  in  (Set.union `on` Set.fromList) declarations solutions

existentialSolutions :: Context -> Map (Variable 'Existential) (Type, Kind)
existentialSolutions gamma =
  Map.fromList [ (tv, (typ, kind)) | SolvedExistential tv kind typ <- toList $ unContext gamma ]

isUnsolved :: Variable 'Existential -> Context -> Bool
isUnsolved exvar gamma = Map.notMember exvar $ existentialSolutions gamma

universalSolutions :: Context -> Map (Variable 'Universal) Type
universalSolutions gamma =
  Map.fromList [ (tv, typ) | SolvedUniversal tv typ <- toList $ unContext gamma ]

bindings :: Context -> Map Ref.Value (Type, Principality)
bindings gamma = Map.fromList
  [ (binding, (typ, principality)) | Binding binding typ principality <- toList $ unContext gamma ]

lookup :: Ref.Value -> Context -> Infer (Type, Principality)
lookup binding gamma = do
  case Map.lookup binding $ bindings gamma of
    Nothing     -> typeerror $ UnknownBinding binding
    Just result -> pure result

definitions :: Context -> Map Ref.Type (Type, Kind)
definitions gamma =
  Map.fromList [ (name, (kind, typ)) | Definition name typ kind <- toList $ unContext gamma ]

apply :: Context -> Type -> Type
apply ctx typ = case typ of
  Primitive _           -> typ
  Function type1  type2 -> Function (apply ctx type1) (apply ctx type2)
  Variant  rowvar types -> Variant rowvar (map (apply ctx) types)
  Tuple types           -> Tuple (map (apply ctx) types)
  Record rowvar types   -> Record rowvar (map (apply ctx) types)
  UniversalVariable var -> case Map.lookup var $ universalSolutions ctx of
    Just tau -> apply ctx tau
    Nothing  -> typ
  ExistentialVariable var -> case Map.lookup var $ existentialSolutions ctx of
    Just (tau, _) -> apply ctx tau
    Nothing       -> typ
  Named _             -> typ
  Forall var kind t   -> Forall var kind (apply ctx t)
  Exists var kind sub -> Exists var kind (apply ctx sub)
  Implies prop sub    -> Implies prop (apply ctx sub)
  With    sub  prop   -> With (apply ctx sub) prop
  Zero                -> Zero
  Succ sub            -> Succ (apply ctx sub)
  Vector type1 type2  -> Vector (apply ctx type1) (apply ctx type2)
  Fix    var   sub    -> Fix var sub

substitute :: Context -> Type -> Type -> Context
substitute (Context ctx) match replacement = Context $ map replace ctx
 where
  replace :: Fact -> Fact
  replace = \case
    Binding name typ principality ->
      Binding name (Type.substitute typ match replacement) principality
    SolvedUniversal var typ -> SolvedUniversal var (Type.substitute typ match replacement)
    SolvedExistential var kind typ ->
      SolvedExistential var kind (Type.substitute typ match replacement)
    element -> element

incorporate :: Context -> Context -> Context
incorporate (Context Empty) (Context Empty) = Context Empty
incorporate (Context (omegas :|> l)) (Context (gammas :|> r)) =
  let omega = Context omegas
      gamma = Context gammas
      rest  = incorporate omega gamma
  in  case (l, r) of
        (Binding x a p, Binding x' aGamma p')
          | x == x' && p == p' && apply omega a == apply omega aGamma -> add
            rest
            (Binding x (apply omega a) p)
        (declaration@(DeclareUniversal alpha k), DeclareUniversal alpha' k')
          | alpha == alpha' && k == k' -> add rest declaration
        (Marker u, Marker u') | u == u' -> rest
        (SolvedUniversal alpha t, SolvedUniversal alpha' t')
          | alpha == alpha' && apply omega t == apply omega t' -> substitute
            (incorporate omega gamma)
            (UniversalVariable alpha)
            t
        (SolvedExistential alpha k _, _) -> case r of
          SolvedExistential alpha' k' _ | alpha == alpha' && k == k' -> rest
          DeclareExistential alpha' k' | alpha == alpha' && k == k' -> rest
          h -> incorporate omega (add gamma h)
        _ -> error "Impossible context-to-context application"
incorporate (Context Empty) (Context _    ) = error "Contexts need to be of identical length"
incorporate (Context _    ) (Context Empty) = error "Contexts need to be of identical length"

existentialVariables :: Type -> Set (Variable 'Existential)
existentialVariables typ = case typ of
  Primitive _                 -> Set.empty
  Function type1        type2 -> existentialVariables type1 <> existentialVariables type2
  Variant  (Open alpha) types -> Set.delete alpha $ foldMap existentialVariables types
  Variant  _            types -> foldMap existentialVariables types
  Tuple types                 -> foldMap existentialVariables types
  Record (Open alpha) types   -> Set.delete alpha $ foldMap existentialVariables types
  Record _            types   -> foldMap existentialVariables types
  UniversalVariable   _       -> Set.empty
  ExistentialVariable ev      -> Set.singleton ev
  Named               _       -> Set.empty
  Exists _ _ body             -> existentialVariables body
  Forall _ _ body             -> existentialVariables body
  Fix     exvar body          -> existentialVariables body
  Implies _     body          -> existentialVariables body
  With    body  _             -> existentialVariables body

freeExistentialVariables :: Context -> Type -> Set (Variable 'Existential)
freeExistentialVariables ctx typ = case typ of
  Primitive _                 -> Set.empty
  Function type1 type2 -> freeExistentialVariables ctx type1 <> freeExistentialVariables ctx type2
  Variant  (Open alpha) types -> Set.delete alpha $ foldMap (freeExistentialVariables ctx) types
  Variant  _            types -> foldMap (freeExistentialVariables ctx) types
  Tuple types                 -> foldMap (freeExistentialVariables ctx) types
  Record (Open alpha) types   -> Set.delete alpha $ foldMap (freeExistentialVariables ctx) types
  Record _            types   -> foldMap (freeExistentialVariables ctx) types
  UniversalVariable _         -> Set.empty
  ExistentialVariable ev ->
    if Map.notMember ev (existentialSolutions ctx) then Set.singleton ev else Set.empty
  Named _            -> Set.empty
  Exists _ _ body    -> freeExistentialVariables ctx body
  Forall _ _ body    -> freeExistentialVariables ctx body
  Fix     exvar body -> Set.delete exvar $ freeExistentialVariables ctx body
  Implies _     body -> freeExistentialVariables ctx body
  With    body  _    -> freeExistentialVariables ctx body

freeUniversalVariables :: Context -> Type -> Set (Variable 'Universal)
freeUniversalVariables ctx typ = case typ of
  UniversalVariable uv ->
    if Map.notMember uv (universalSolutions ctx) then Set.singleton uv else Set.empty
  Function type1 type2 -> freeUniversalVariables ctx type1 <> freeUniversalVariables ctx type2
  Variant  _     types -> foldMap (freeUniversalVariables ctx) types
  Tuple types          -> foldMap (freeUniversalVariables ctx) types
  Record _ types       -> foldMap (freeUniversalVariables ctx) types
  Exists _ _ body      -> freeUniversalVariables ctx body
  Forall _ _ body      -> freeUniversalVariables ctx body
