module Type.Types
  ( Type(..)
  , Fact(..)
  , Context(..)
  , Kind(..)
  , Variable(..)
  , VariableId(..)
  , Mode(..)
  , Row(..)
  , compareExtent
  , Principality(..)
  , Proposition(..)
  , Polarity(..)
  , Term
  , Atom
  , Branch
  , Pattern
  )
where

import qualified Data.Map.Strict               as Map
import           Data.Text.Prettyprint.Doc
import qualified Universum.Unsafe              as Unsafe

import qualified Classes
import qualified Syntax.Atom                   as Syntax
import qualified Syntax.Common                 as Syntax
import qualified Syntax.Pattern                as Syntax
import qualified Syntax.Reference              as Ref
import qualified Syntax.Term                   as Syntax


type Term = Syntax.Term Classes.Empty
type Atom = Syntax.Atom
type Pattern = Syntax.Pattern Classes.Empty
type Branch = Syntax.Branch Classes.Empty

newtype Context = Context
  { unContext :: Seq Fact
  } deriving (Show, Eq, Ord)

data Fact
  = DeclareUniversal (Variable 'Universal)
                     Kind
  | DeclareExistential (Variable 'Existential)
                       Kind
  | Binding Ref.Value
            Type
            Principality
  | SolvedUniversal (Variable 'Universal)
                    Type
  | SolvedExistential (Variable 'Existential)
                      Kind
                      Type
  | Definition Ref.Type Kind Type
  | Marker (Variable 'Mark)
  deriving (Show, Ord, Generic)

instance Eq Fact where
  (==) (DeclareUniversal name kind) = \case
    DeclareUniversal name' kind' -> name == name' && kind == kind'
    SolvedUniversal name' _ -> name == name'
    _ -> False
  (==) (DeclareExistential name kind) = \case
    DeclareExistential name' kind' -> name == name' && kind == kind'
    SolvedExistential name' kind' _ -> name == name' && kind == kind'
    _ -> False
  (==) (SolvedUniversal name _) = \case
    SolvedUniversal name' _ -> name == name'
    DeclareUniversal name' _ -> name == name'
    _ -> False
  (==) (SolvedExistential name kind _) = \case
    DeclareExistential name' kind' -> name == name' && kind == kind'
    SolvedExistential name' kind' _ -> name == name' && kind == kind'
    _ -> False
  (==) (Binding name _ _) = \case
    Binding name' _ _ -> name == name'
    _ -> False
  (==) (Definition name kind _) = \case
    Definition name' kind' _ -> name == name' && kind == kind'
    _ -> False
  (==) (Marker name) = \case
    Marker name' -> name == name'
    _ -> False

data Principality
  = Principal
  | Nonprincipal
  deriving (Show, Eq, Ord, Generic)

newtype Variable (mode :: Mode) =
  Variable VariableId
  deriving (Show, Eq, Ord, Generic)

data Mode
  = Existential
  | Universal
  | Mark

newtype VariableId =
  VariableId Int
  deriving (Show, Eq, Ord, Enum, Generic)

data Kind
  = Type
  | Natural
  deriving (Show, Eq, Ord, Generic)

data Type
  = Primitive Text
  | Function Type Type
  | Variant Row (Map Ref.Keyword Type)
  | Tuple (Map Int Type)
  | Record Row (Map Ref.Keyword Type)
  | UniversalVariable (Variable 'Universal)
  | ExistentialVariable (Variable 'Existential)
  | Forall (Variable 'Universal)
           Kind
           Type
  | Exists (Variable 'Universal)
           Kind
           Type
  | Implies Proposition
            Type
  | With Type
         Proposition
  | Zero
  | Succ Type
  | Vector Type
           Type
  | Fix (Variable 'Existential)
        Type
  | Abstraction [(Variable 'Universal, Kind)] Type
  | Application Type [Type]
  deriving (Show, Eq, Ord, Generic)

instance Pretty Type where
  pretty = evaluatingState initial . render
    where initial = (greekAlphabet, mempty)
          display :: (MonadState ([Text], Map VariableId Text) m) => Variable q -> m (Doc ann)
          display (Variable varid) = do
            (alphabet, knownVariables) <- get
            case Map.lookup varid knownVariables of
              Just name -> pure $ pretty name
              Nothing -> do
                let varName = Unsafe.head alphabet
                    knownVariables' = Map.insert varid varName knownVariables
                put (Unsafe.tail alphabet, knownVariables')
                pure $ pretty varName
          render :: (MonadState ([Text], Map VariableId Text) m) => Type -> m (Doc ann)
          render (Primitive prim) = pure $ pretty prim
          render (Function a b) = do
            let args (Function inp out) = inp : args out
                args t                  = [t]
            arguments <- traverse render (a : args b)
            let body = hsep $ "->" : arguments
            pure $ parens body
          render (Variant rowvar cases) = do
            cases' <- for (toPairs cases) $ \(tag, typ) -> do
              typ' <- render typ
              pure $ brackets $ pretty tag <+> typ'
            let cases'' = case rowvar of
                           Closed -> cases'
                           Open _ -> cases' <> ["..."]
            pure $ parens $ hsep $ "|" : cases''
          render (Tuple fields) = do
            fields' <- traverse render $ elems fields
            pure $ braces $ hsep fields'
          render (Record rowvar fields) = do
            fields' <- for (toPairs fields) $ \(name, typ) -> do
              typ' <- render typ
              pure $ pretty name <+> typ'
            let fields'' = case rowvar of
                             Closed -> fields'
                             Open _ -> fields' <> ["..."]
            pure $ braces $ hsep fields''
          render (UniversalVariable var) = display var
          render (ExistentialVariable var) = display var
          render (Forall var _ typ) = do
            var' <- display var
            typ' <- render typ
            pure $ parens $ hsep ["∀", var' <> ".", typ']
          render (Fix var typ) = do
            var' <- display var
            typ' <- render typ
            pure $ parens $ hsep ["μ", var' <> ".", typ']
          render (Abstraction params body) = do
            params' <- fmap (brackets . hsep) $ traverse (display . fst) params
            pure $ parens $ hsep ["Λ" , params']
          render (Application operator args) = do
            operator' <- render operator
            args' <- traverse render args
            pure $ parens $ hsep $ operator' : args'
          render t = pure $ show t

data Row = Closed | Open (Variable 'Existential) deriving (Generic, Show, Eq, Ord)


compareExtent :: Syntax.Extent -> Row -> Bool
compareExtent Syntax.Closed Closed   = True
compareExtent Syntax.Open   (Open _) = True
compareExtent _             _        = False

data Proposition =
  Equals Type
         Type
  deriving (Show, Eq, Ord, Generic)

data Polarity
  = Positive
  | Negative
  | Neutral
  deriving (Show, Eq)

greekAlphabet :: IsString s => [s]
greekAlphabet =
  [ "α"
  , "β"
  , "γ"
  , "δ"
  , "ε"
  , "ζ"
  , "η"
  , "θ"
  , "ι"
  , "κ"
  , "λ"
  , "μ"
  , "ν"
  , "ξ"
  , "ο"
  , "π"
  , "ρ"
  , "σ"
  , "τ"
  , "υ"
  , "ϕ"
  , "χ"
  , "ψ"
  , "ω"
  ]
