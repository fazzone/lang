{-|
This module implements the type __SYNTHESIS__ (@<=@) rules from /figure 14a:: Algorithmic typing, including rules omitted from main paper/ (page 37)
-}
module Type.Synthesis
  ( synthesize
  )
where

import qualified Data.Map.Strict               as Map
import qualified Data.Set                      as Set

import           Error                          ( TypeError(..) )
import qualified Syntax.Term                   as Syntax
import qualified Type.Analysis                 as Analysis
import qualified Type.Context                  as Ctx
import qualified Type.Equation                 as Equation
import           Type.Expression
import           Type.Monad
import           Type.Rules
import           Type.Types
import qualified Type.Wellformedness           as Wellformed


synthesize, synthesize' :: Context -> Term -> Infer ((Type, Principality), Context)

synthesize gamma e = do
  judgement $ TypeSynthesis gamma e
  synthesize' gamma e

-- RULE: Var
synthesize' gamma (Syntax.Symbol _ binding) = do
  (a, p) <- Ctx.lookup binding gamma
  pure ((Ctx.apply gamma a, p), gamma)
-- TODO: Anno
synthesize' gamma (Syntax.Annotation _ e a) =
--   guard $ Wellformed.checkTypeWithPrincipality gamma (a, Principal)
--   delta <- Analysis.check gamma e (Ctx.apply gamma a) Principal
--   pure ((Ctx.apply delta a, Principal), delta)
  error "Synthesis of annotated AST nodes not implemented"
-- RULE: →E (Function elimination)
synthesize' gamma (Syntax.Application _ e s) = do
  (ap, theta) <- synthesize gamma e
  recoverSpine theta s ap
-- RULE
synthesize' gamma e = do
  alpha <- freshExistential
  let gamma'    = Ctx.add gamma $ DeclareExistential alpha Type
      alphaType = ExistentialVariable alpha
  delta <- Analysis.check gamma' e (alphaType, Nonprincipal)
  let typ = maybe alphaType fst $ Map.lookup alpha $ Ctx.existentialSolutions delta
  pure ((typ, Nonprincipal), delta)

spine, spine', recoverSpine, recoverSpine'
  :: Context -> [Term] -> (Type, Principality) -> Infer ((Type, Principality), Context)
spine gamma s ap = do
  judgement $ SpineTyping gamma s ap
  spine' gamma s ap

-- RULE: EmptySpine
spine' gamma [] ap                        = pure (ap, gamma)
-- RULE: ∀Spine
spine' gamma es (Forall alpha kind a, _p) = do
  alphaEx <- freshExistential
  spine (Ctx.add gamma (DeclareExistential alphaEx kind))
        es
        (substitute a (UniversalVariable alpha) (ExistentialVariable alphaEx), Nonprincipal)
-- RULE: ⊃Spine
spine' gamma es (Implies prop a, p) = do
  theta <- Equation.true gamma prop
  spine theta es (Ctx.apply theta a, p)
-- RULE: →Spine
spine' gamma (e : s) (Function a b, p) = do
  theta <- Analysis.check gamma e (a, p)
  spine theta s (Ctx.apply theta b, p)
-- RULE: α̂Spine
spine' gamma es (ExistentialVariable alpha, p) | (alpha, Type) `Set.member` Ctx.existentials gamma =
  do
    alpha1 <- freshExistential
    alpha2 <- freshExistential
    let function    = Function (ExistentialVariable alpha1) (ExistentialVariable alpha2)
        (pre, post) = Ctx.split gamma (DeclareExistential alpha Type)
        gamma'      = Ctx.splice
          pre
          [ DeclareExistential alpha1 Type
          , DeclareExistential alpha2 Type
          , SolvedExistential alpha Type function
          ]
          post
    spine gamma' es (function, p)
spine' _ _ _ = error "No spine typing rule defined"

recoverSpine gamma s ap = do
  judgement $ PrincipalityRecoveringSpineTyping gamma s ap
  recoverSpine' gamma s ap

-- RULE: SpineRecover
recoverSpine' gamma s ap@(_, Principal) = do
  (cp, delta) <- spine gamma s ap
  case cp of
    (c, Principal) -> pure (cp, delta)
    (c, Nonprincipal) ->
      let fvs = Ctx.freeExistentialVariables gamma c
      in  if Set.null fvs then pure (cp, delta) else throwError $ PrincipalityRecoveryFailure fvs
-- RULE: SpinePass
recoverSpine' gamma s ap@(_, p) = do
  ((c, q), delta) <- spine gamma s ap
  unless
      (  p
      == Nonprincipal
      || q
      == Principal
      || (not . Set.null $ Ctx.freeExistentialVariables delta c)
      )
    $ throwError (RuleError "SpinePass")
  pure ((c, q), delta)