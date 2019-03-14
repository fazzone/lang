module Parser.Definition
  ( definition
  )
where

import           Parser.Common
import           Parser.Reference               ( moduleName
                                                , typeName
                                                , variableName
                                                )
import qualified Parser.Term                   as Term
import qualified Parser.Type                   as Type
import           Syntax.Definition              ( Definition(..) )
import           Syntax.Reference               ( Value(..) )
import           Syntax.Term                    ( Term(..) )


definition :: Parser (Definition Parsing)
definition = injectContext
  $ cases [moduleDefinition, typeDefinition, constantDefinition, functionDefinition]
 where
  moduleDefinition = sexp $ do
    reserved "defmodule"
    modulename <- moduleName
    forms      <- many definition
    pure $ \ctx -> Module ctx modulename forms
  typeDefinition = sexp $ do
    reserved "deftype"
    typename  <- typeName
    params    <- many typeName
    structure <- Type.expr
    pure $ \ctx -> Type ctx typename params structure
  constantDefinition = sexp $ do
    reserved "def"
    constname <- variableName
    value     <- Term.expr
    pure $ \ctx -> Constant ctx constname value
  functionDefinition = sexp $ do
    reserved "defn"
    funcname <- variableName
    args     <- vector $ many variableName
    body     <- many1 Term.expr
    pure $ \ctx ->
      let args' = case args of
            [] -> [Local "run"]
            _  -> args
          body' = case body of
            [form] -> form
            forms  -> Sequence ctx forms
      in  Constant ctx funcname $ Fix ctx funcname $ foldr' (Lambda ctx) body' args'