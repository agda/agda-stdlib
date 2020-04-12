------------------------------------------------------------------------
-- The Agda standard library
--
-- The TC (Type Checking) monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.TypeChecking.Monad where

open import Reflection.Term
import Agda.Builtin.Reflection as Builtin

------------------------------------------------------------------------
-- Type errors

open Builtin public
  using (ErrorPart; strErr; termErr; nameErr)

------------------------------------------------------------------------
-- The monad

open Builtin public
  using
  ( TC; bindTC; unify; typeError; inferType; checkType
  ; normalise; reduce
  ; catchTC; quoteTC; unquoteTC ; quoteωTC
  ; getContext; extendContext; inContext; freshName
  ; declareDef; declarePostulate; defineFun; getType; getDefinition
  ; blockOnMeta; commitTC; isMacro; withNormalisation
  ; debugPrint; noConstraints; runSpeculative)
  renaming (returnTC to return)

------------------------------------------------------------------------
-- Utility functions

newMeta : Type → TC Term
newMeta = checkType unknown
