------------------------------------------------------------------------
-- The Agda standard library
--
-- The TC (Type Checking) monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.TCM where

open import Agda.Builtin.Reflection as Builtin using (Meta)

open import Reflection.AST.Term
import Reflection.TCM.Format as Format

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
  ; catchTC; quoteTC; unquoteTC
  ; getContext; extendContext; inContext; freshName
  ; declareDef; declarePostulate; defineFun; getType; getDefinition
  ; commitTC; isMacro; withNormalisation
  ; debugPrint; noConstraints; runSpeculative
  ; Blocker ; blockTC; blockerMeta ; blockerAny ; blockerAll
  )
  renaming (returnTC to pure)

open Format public
  using (typeErrorFmt; debugPrintFmt; errorPartFmt)

------------------------------------------------------------------------
-- Utility functions

newMeta : Type → TC Term
newMeta = checkType unknown

blockOnMeta : ∀ {a} {A : Set a} → Meta → TC A
blockOnMeta m = blockTC (blockerMeta m)
