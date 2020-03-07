------------------------------------------------------------------------
-- The Agda standard library
--
-- The TC (Type Checking) monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.TCMonad where

open import Reflection.Term

import Agda.Builtin.Reflection as Builtin


-- Type errors
open Builtin public using (ErrorPart; strErr; termErr; nameErr)

-- The monad
open Builtin public
  using ( TC; bindTC; unify; typeError; inferType; checkType
        ; normalise; reduce
        ; catchTC; quoteTC; unquoteTC
        ; getContext; extendContext; inContext; freshName
        ; declareDef; declarePostulate; defineFun; getType; getDefinition
        ; blockOnMeta; commitTC; isMacro; withNormalisation
        ; debugPrint; noConstraints; runSpeculative)
  renaming (returnTC to return)

newMeta : Type → TC Term
newMeta = checkType unknown
