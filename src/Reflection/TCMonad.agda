------------------------------------------------------------------------
-- The Agda standard library
--
-- The TC (Type Checking) monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.TCMonad where

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Data.List.Base using ([])

open import Function

open import Level

open import Reflection.Term

import Agda.Builtin.Reflection as Builtin

private
  variable
    ℓ : Level

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

functor : RawFunctor {ℓ} TC
functor = record
  { _<$>_ = λ f mx → bindTC mx (return ∘ f)
  }

applicative : RawApplicative {ℓ} TC
applicative = record
  { pure = return
  ; _⊛_  = λ mf mx → bindTC mf λ f → bindTC mx (return ∘ f)
  }

applicativeZero : RawApplicativeZero {ℓ} TC
applicativeZero = record
  { applicative = applicative
  ; ∅           = typeError []
  }

alternative : RawAlternative {ℓ} TC
alternative = record
  { applicativeZero = applicativeZero
  ; _∣_             = catchTC
  }

monad : RawMonad {ℓ} TC
monad = record
  { return = return
  ; _>>=_  = bindTC
  }

monadZero : RawMonadZero {ℓ} TC
monadZero = record
  { monad           = monad
  ; applicativeZero = applicativeZero
  }

monadPlus : RawMonadPlus {ℓ} TC
monadPlus = record
  { monad       = monad
  ; alternative = alternative
  }
