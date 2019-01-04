------------------------------------------------------------------------
-- The Agda standard library
--
-- Printing Strings During Evaluation
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

module Debug.Trace where

open import Agda.Builtin.String
open import Agda.Builtin.Equality

-- Postulating the `trace` function and explaining how to compile it

postulate
  trace : ∀ {a} {A : Set a} → String → A → A

{-# FOREIGN GHC import qualified Debug.Trace as Debug #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC trace = const (const (Debug.trace . Text.unpack)) #-}

-- Because expressions involving postulates get stuck during evaluation,
-- we also postulate an equality characterising `trace`'s behaviour. By
-- declaring it as a rewrite rule we internalise that evaluation rule.

postulate
  trace-eq : ∀ {a} {A : Set a} (a : A) str → trace str a ≡ a

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE trace-eq #-}

-- Specialised version of `trace` returning the traced message.

traceId : String → String
traceId str = trace str str
