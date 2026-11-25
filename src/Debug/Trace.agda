------------------------------------------------------------------------
-- The Agda standard library
--
-- Printing Strings During Evaluation
------------------------------------------------------------------------

{-# OPTIONS --without-K --rewriting #-}

-- see README.Debug.Trace for a use-case

module Debug.Trace where

open import Agda.Primitive using (Level)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_)

private
  variable
    a : Level
    A : Set a

-- Postulating the `trace` function and explaining how to compile it

postulate
  trace : String → A → A

{-# FOREIGN GHC import qualified Debug.Trace as Debug #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC trace = const (const (Debug.trace . Text.unpack)) #-}

-- Because expressions involving postulates get stuck during evaluation,
-- we also postulate an equality characterising `trace`'s behaviour. By
-- declaring it as a rewrite rule we internalise that evaluation rule.

postulate
  trace-eq : ∀ (x : A) str → trace str x ≡ x

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE trace-eq #-}

-- Specialised version of `trace` returning the traced message.

traceId : String → String
traceId str = trace str str
