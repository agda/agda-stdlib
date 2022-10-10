------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definition and functions on the state monad transformer
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Effect.Monad.State.Transformer.Base where

open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤)

open import Effect.Functor

private
  variable
    f s : Level
    A : Set s
    S : Set s
    M : Set s → Set f

------------------------------------------------------------------------
-- State monad operations

record RawMonadState
       (S : Set s)
       (M : Set s → Set f)
       : Set (suc s ⊔ f) where
  field
    get : M S
    put : S → M ⊤
    modify : (S → S) → M ⊤

------------------------------------------------------------------------
-- State monad transformer

record StateT
       (S : Set s)
       (M : Set s → Set f)
       (A : Set s)
       : Set (s ⊔ f) where
  constructor mkStateT
  field runStateT : S → M (S × A)
open StateT public

evalStateT : RawFunctor M → StateT S M A → S → M A
evalStateT M ma s = let open RawFunctor M in proj₂ <$> runStateT ma s

execStateT : RawFunctor M → StateT S M A → S → M S
execStateT M ma s = let open RawFunctor M in proj₁ <$> runStateT ma s
