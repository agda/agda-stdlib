------------------------------------------------------------------------
-- The Agda standard library
--
-- Comonads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

{-# OPTIONS --without-K --safe #-}

module Category.Comonad where

open import Level
open import Function

record RawComonad {f} (W : Set f → Set f) : Set (suc f) where

  infixl 1 _=>>_ _=>=_
  infixr 1 _<<=_ _=<=_

  field
    extract : ∀ {A} → W A → A
    extend  : ∀ {A B} → (W A → B) → (W A → W B)

  duplicate : ∀ {A} → W A → W (W A)
  duplicate = extend id

  liftW : ∀ {A B} → (A → B) → W A → W B
  liftW f = extend (f ∘′ extract)

  _=>>_ : ∀ {A B} → W A → (W A → B) → W B
  _=>>_ = flip extend

  _=>=_ : ∀ {c A B} {C : Set c} → (W A → B) → (W B → C) → W A → C
  f =>= g = g ∘′ extend f

  _<<=_ : ∀ {A B} → (W A → B) → W A → W B
  _<<=_ = extend

  _=<=_ : ∀ {A B c} {C : Set c} → (W B → C) → (W A → B) → W A → C
  _=<=_ = flip _=>=_
