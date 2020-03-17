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

private
  variable
    a b c f : Level
    A : Set a
    B : Set b
    C : Set c

record RawComonad (W : Set f → Set f) : Set (suc f) where

  infixl 1 _=>>_ _=>=_
  infixr 1 _<<=_ _=<=_

  field
    extract : W A → A
    extend  : (W A → B) → (W A → W B)

  duplicate : W A → W (W A)
  duplicate = extend id

  liftW : (A → B) → W A → W B
  liftW f = extend (f ∘′ extract)

  _=>>_ : W A → (W A → B) → W B
  _=>>_ = flip extend

  _=>=_ : (W A → B) → (W B → C) → W A → C
  f =>= g = g ∘′ extend f

  _<<=_ : (W A → B) → W A → W B
  _<<=_ = extend

  _=<=_ : (W B → C) → (W A → B) → W A → C
  _=<=_ = flip _=>=_
