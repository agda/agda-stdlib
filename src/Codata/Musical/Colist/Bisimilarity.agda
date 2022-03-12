------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise equality of colists
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Codata.Musical.Colist.Bisimilarity where

open import Codata.Musical.Colist.Base
open import Codata.Musical.Notation
open import Level using (Level)
open import Relation.Binary

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- xs ≈ ys means that xs and ys are equal.

infix 4 _≈_

data _≈_ {A : Set a} : Rel (Colist A) a where
  []  :                                       []     ≈ []
  _∷_ : ∀ x {xs ys} (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ x ∷ ys

-- The equality relation forms a setoid.

setoid : Set a → Setoid _ _
setoid A = record
  { Carrier       = Colist A
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {[]}     = []
  refl {x ∷ xs} = x ∷ ♯ refl

  sym : Symmetric _≈_
  sym []        = []
  sym (x ∷ xs≈) = x ∷ ♯ sym (♭ xs≈)

  trans : Transitive _≈_
  trans []        []         = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

module ≈-Reasoning where
  import Relation.Binary.Reasoning.Setoid as EqR
  private
    open module R {a} {A : Set a} = EqR (setoid A) public

-- map preserves equality.

map-cong : (f : A → B) → _≈_ =[ map f ]⇒ _≈_
map-cong f []        = []
map-cong f (x ∷ xs≈) = f x ∷ ♯ map-cong f (♭ xs≈)
