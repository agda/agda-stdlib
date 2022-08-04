------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of extensional equivalence.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions

module Function.Relation.Binary.Equality
  {b ℓ : Level}
  (B-setoid : Setoid b ℓ)
  where

private
  variable
    a : Level
    A : Set a

open Setoid B-setoid renaming (Carrier to B)

infix 4 _≗_

_≗_ : ∀ {a} → {A : Set a} → (f g : A → B) → Set (ℓ ⊔ a)
f ≗ g = ∀ x → f x ≈ g x

≗-refl : ∀ {a} → {A : Set a} → Reflexive {A = A → B} _≗_
≗-refl x = Setoid.refl B-setoid

≗-sym : ∀ {a} → {A : Set a} → Symmetric {A = A → B} _≗_
≗-sym f≗g x = Setoid.sym B-setoid (f≗g x)

≗-trans : ∀ {a} → {A : Set a} → Transitive {A = A → B} _≗_
≗-trans f≗g g≗h x = Setoid.trans B-setoid (f≗g x) (g≗h x)
