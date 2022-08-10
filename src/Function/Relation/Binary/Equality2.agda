------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of extensional equivalence.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions

module Function.Relation.Binary.Equality2
  {a b ℓa ℓb : Level}
  (A-setoid : Setoid a ℓa)
  (B-setoid : Setoid b ℓb)
  where

open Setoid A-setoid renaming (Carrier to A; _≈_ to _≈ᴬ_)
open Setoid B-setoid renaming (Carrier to B; _≈_ to _≈ᴮ_)

infix 4 _≗_

_≗_ : (f g : A → B) → Set (a ⊔ ℓb)
f ≗ g = ∀ x → f x ≈ᴮ g x

≗-refl : Reflexive {A = A → B} _≗_
≗-refl x = Setoid.refl B-setoid

≗-sym : Symmetric {A = A → B} _≗_
≗-sym f≗g x = Setoid.sym B-setoid (f≗g x)

≗-trans : Transitive {A = A → B} _≗_
≗-trans f≗g g≗h x = Setoid.trans B-setoid (f≗g x) (g≗h x)
