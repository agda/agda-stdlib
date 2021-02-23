------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations over Vector
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base
open import Data.Nat.Base
open import Data.Vec.Functional as VF hiding (map)
open import Data.Vec.Functional.Relation.Binary.Pointwise
  using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as PW
open import Level using (Level)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Data.Vec.Functional.Relation.Binary.Equality.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition
------------------------------------------------------------------------

_≋_ : ∀ {n} → Vector A n → Vector A n → Set ℓ
_≋_ = Pointwise _≈_

------------------------------------------------------------------------
-- Relational properties
------------------------------------------------------------------------

≋-refl : ∀ {n} → Reflexive (_≋_ {n = n})
≋-refl {n} = PW.refl {R = _≈_} refl

≋-reflexive : ∀ {n} → _≡_ ⇒ (_≋_ {n = n})
≋-reflexive P.refl = ≋-refl

≋-sym : ∀ {n} → Symmetric (_≋_ {n = n})
≋-sym = PW.sym {R = _≈_} sym

≋-trans : ∀ {n} → Transitive (_≋_ {n = n})
≋-trans = PW.trans {R = _≈_} trans

≋-isEquivalence : ∀ n → IsEquivalence (_≋_ {n = n})
≋-isEquivalence = PW.isEquivalence isEquivalence

≋-setoid : ℕ → Setoid _ _
≋-setoid = PW.setoid S

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

open PW public
  using
  ( map⁺
  ; head⁺; tail⁺
  ; ++⁺; ++⁻ˡ; ++⁻ʳ; ++⁻
  ; replicate⁺
  ; ⊛⁺
  ; zipWith⁺; zip⁺; zip⁻
  )

foldr-cong : ∀ {f g} → (∀ {w x y z} → w ≈ x → y ≈ z → f w y ≈ g x z) →
             ∀ {d e : A} → d ≈ e →
             ∀ {n} {xs ys : Vector A n} → xs ≋ ys →
             foldr f d xs ≈ foldr g e ys
foldr-cong = PW.foldr-cong
