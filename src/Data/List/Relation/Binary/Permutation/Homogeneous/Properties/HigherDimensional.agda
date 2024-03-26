------------------------------------------------------------------------
-- The Agda standard library
--
-- Higher-dimensional properties of the `Homogeneous` definition of permutation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Homogeneous.Properties.HigherDimensional where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.Any as Any
  using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Function.Base using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Symmetric; Transitive; _Respects_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_ ; cong; cong₂)

import Data.List.Relation.Binary.Permutation.Homogeneous.Properties.Core as Core
import Data.List.Relation.Binary.Permutation.Homogeneous.Properties as Properties

private
  variable
    a r : Level
    A : Set a
    x y : A
    xs ys : List A

------------------------------------------------------------------------
-- Two higher-dimensional properties useful in the `Propositional` case,
-- specifically in the equivalence proof between `Bag` equality and `_↭_`
------------------------------------------------------------------------

module _ {_≈_ : Rel A r} (≈-sym : Symmetric _≈_) where

  open Core {R = _≈_} using (_≋_; _↭_; refl; prep; swap; trans; module Symmetry)
  open Symmetry ≈-sym using (≋-sym; ↭-sym)

-- involutive symmetry lifts

  module _ (≈-sym-involutive : ∀ {x y} (p : x ≈ y) → ≈-sym (≈-sym p) ≡ p)
    where

    ↭-sym-involutive : (p : xs ↭ ys) → ↭-sym (↭-sym p) ≡ p
    ↭-sym-involutive (refl xs≋ys) = cong refl (≋-sym-involutive xs≋ys)
      where
      ≋-sym-involutive : (p : xs ≋ ys) → ≋-sym (≋-sym p) ≡ p
      ≋-sym-involutive [] = ≡.refl
      ≋-sym-involutive (x≈y ∷ xs≋ys) rewrite ≈-sym-involutive x≈y
        = cong (_ ∷_) (≋-sym-involutive xs≋ys)
    ↭-sym-involutive (prep eq p) = cong₂ prep (≈-sym-involutive eq) (↭-sym-involutive p)
    ↭-sym-involutive (swap eq₁ eq₂ p) rewrite ≈-sym-involutive eq₁ | ≈-sym-involutive eq₂
      = cong (swap _ _) (↭-sym-involutive p)
    ↭-sym-involutive (trans p q) = cong₂ trans (↭-sym-involutive p) (↭-sym-involutive q)

    module _ (≈-trans : Transitive _≈_) where

      private
        ∈-resp-Pointwise : (Any (x ≈_)) Respects  _≋_
        ∈-resp-Pointwise = Properties.∈-resp-Pointwise ≈-trans

        ∈-resp-↭ : (Any (x ≈_)) Respects _↭_
        ∈-resp-↭ = Properties.∈-resp-↭ ≈-trans

-- invertible symmetry lifts to equality on proofs of membership

      module _ (≈-trans-trans-sym : ∀ {x y z} (p : x ≈ y) (q : y ≈ z) →
                                    ≈-trans (≈-trans p q) (≈-sym q) ≡ p) where

        ∈-resp-Pointwise-sym : (p : xs ≋ ys) {ix : Any (x ≈_) xs} →
                               ∈-resp-Pointwise (≋-sym p) (∈-resp-Pointwise p ix) ≡ ix
        ∈-resp-Pointwise-sym (x≈y ∷ xs≋ys) {here ix}
          = cong here (≈-trans-trans-sym ix x≈y)
        ∈-resp-Pointwise-sym (x≈y ∷ xs≋ys) {there ixs}
          = cong there (∈-resp-Pointwise-sym xs≋ys)

        ∈-resp-↭-sym′   : (p : ys ↭ xs) {iy : Any (x ≈_) ys} {ix : Any (x ≈_) xs} →
                           ix ≡ ∈-resp-↭ p iy → ∈-resp-↭ (↭-sym p) ix ≡ iy
        ∈-resp-↭-sym′ (refl xs≋ys) ≡.refl = ∈-resp-Pointwise-sym xs≋ys
        ∈-resp-↭-sym′ (prep eq₁ p) {here iy} {here ix} eq
          with ≡.refl ← eq = cong here (≈-trans-trans-sym iy eq₁)
        ∈-resp-↭-sym′ (prep eq₁ p) {there iys} {there ixs} eq
          with ≡.refl ← eq = cong there (∈-resp-↭-sym′ p ≡.refl)
        ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {here ix} {here iy} ()
        ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {here ix} {there iys} eq
          with ≡.refl ← eq = cong here (≈-trans-trans-sym ix eq₁)
        ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {there (here ix)} {there (here iy)} ()
        ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {there (here ix)} {here iy} eq
          with ≡.refl ← eq = cong (there ∘ here) (≈-trans-trans-sym ix eq₂)
        ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {there (there ixs)} {there (there iys)} eq
          with ≡.refl ← eq = cong (there ∘ there) (∈-resp-↭-sym′ p ≡.refl)
        ∈-resp-↭-sym′ (trans p₁ p₂) eq = ∈-resp-↭-sym′ p₁ (∈-resp-↭-sym′ p₂ eq)

        ∈-resp-↭-sym : (p : xs ↭ ys) {ix : Any (x ≈_) xs} →
                       ∈-resp-↭ (↭-sym p) (∈-resp-↭ p ix) ≡ ix
        ∈-resp-↭-sym p = ∈-resp-↭-sym′ p ≡.refl

        ∈-resp-↭-sym⁻¹ : (p : xs ↭ ys) {iy : Any (x ≈_) ys} →
                         ∈-resp-↭ p (∈-resp-↭ (↭-sym p) iy) ≡ iy
        ∈-resp-↭-sym⁻¹ p with eq′ ← ∈-resp-↭-sym′ (↭-sym p)
                         rewrite ↭-sym-involutive p = eq′ ≡.refl
