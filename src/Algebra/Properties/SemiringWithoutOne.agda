------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles

module Algebra.Properties.SemiringWithoutOne
  {g₁ g₂} (M : SemiringWithoutOne g₁ g₂) where

open SemiringWithoutOne M
open import Algebra.Definitions _≈_
open import Algebra.Operations.CommutativeMonoid +-commutativeMonoid
open import Data.Nat.Base using (ℕ; suc; zero)
import Data.Fin.Base as Fin
open import Data.Fin.Base using (Fin; suc)
open import Data.Fin.Combinatorics using (_C_)
open import Relation.Binary.Reasoning.Setoid setoid

*-distribˡ-∑ : ∀ n (f : Fin n → Carrier) x → x * (∑[ i < n ] f i) ≈ ∑[ i < n ] (x * (f i))
*-distribˡ-∑ zero f x = zeroʳ x
*-distribˡ-∑ (suc n) f x = begin
  (x * (f₀ + ∑f))   ≈⟨ distribˡ _ _ _ ⟩
  (x * f₀ + x * ∑f) ≈⟨ +-congˡ (*-distribˡ-∑ n _ _) ⟩
  (x * f₀ + ∑xf)    ∎
  where
    f₀ = f Fin.zero
    ∑f = ∑[ i < n ] f (suc i)
    ∑xf = ∑[ i < n ] (x * f (suc i))

*-distribʳ-∑ : ∀ n (f : Fin n → Carrier) x → (∑[ i < n ] f i) * x ≈ ∑[ i < n ] ((f i) * x)
*-distribʳ-∑ zero f x = zeroˡ x
*-distribʳ-∑ (suc n) f x = begin
  ((f₀ + ∑f) * x)   ≈⟨ distribʳ _ _ _ ⟩
  (f₀ * x + ∑f * x) ≈⟨ +-congˡ (*-distribʳ-∑ n _ _) ⟩
  (f₀ * x + ∑fx)    ∎
  where
    f₀ = f Fin.zero
    ∑f = ∑[ i < n ] f (suc i)
    ∑fx = ∑[ i < n ] (f (suc i) * x)

×-comm : ∀ n x y → x * (n × y) ≈ n × (x * y)
×-comm zero x y = zeroʳ x
×-comm (suc n) x y = begin
  x * (suc n × y)       ≡⟨⟩
  x * (y + n × y)       ≈⟨ distribˡ _ _ _ ⟩
  x * y + x * (n × y)   ≈⟨ +-congˡ (×-comm n _ _) ⟩
  x * y + n × (x * y)   ≡⟨⟩
  suc n × (x * y)       ∎

×-assoc : ∀ n x y → (n × x) * y ≈ n × (x * y)
×-assoc zero x y = zeroˡ y
×-assoc (suc n) x y = begin
  (suc n × x) * y       ≡⟨⟩
  (x + n × x) * y       ≈⟨ distribʳ _ _ _ ⟩
  x * y + (n × x) * y   ≈⟨ +-congˡ (×-assoc n _ _) ⟩
  x * y + n × (x * y)   ≡⟨⟩
  suc n × (x * y)       ∎
