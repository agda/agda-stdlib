open import Level
open import Data.Product
open import Relation.Unary
open import Algebra
open import Algebra.Module

module Algebra.VectorSpace.Base {r} {ℓr} {m} {ℓm}
  {ring : Ring r ℓr}
  (leftModule : LeftModule ring m ℓm)
  where

open LeftModule leftModule

private variable
  ℓ : Level
  x y : Carrierᴹ

record isVectorSpace (VS : Pred Carrierᴹ ℓ) : Set (m ⊔ r ⊔ ℓ) where
  field
    +-closed     : (x∈VS : x ∈ VS) (y∈VS : y ∈ VS) → x +ᴹ y ∈ VS
    0m-closed    : 0ᴹ ∈ VS
    ·-closedLeft : ∀ r (x∈VS : x ∈ VS) → r *ₗ x ∈ VS

VectorSpace : (ℓ : Level) → Set (m ⊔ r ⊔ suc ℓ)
VectorSpace ℓ = Σ[ VS ∈ Pred Carrierᴹ ℓ ] isVectorSpace VS
