------------------------------------------------------------------------
-- The Agda standard library
--
-- Additional properties for setoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (PartialSetoid; Setoid)

module Relation.Binary.Properties.PartialSetoid
  {a ℓ} (S : PartialSetoid a ℓ) where

open import Data.Product.Base using (_,_; _×_; Σ; proj₁)
open import Function.Base using (id)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; LeftTrans; RightTrans)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Relation.Binary.Structures as Structures
  using (IsPartialEquivalence; IsEquivalence)
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsRelMonomorphism)

private
  open module PER = PartialSetoid S

  variable
    x y z : Carrier


------------------------------------------------------------------------
-- Proofs for partial equivalence relations

trans-reflˡ : LeftTrans _≡_ _≈_
trans-reflˡ ≡.refl p = p

trans-reflʳ : RightTrans _≈_ _≡_
trans-reflʳ p ≡.refl = p

partial-reflˡ : x ≈ y → x ≈ x
partial-reflˡ p = trans p (sym p)

partial-reflʳ : x ≈ y → y ≈ y
partial-reflʳ p = trans (sym p) p

partial-refl : x ≈ y → x ≈ x × y ≈ y
partial-refl p = partial-reflˡ p , partial-reflʳ p

partial-reflexiveˡ : x ≈ y → x ≡ z → x ≈ z
partial-reflexiveˡ p ≡.refl = partial-reflˡ p

partial-reflexiveʳ : x ≈ y → y ≡ z → y ≈ z
partial-reflexiveʳ p ≡.refl = partial-reflʳ p

------------------------------------------------------------------------
-- Setoids from partial setoids

-- Definitions

Carrierₛ : Set _
Carrierₛ = Σ Carrier λ x → x ≈ x

_≈ₛ_ : Rel Carrierₛ _
x≈x@(x , _) ≈ₛ y≈y@(y , _) = x ≈ y

-- Properties

reflₛ : Reflexive _≈ₛ_
reflₛ {x = _ , x≈x} = x≈x

-- Structure

isEquivalenceₛ : Structures.IsEquivalence _≈ₛ_
isEquivalenceₛ = record { refl = λ {x} → reflₛ {x = x} ; sym = sym ; trans = trans }

-- Bundle

setoidₛ : Setoid _ _
setoidₛ = record { isEquivalence = isEquivalenceₛ }

-- Monomorphism

isRelHomomorphism : IsRelHomomorphism _≈ₛ_ _≈_ proj₁
isRelHomomorphism = record { cong = id }

isRelMonomorphism : IsRelMonomorphism _≈ₛ_ _≈_ proj₁
isRelMonomorphism = record { isHomomorphism = isRelHomomorphism ; injective = id }

