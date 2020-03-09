------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between binary relations
------------------------------------------------------------------------

-- See Data.Nat.Binary.Properties for examples of how this and similar
-- modules can be used to easily translate properties between types.

{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Binary
open import Relation.Binary.Morphism

module Relation.Binary.Morphism.RelMonomorphism
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
  {_∼₁_ : Rel A ℓ₁} {_∼₂_ : Rel B ℓ₂}
  {⟦_⟧ : A → B} (isMonomorphism : IsRelMonomorphism _∼₁_ _∼₂_ ⟦_⟧)
  where

open import Data.Sum.Base as Sum
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable

open IsRelMonomorphism isMonomorphism

------------------------------------------------------------------------
-- Properties

refl : Reflexive _∼₂_ → Reflexive _∼₁_
refl refl = injective refl

sym : Symmetric _∼₂_ → Symmetric _∼₁_
sym sym x∼y = injective (sym (cong x∼y))

trans : Transitive _∼₂_ → Transitive _∼₁_
trans trans x∼y y∼z = injective (trans (cong x∼y) (cong y∼z))

total : Total _∼₂_ → Total _∼₁_
total total x y = Sum.map injective injective (total ⟦ x ⟧ ⟦ y ⟧)

asym : Asymmetric _∼₂_ → Asymmetric _∼₁_
asym asym x∼y y∼x = asym (cong x∼y) (cong y∼x)

dec : Decidable _∼₂_ → Decidable _∼₁_
dec _∼?_ x y = map′ injective cong (⟦ x ⟧ ∼? ⟦ y ⟧)

------------------------------------------------------------------------
-- Structures

isEquivalence : IsEquivalence _∼₂_ → IsEquivalence _∼₁_
isEquivalence isEq = record
  { refl  = refl  E.refl
  ; sym   = sym   E.sym
  ; trans = trans E.trans
  } where module E = IsEquivalence isEq

isDecEquivalence : IsDecEquivalence _∼₂_ → IsDecEquivalence _∼₁_
isDecEquivalence isDecEq = record
  { isEquivalence  = isEquivalence E.isEquivalence
  ; _≟_            = dec E._≟_
  } where module E = IsDecEquivalence isDecEq
