------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting equivalences via injective morphisms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Binary
open import Relation.Binary.Morphism

module Relation.Binary.Morphism.RawRelation
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
  {_∼₁_ : Rel A ℓ₁} {_∼₂_ : Rel B ℓ₂}
  {f : A → B} (injective : Injective _∼₁_ _∼₂_ f)
  (isRawRelationMorphism : IsRawRelationMorphism _∼₁_ _∼₂_ f)
  where

open import Data.Sum as Sum
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable

open IsRawRelationMorphism isRawRelationMorphism

------------------------------------------------------------------------
-- Properties

refl : Reflexive _∼₂_ → Reflexive _∼₁_
refl refl = injective refl

sym : Symmetric _∼₂_ → Symmetric _∼₁_
sym sym x∼y = injective (sym (cong x∼y))

trans : Transitive _∼₂_ → Transitive _∼₁_
trans trans x∼y y∼z = injective (trans (cong x∼y) (cong y∼z))

total : Total _∼₂_ → Total _∼₁_
total total x y = Sum.map injective injective (total (f x) (f y))

asym : Asymmetric _∼₂_ → Asymmetric _∼₁_
asym asym x∼y y∼x = asym (cong x∼y) (cong y∼x)

dec : Decidable _∼₂_ → Decidable _∼₁_
dec _∼?_ x y = map′ injective cong (f x ∼? f y)

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
