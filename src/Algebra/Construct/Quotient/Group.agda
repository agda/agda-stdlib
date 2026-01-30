------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotient groups
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group)
open import Algebra.NormalSubgroup using (NormalSubgroup)

module Algebra.Construct.Quotient.Group  {c ℓ} (G : Group c ℓ) {c′ ℓ′} (N : NormalSubgroup G c′ ℓ′) where

open Group G

import Algebra.Definitions as AlgDefs
open import Algebra.Morphism.Structures using (IsGroupHomomorphism)
open import Algebra.Properties.Monoid monoid
open import Algebra.Properties.Group G using (⁻¹-anti-homo-∙)
open import Algebra.Structures using (IsGroup)
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_)
open import Function.Definitions using (Surjective)
open import Level using (_⊔_)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Reasoning.Setoid setoid

private
  module N = NormalSubgroup N
open NormalSubgroup N using (ι; module ι; conjugate; normal)

infix 0 _by_

data _≋_ (x y : Carrier) : Set (c ⊔ ℓ ⊔ c′) where
  _by_ : ∀ g → ι g ∙ x ≈ y → x ≋ y

≈⇒≋ : _≈_ ⇒ _≋_
≈⇒≋ {x} {y} x≈y = N.ε by trans (∙-cong ι.ε-homo x≈y) (identityˡ y)

≋-refl : Reflexive _≋_
≋-refl = ≈⇒≋ refl

≋-sym : Symmetric _≋_
≋-sym {x} {y} (g by ιg∙x≈y) = g N.⁻¹ by begin
  ι (g N.⁻¹) ∙ y      ≈⟨ ∙-cong (ι.⁻¹-homo g) (sym ιg∙x≈y) ⟩
  ι g ⁻¹ ∙ (ι g ∙ x)  ≈⟨ cancelˡ (inverseˡ (ι g)) x ⟩
  x                   ∎

≋-trans : Transitive _≋_
≋-trans {x} {y} {z} (g by ιg∙x≈y) (h by ιh∙y≈z) = h N.∙ g by begin
  ι (h N.∙ g) ∙ x ≈⟨ ∙-congʳ (ι.∙-homo h g) ⟩
  (ι h ∙ ι g) ∙ x ≈⟨ uv≈w⇒xu∙v≈xw ιg∙x≈y (ι h) ⟩
  ι h ∙ y         ≈⟨ ιh∙y≈z ⟩
  z               ∎

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = record
  { refl = ≋-refl
  ; sym = ≋-sym
  ; trans = ≋-trans
  }

open AlgDefs _≋_

≋-∙-cong : Congruent₂ _∙_
≋-∙-cong {x} {y} {u} {v} (g by ιg∙x≈y) (h by ιh∙u≈v) = g N.∙ h′ by begin
  ι (g N.∙ h′) ∙ (x ∙ u) ≈⟨ ∙-congʳ (ι.∙-homo g h′) ⟩
  (ι g ∙ ι h′) ∙ (x ∙ u) ≈⟨ uv≈wx⇒yu∙vz≈yw∙xz (normal h x) (ι g) u ⟩
  (ι g ∙ x) ∙ (ι h ∙ u)  ≈⟨ ∙-cong ιg∙x≈y ιh∙u≈v ⟩
  y ∙ v                  ∎
  where h′ = conjugate h x

≋-⁻¹-cong : Congruent₁ _⁻¹
≋-⁻¹-cong {x} {y} (g by ιg∙x≈y) = h by begin
  ι h ∙ x ⁻¹        ≈⟨ normal (g N.⁻¹) (x ⁻¹) ⟩
  x ⁻¹ ∙ ι (g N.⁻¹) ≈⟨ ∙-congˡ (ι.⁻¹-homo g) ⟩
  x ⁻¹ ∙ ι g ⁻¹     ≈⟨ ⁻¹-anti-homo-∙ (ι g) x ⟨
  (ι g ∙ x) ⁻¹      ≈⟨ ⁻¹-cong ιg∙x≈y ⟩
  y ⁻¹              ∎
  where h = conjugate (g N.⁻¹) (x ⁻¹)

quotientIsGroup : IsGroup _≋_ _∙_ ε _⁻¹
quotientIsGroup = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ≋-isEquivalence
        ; ∙-cong = ≋-∙-cong
        }
      ; assoc = λ x y z → ≈⇒≋ (assoc x y z)
      }
    ; identity = ≈⇒≋ ∘ identityˡ , ≈⇒≋ ∘ identityʳ
    }
  ; inverse = ≈⇒≋ ∘ inverseˡ , ≈⇒≋ ∘ inverseʳ
  ; ⁻¹-cong = ≋-⁻¹-cong
  }

quotientGroup : Group c (c ⊔ ℓ ⊔ c′)
quotientGroup = record { isGroup = quotientIsGroup }

_/_ : Group c (c ⊔ ℓ ⊔ c′)
_/_ = quotientGroup

π : Group.Carrier G → Group.Carrier quotientGroup
π x = x -- because we do all the work in the relation

π-isHomomorphism : IsGroupHomomorphism rawGroup (Group.rawGroup quotientGroup) π
π-isHomomorphism = record
  { isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = ≈⇒≋
        }
      ; homo = λ _ _ → ≋-refl
      }
    ; ε-homo = ≋-refl
    }
  ; ⁻¹-homo = λ _ → ≋-refl
  }

π-surjective : Surjective _≈_ _≋_ π
π-surjective g = g , ≈⇒≋
