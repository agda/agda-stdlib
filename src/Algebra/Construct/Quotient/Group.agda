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
open import Algebra.Morphism.Structures
open import Algebra.Properties.Group G
open import Algebra.Structures using (IsGroup)
open import Data.Product.Base
open import Level using (_⊔_)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Reasoning.Setoid setoid

open NormalSubgroup N

infix 0 _by_

data _≋_ (x y : Carrier) : Set (c ⊔ ℓ ⊔ c′) where
  _by_ : ∀ g → ι g ∙ x ≈ y → x ≋ y

≋-refl : Reflexive _≋_
≋-refl {x} = N.ε by trans (∙-congʳ ι.ε-homo) (identityˡ x)

≋-sym : Symmetric _≋_
≋-sym {x} {y} (g by ιg∙x≈y) = g N.⁻¹ by begin
  ι (g N.⁻¹) ∙ y      ≈⟨ ∙-cong (ι.⁻¹-homo g) (sym ιg∙x≈y) ⟩
  ι g ⁻¹ ∙ (ι g ∙ x)  ≈⟨ assoc (ι g ⁻¹) (ι g) x ⟨
  (ι g ⁻¹  ∙ ι g) ∙ x ≈⟨ ∙-congʳ (inverseˡ (ι g)) ⟩
  ε ∙ x               ≈⟨ identityˡ x ⟩
  x                   ∎

≋-trans : Transitive _≋_
≋-trans {x} {y} {z} (g by ιg∙x) (h by ιh∙y) = h N.∙ g by begin
  ι (h N.∙ g) ∙ x ≈⟨ ∙-congʳ (ι.∙-homo h g) ⟩
  (ι h ∙ ι g) ∙ x ≈⟨ assoc (ι h) (ι g) x ⟩
  ι h ∙ (ι g ∙ x) ≈⟨ ∙-congˡ ιg∙x ⟩
  ι h ∙ y         ≈⟨ ιh∙y ⟩
  z               ∎

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = record
  { refl = ≋-refl
  ; sym = ≋-sym
  ; trans = ≋-trans
  }

≈⇒≋ : _≈_ ⇒ _≋_
≈⇒≋ {x} {y} x≈y = N.ε by trans (∙-cong ι.ε-homo x≈y) (identityˡ y)

open AlgDefs _≋_

≋-∙-cong : Congruent₂ _∙_
≋-∙-cong {x} {y} {u} {v} (g by ιg∙x≈y) (h by ιh∙u≈v) = g N.∙ h′ by begin
  ι (g N.∙ h′) ∙ (x ∙ u) ≈⟨ ∙-congʳ (ι.∙-homo g h′) ⟩
  (ι g ∙ ι h′) ∙ (x ∙ u) ≈⟨ assoc (ι g) (ι h′) (x ∙ u) ⟩
  ι g ∙ (ι h′ ∙ (x ∙ u)) ≈⟨ ∙-congˡ (assoc (ι h′) x u) ⟨
  ι g ∙ ((ι h′ ∙ x) ∙ u) ≈⟨ ∙-congˡ (∙-congʳ x∙ιh≈ιh′∙x) ⟨
  ι g ∙ ((x ∙ ι h) ∙ u)  ≈⟨ ∙-congˡ (assoc x (ι h) u) ⟩
  ι g ∙ (x ∙ (ι h ∙ u))  ≈⟨ assoc (ι g) x (ι h ∙ u) ⟨
  (ι g ∙ x) ∙ (ι h ∙ u)  ≈⟨ ∙-cong ιg∙x≈y ιh∙u≈v ⟩
  y ∙ v                  ∎
  where
    h′ : N.Carrier
    h′ = normal h x .proj₁
    x∙ιh≈ιh′∙x : x ∙ ι h ≈ ι h′ ∙ x
    x∙ιh≈ιh′∙x = normal h x .proj₂


≋-⁻¹-cong : Congruent₁ _⁻¹
≋-⁻¹-cong {x} {y} (g by ιg∙x≈y) = g′ by begin
  ι g′ ∙ x ⁻¹       ≈⟨ x⁻¹∙ιg⁻¹≈ιg′∙x⁻¹ ⟨
  x ⁻¹ ∙ ι (g N.⁻¹) ≈⟨ ∙-congˡ (ι.⁻¹-homo g) ⟩
  x ⁻¹ ∙ ι g ⁻¹     ≈⟨ ⁻¹-anti-homo-∙ (ι g) x ⟨
  (ι g ∙ x) ⁻¹      ≈⟨ ⁻¹-cong ιg∙x≈y ⟩
  y ⁻¹              ∎
  where
    g′ : N.Carrier
    g′ = normal (g N.⁻¹) (x ⁻¹) .proj₁
    x⁻¹∙ιg⁻¹≈ιg′∙x⁻¹ : x ⁻¹ ∙ ι (g N.⁻¹) ≈ ι g′ ∙ x ⁻¹
    x⁻¹∙ιg⁻¹≈ιg′∙x⁻¹ = normal (g N.⁻¹) (x ⁻¹) .proj₂

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
    ; identity = record
      { fst = λ x → ≈⇒≋ (identityˡ x)
      ; snd = λ x → ≈⇒≋ (identityʳ x)
      }
    }
  ; inverse = record
    { fst = λ x → ≈⇒≋ (inverseˡ x)
    ; snd = λ x → ≈⇒≋ (inverseʳ x)
    }
  ; ⁻¹-cong = ≋-⁻¹-cong
  }

quotientGroup : Group c (c ⊔ ℓ ⊔ c′)
quotientGroup = record { isGroup = quotientIsGroup }

η : Group.Carrier G → Group.Carrier quotientGroup
η x = x -- because we do all the work in the relation

η-isHomomorphism : IsGroupHomomorphism rawGroup (Group.rawGroup quotientGroup) η
η-isHomomorphism = record
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

