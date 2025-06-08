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
  _by_ : ∀ g → x // y ≈ ι g → x ≋ y

≋-refl : Reflexive _≋_
≋-refl {x} = N.ε by begin
  x // x ≈⟨ inverseʳ x ⟩
  ε      ≈⟨ ι.ε-homo ⟨
  ι N.ε  ∎

≋-sym : Symmetric _≋_
≋-sym {x} {y} (g by x//y≈ιg) = g N.⁻¹ by begin
  y // x      ≈⟨ ⁻¹-anti-homo-// x y ⟨
  (x // y) ⁻¹ ≈⟨ ⁻¹-cong x//y≈ιg ⟩
  ι g ⁻¹      ≈⟨ ι.⁻¹-homo g ⟨
  ι (g N.⁻¹)  ∎


≋-trans : Transitive _≋_
≋-trans {x} {y} {z} (g by x//y≈ιg) (h by y//z≈ιh) = g N.∙ h by begin
  x // z              ≈⟨ ∙-congʳ (identityʳ x) ⟨
  x ∙ ε // z          ≈⟨ ∙-congʳ (∙-congˡ (inverseˡ y)) ⟨
  x ∙ (y \\ y) // z   ≈⟨ ∙-congʳ (assoc x (y ⁻¹) y) ⟨
  (x // y) ∙ y // z   ≈⟨ assoc (x // y) y (z ⁻¹) ⟩
  (x // y) ∙ (y // z) ≈⟨ ∙-cong x//y≈ιg y//z≈ιh ⟩
  ι g ∙ ι h           ≈⟨ ι.∙-homo g h ⟨
  ι (g N.∙ h)         ∎

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = record
  { refl = ≋-refl
  ; sym = ≋-sym
  ; trans = ≋-trans
  }

≈⇒≋ : _≈_ ⇒ _≋_
≈⇒≋ {x} {y} x≈y = N.ε by begin
  x // y ≈⟨ x≈y⇒x∙y⁻¹≈ε x≈y ⟩
  ε      ≈⟨ ι.ε-homo ⟨
  ι N.ε  ∎

open AlgDefs _≋_

≋-∙-cong : Congruent₂ _∙_
≋-∙-cong {x} {y} {u} {v} (g by x//y≈ιg) (h by u//v≈ιh) = g N.∙ normal h y .proj₁ by begin
  x ∙ u // y ∙ v              ≈⟨ ∙-congˡ (⁻¹-anti-homo-∙ y v) ⟩
  x ∙ u ∙ (v ⁻¹ ∙ y ⁻¹)       ≈⟨ assoc (x ∙ u) (v ⁻¹) (y ⁻¹) ⟨
  (x ∙ u // v) // y           ≈⟨ ∙-congʳ (assoc x u (v ⁻¹)) ⟩
  x ∙ (u // v) // y           ≈⟨ ∙-congʳ (∙-congˡ u//v≈ιh) ⟩
  x ∙ ι h // y                ≈⟨ ∙-congʳ (∙-congˡ (identityˡ (ι h))) ⟨
  x ∙ (ε ∙ ι h) // y          ≈⟨ ∙-congʳ (∙-congˡ (∙-congʳ (inverseˡ y))) ⟨
  x ∙ ((y \\ y) ∙ ι h) // y   ≈⟨ ∙-congʳ (∙-congˡ (assoc (y ⁻¹) y (ι h))) ⟩
  x ∙ (y \\ y ∙ ι h) // y     ≈⟨ ∙-congʳ (assoc x (y ⁻¹) (y ∙ ι h)) ⟨
  (x // y) ∙ (y ∙ ι h) // y   ≈⟨ assoc (x // y) (y ∙ ι h) (y ⁻¹) ⟩
  (x // y) ∙ (y ∙ ι h // y)   ≈⟨ ∙-cong x//y≈ιg (proj₂ (normal h y)) ⟩
  ι g ∙ ι (normal h y .proj₁) ≈⟨ ι.∙-homo g (normal h y .proj₁) ⟨
  ι (g N.∙ normal h y .proj₁) ∎

≋-⁻¹-cong : Congruent₁ _⁻¹
≋-⁻¹-cong {x} {y} (g by x//y≈ιg) = normal (g N.⁻¹) (y ⁻¹) .proj₁ by begin
  x ⁻¹ ∙ y ⁻¹ ⁻¹                      ≈⟨ ∙-congʳ (identityˡ (x ⁻¹)) ⟨
  (ε ∙ x ⁻¹) ∙ y ⁻¹ ⁻¹                ≈⟨ ∙-congʳ (∙-congʳ (inverseʳ (y ⁻¹))) ⟨
  ((y ⁻¹ ∙ y ⁻¹ ⁻¹) ∙ x ⁻¹) ∙ y ⁻¹ ⁻¹ ≈⟨ ∙-congʳ (assoc (y ⁻¹) ((y ⁻¹) ⁻¹) (x ⁻¹)) ⟩
  y ⁻¹ ∙ (y ⁻¹ ⁻¹ ∙ x ⁻¹) ∙ y ⁻¹ ⁻¹   ≈⟨ ∙-congʳ (∙-congˡ (⁻¹-anti-homo-∙ x (y ⁻¹))) ⟨
  y ⁻¹ ∙ (x ∙ y ⁻¹) ⁻¹ ∙ y ⁻¹ ⁻¹      ≈⟨ ∙-congʳ (∙-congˡ (⁻¹-cong x//y≈ιg)) ⟩
  y ⁻¹ ∙ ι g ⁻¹ ∙ y ⁻¹ ⁻¹             ≈⟨ ∙-congʳ (∙-congˡ (ι.⁻¹-homo g)) ⟨
  y ⁻¹ ∙ ι (g N.⁻¹) ∙ y ⁻¹ ⁻¹         ≈⟨ proj₂ (normal (g N.⁻¹) (y ⁻¹)) ⟩
  ι (normal (g N.⁻¹) (y ⁻¹) .proj₁)   ∎

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

