------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotient groups
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Group)
open import Algebra.Construct.Sub.Group.Normal using (NormalSubgroup)

module Algebra.Construct.Quotient.Group
  {c ℓ} (G : Group c ℓ) {c′ ℓ′} (N : NormalSubgroup G c′ ℓ′) where

open import Algebra.Definitions using (Congruent₁; Congruent₂)
open import Algebra.Morphism.Structures using (IsGroupHomomorphism)
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_)
open import Function.Definitions using (Surjective)
open import Level using (_⊔_)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)

private
  open module G = Group G
    using (_≈_; _∙_; ε; _⁻¹)
  open module N = NormalSubgroup N
    using (ι; module ι; conjugate; normal)

open import Algebra.Properties.Group G using (⁻¹-anti-homo-∙)
open import Algebra.Properties.Monoid G.monoid
open import Relation.Binary.Reasoning.Setoid G.setoid

infix 0 _by_

data _≋_ (x y : G.Carrier) : Set (c ⊔ ℓ ⊔ c′) where
  _by_ : ∀ g → ι g ∙ x ≈ y → x ≋ y

≈⇒≋ : _≈_ ⇒ _≋_
≈⇒≋ x≈y = N.ε by G.trans (G.∙-cong ι.ε-homo x≈y) (G.identityˡ _)

refl : Reflexive _≋_
refl = ≈⇒≋ G.refl

sym : Symmetric _≋_
sym {x} {y} (g by ιg∙x≈y) = g N.⁻¹ by begin
  ι (g N.⁻¹) ∙ y      ≈⟨ G.∙-cong (ι.⁻¹-homo g) (G.sym ιg∙x≈y) ⟩
  ι g ⁻¹ ∙ (ι g ∙ x)  ≈⟨ cancelˡ (G.inverseˡ (ι g)) x ⟩
  x                   ∎

trans : Transitive _≋_
trans {x} {y} {z} (g by ιg∙x≈y) (h by ιh∙y≈z) = h N.∙ g by begin
  ι (h N.∙ g) ∙ x ≈⟨ G.∙-congʳ (ι.∙-homo h g) ⟩
  (ι h ∙ ι g) ∙ x ≈⟨ uv≈w⇒xu∙v≈xw ιg∙x≈y (ι h) ⟩
  ι h ∙ y         ≈⟨ ιh∙y≈z ⟩
  z               ∎

∙-cong : Congruent₂ _≋_ _∙_
∙-cong {x} {y} {u} {v} (g by ιg∙x≈y) (h by ιh∙u≈v) = g N.∙ h′ by begin
  ι (g N.∙ h′) ∙ (x ∙ u) ≈⟨ G.∙-congʳ (ι.∙-homo g h′) ⟩
  (ι g ∙ ι h′) ∙ (x ∙ u) ≈⟨ uv≈wx⇒yu∙vz≈yw∙xz (normal h x) (ι g) u ⟩
  (ι g ∙ x) ∙ (ι h ∙ u)  ≈⟨ G.∙-cong ιg∙x≈y ιh∙u≈v ⟩
  y ∙ v                  ∎
  where h′ = conjugate h x

⁻¹-cong : Congruent₁ _≋_ _⁻¹
⁻¹-cong {x} {y} (g by ιg∙x≈y) = h by begin
  ι h ∙ x ⁻¹        ≈⟨ normal (g N.⁻¹) (x ⁻¹) ⟩
  x ⁻¹ ∙ ι (g N.⁻¹) ≈⟨ G.∙-congˡ (ι.⁻¹-homo g) ⟩
  x ⁻¹ ∙ ι g ⁻¹     ≈⟨ ⁻¹-anti-homo-∙ (ι g) x ⟨
  (ι g ∙ x) ⁻¹      ≈⟨ G.⁻¹-cong ιg∙x≈y ⟩
  y ⁻¹              ∎
  where h = conjugate (g N.⁻¹) (x ⁻¹)

group : Group c (c ⊔ ℓ ⊔ c′)
group = record
  { isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record
            { refl = refl
            ; sym = sym
            ; trans = trans
            }
          ; ∙-cong = ∙-cong
          }
        ; assoc = λ x y z → ≈⇒≋ (G.assoc x y z)
        }
      ; identity = ≈⇒≋ ∘ G.identityˡ , ≈⇒≋ ∘ G.identityʳ
      }
    ; inverse = ≈⇒≋ ∘ G.inverseˡ , ≈⇒≋ ∘ G.inverseʳ
    ; ⁻¹-cong = ⁻¹-cong
    }
  }

private module Q = Group group

-- Public re-exports

_/_ : Group c (c ⊔ ℓ ⊔ c′)
_/_ = group

π : G.Carrier → Q.Carrier
π x = x -- because we do all the work in the relation _≋_

π-surjective : Surjective _≈_ _≋_ π
π-surjective g = g , ≈⇒≋

π-isGroupHomomorphism : IsGroupHomomorphism G.rawGroup Q.rawGroup π
π-isGroupHomomorphism = record
  { isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = ≈⇒≋
        }
      ; homo = λ _ _ → refl
      }
    ; ε-homo = refl
    }
  ; ⁻¹-homo = λ _ → refl
  }

open IsGroupHomomorphism π-isGroupHomomorphism public
  using ()
  renaming (isMonoidHomomorphism to π-isMonoidHomomorphism
           ; isMagmaHomomorphism to π-isMagmaHomomorphism
           )
