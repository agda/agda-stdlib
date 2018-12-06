------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of binary operators to binary relations via the right
-- natural order.
------------------------------------------------------------------------

open import Relation.Binary
open import Algebra.FunctionProperties using (Op₂)

module Relation.Binary.Construct.NaturalOrder.Right
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A) where

open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Algebra.FunctionProperties _≈_
open import Algebra.Structures _≈_
import Relation.Binary.EqReasoning as EqReasoning

------------------------------------------------------------------------
-- Definition

infix 4 _≤_

_≤_ : Rel A ℓ
x ≤ y = (y ∙ x) ≈ x

------------------------------------------------------------------------
-- Relational properties

reflexive : IsMagma _∙_ → Idempotent _∙_ → _≈_ ⇒ _≤_
reflexive magma idem {x} {y} x≈y = begin
  y ∙ x ≈⟨ ∙-cong (sym x≈y) refl ⟩
  x ∙ x ≈⟨ idem x ⟩
  x     ∎
  where open IsMagma magma; open EqReasoning setoid

refl : Idempotent _∙_ → Reflexive _≤_
refl idem {x} = idem x

antisym : IsEquivalence _≈_ → Commutative _∙_ → Antisymmetric _≈_ _≤_
antisym isEq comm {x} {y} x≤y y≤x = trans (trans (sym x≤y) (comm y x)) y≤x
  where open IsEquivalence isEq

total : Transitive _≈_ → Selective _∙_ → Commutative _∙_ → Total _≤_
total trans sel comm x y with sel x y
... | inj₁ x∙y≈x = inj₁ (trans (comm y x) x∙y≈x)
... | inj₂ x∙y≈y = inj₂ x∙y≈y

trans : IsSemigroup _∙_ → Transitive _≤_
trans semi {x} {y} {z} x≤y y≤z = begin
  z ∙ x       ≈⟨ ∙-cong S.refl (sym x≤y) ⟩
  z ∙ (y ∙ x) ≈⟨ sym (assoc z y x) ⟩
  (z ∙ y) ∙ x ≈⟨ ∙-cong y≤z S.refl ⟩
  y ∙ x       ≈⟨ x≤y ⟩
  x           ∎
  where open module S = IsSemigroup semi; open EqReasoning S.setoid

respʳ : IsMagma _∙_ → _≤_ Respectsʳ _≈_
respʳ magma {x} {y} {z} y≈z x≤y = begin
  z ∙ x ≈⟨ ∙-cong (M.sym y≈z) M.refl ⟩
  y ∙ x ≈⟨ x≤y ⟩
  x     ∎
  where open module M = IsMagma magma; open EqReasoning M.setoid

respˡ : IsMagma _∙_ → _≤_ Respectsˡ _≈_
respˡ magma {x} {y} {z} y≈z y≤x = begin
  x ∙ z ≈⟨ ∙-cong M.refl (M.sym y≈z) ⟩
  x ∙ y ≈⟨ y≤x ⟩
  y     ≈⟨ y≈z ⟩
  z     ∎
  where open module M = IsMagma magma; open EqReasoning M.setoid

resp₂ : IsMagma _∙_ →  _≤_ Respects₂ _≈_
resp₂ magma = respʳ magma , respˡ magma

dec : Decidable _≈_ → Decidable _≤_
dec _≟_ x y = (y ∙ x) ≟ x

------------------------------------------------------------------------
-- Structures

isPreorder : IsBand _∙_ → IsPreorder _≈_ _≤_
isPreorder band = record
  { isEquivalence = isEquivalence
  ; reflexive     = reflexive isMagma idem
  ; trans         = trans isSemigroup
  }
  where open IsBand band hiding (reflexive; trans)

isPartialOrder : IsSemilattice _∙_ → IsPartialOrder _≈_ _≤_
isPartialOrder semilattice = record
  { isPreorder = isPreorder isBand
  ; antisym    = antisym isEquivalence comm
  }
  where open IsSemilattice semilattice

isDecPartialOrder : IsSemilattice _∙_ → Decidable _≈_ →
                    IsDecPartialOrder _≈_ _≤_
isDecPartialOrder semilattice _≟_ = record
  { isPartialOrder = isPartialOrder semilattice
  ; _≟_            = _≟_
  ; _≤?_           = dec _≟_
  }

isTotalOrder : IsSemilattice _∙_ → Selective _∙_ → IsTotalOrder _≈_ _≤_
isTotalOrder latt sel  = record
  { isPartialOrder = isPartialOrder latt
  ; total          = total S.trans sel comm
  }
  where open module S = IsSemilattice latt

isDecTotalOrder : IsSemilattice _∙_ → Selective _∙_ →
                  Decidable _≈_ → IsDecTotalOrder _≈_ _≤_
isDecTotalOrder latt sel _≟_ = record
  { isTotalOrder = isTotalOrder latt sel
  ; _≟_          = _≟_
  ; _≤?_         = dec _≟_
  }

------------------------------------------------------------------------
-- Packages

preorder : IsBand _∙_ → Preorder a ℓ ℓ
preorder band = record
  { isPreorder = isPreorder band
  }

poset : IsSemilattice _∙_ → Poset a ℓ ℓ
poset latt = record
  { isPartialOrder = isPartialOrder latt
  }

decPoset : IsSemilattice _∙_ → Decidable _≈_ → DecPoset a ℓ ℓ
decPoset latt dec = record
  { isDecPartialOrder = isDecPartialOrder latt dec
  }

totalOrder : IsSemilattice _∙_ → Selective _∙_ → TotalOrder a ℓ ℓ
totalOrder latt sel = record
  { isTotalOrder = isTotalOrder latt sel
  }

decTotalOrder : IsSemilattice _∙_ → Selective _∙_ →
                Decidable _≈_ → DecTotalOrder a ℓ ℓ
decTotalOrder latt sel dec = record
  { isDecTotalOrder = isDecTotalOrder latt sel dec
  }
