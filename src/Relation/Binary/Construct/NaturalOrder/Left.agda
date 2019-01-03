------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of binary operators to binary relations via the left
-- natural order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
open import Algebra.FunctionProperties using (Op₂)

module Relation.Binary.Construct.NaturalOrder.Left
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A) where

open import Algebra.FunctionProperties _≈_
open import Algebra.Structures _≈_
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.Lattice using (Infimum)

------------------------------------------------------------------------
-- Definition

infix 4 _≤_

_≤_ : Rel A ℓ
x ≤ y = x ≈ (x ∙ y)

------------------------------------------------------------------------
-- Relational properties

reflexive : IsMagma _∙_ → Idempotent _∙_ → _≈_ ⇒ _≤_
reflexive magma idem {x} {y} x≈y = begin
  x     ≈⟨ sym (idem x) ⟩
  x ∙ x ≈⟨ ∙-cong refl x≈y ⟩
  x ∙ y ∎
  where open IsMagma magma; open EqReasoning setoid

refl : Symmetric _≈_ → Idempotent _∙_ → Reflexive _≤_
refl sym idem {x} = sym (idem x)

antisym : IsEquivalence _≈_ → Commutative _∙_ → Antisymmetric _≈_ _≤_
antisym isEq comm {x} {y} x≤y y≤x = begin
  x     ≈⟨ x≤y ⟩
  x ∙ y ≈⟨ comm x y ⟩
  y ∙ x ≈⟨ sym y≤x ⟩
  y     ∎
  where open IsEquivalence isEq; open EqReasoning (record { isEquivalence = isEq })

total : Symmetric _≈_ → Transitive _≈_ → Selective _∙_ → Commutative _∙_ → Total _≤_
total sym trans sel comm x y with sel x y
... | inj₁ x∙y≈x = inj₁ (sym x∙y≈x)
... | inj₂ x∙y≈y = inj₂ (sym (trans (comm y x) x∙y≈y))

trans : IsSemigroup _∙_ → Transitive _≤_
trans semi {x} {y} {z} x≤y y≤z = begin
  x           ≈⟨ x≤y ⟩
  x ∙ y       ≈⟨ ∙-cong S.refl y≤z ⟩
  x ∙ (y ∙ z) ≈⟨ sym (assoc x y z) ⟩
  (x ∙ y) ∙ z ≈⟨ ∙-cong (sym x≤y) S.refl ⟩
  x ∙ z       ∎
  where open module S = IsSemigroup semi; open EqReasoning S.setoid

respʳ : IsMagma _∙_ → _≤_ Respectsʳ _≈_
respʳ magma {x} {y} {z} y≈z x≤y = begin
  x     ≈⟨ x≤y ⟩
  x ∙ y ≈⟨ ∙-cong M.refl y≈z ⟩
  x ∙ z ∎
  where open module M = IsMagma magma; open EqReasoning M.setoid

respˡ : IsMagma _∙_ → _≤_ Respectsˡ _≈_
respˡ magma {x} {y} {z} y≈z y≤x = begin
  z     ≈⟨ sym y≈z ⟩
  y     ≈⟨ y≤x ⟩
  y ∙ x ≈⟨ ∙-cong y≈z M.refl ⟩
  z ∙ x ∎
  where open module M = IsMagma magma; open EqReasoning M.setoid

resp₂ : IsMagma _∙_ →  _≤_ Respects₂ _≈_
resp₂ magma = respʳ magma , respˡ magma

dec : Decidable _≈_ → Decidable _≤_
dec _≟_ x y = x ≟ (x ∙ y)

module _ (semi : IsSemilattice _∙_) where

  private open module S = IsSemilattice semi
  open EqReasoning setoid

  x∙y≤x : ∀ x y → (x ∙ y) ≤ x
  x∙y≤x x y = begin
    x ∙ y       ≈⟨ ∧-cong (sym (idem x)) S.refl ⟩
    (x ∙ x) ∙ y ≈⟨ assoc x x y ⟩
    x ∙ (x ∙ y) ≈⟨ comm x (x ∙ y) ⟩
    (x ∙ y) ∙ x ∎

  x∙y≤y : ∀ x y → (x ∙ y) ≤ y
  x∙y≤y x y = begin
    x ∙ y        ≈⟨ ∧-cong S.refl (sym (idem y)) ⟩
    x ∙ (y ∙ y)  ≈⟨ sym (assoc x y y) ⟩
    (x ∙ y) ∙ y  ∎

  ∙-presʳ-≤ : ∀ {x y} z → z ≤ x → z ≤ y → z ≤ (x ∙ y)
  ∙-presʳ-≤ {x} {y} z z≤x z≤y = begin
    z            ≈⟨ z≤y ⟩
    z ∙ y        ≈⟨ ∧-cong z≤x S.refl ⟩
    (z ∙ x) ∙ y  ≈⟨ assoc z x y ⟩
    z ∙ (x ∙ y)  ∎

  infimum : Infimum _≤_ _∙_
  infimum x y = x∙y≤x x y , x∙y≤y x y , ∙-presʳ-≤

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
  ; total          = total sym S.trans sel comm
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
