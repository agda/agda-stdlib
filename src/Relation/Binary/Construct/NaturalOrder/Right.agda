------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of binary operators to binary relations via the right
-- natural order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core using (Op₂)
open import Data.Product.Base using (_,_; _×_)
open import Data.Sum.Base using (inj₁; inj₂; map)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles
  using (Preorder; Poset; DecPoset; TotalOrder; DecTotalOrder)
open import Relation.Binary.Structures
  using (IsEquivalence; IsPreorder; IsPartialOrder; IsDecPartialOrder
        ; IsTotalOrder; IsDecTotalOrder)
open import Relation.Binary.Definitions
  using (Symmetric; Transitive; Reflexive; Antisymmetric; Total; _Respectsʳ_
        ; _Respectsˡ_; _Respects₂_; Decidable)

open import Relation.Nullary.Negation using (¬_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

module Relation.Binary.Construct.NaturalOrder.Right
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A) where

open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Algebra.Lattice.Structures _≈_

------------------------------------------------------------------------
-- Definition

infix 4 _≤_

_≤_ : Rel A ℓ
x ≤ y = x ≈ (y ∙ x)

------------------------------------------------------------------------
-- Relational properties

reflexive : IsMagma _∙_ → Idempotent _∙_ → _≈_ ⇒ _≤_
reflexive magma idem {x} {y} x≈y = begin
  x     ≈⟨ sym (idem x) ⟩
  x ∙ x ≈⟨ ∙-cong x≈y refl ⟩
  y ∙ x ∎
  where open IsMagma magma; open ≈-Reasoning setoid

refl : Symmetric _≈_ → Idempotent _∙_ → Reflexive _≤_
refl sym idem {x} = sym (idem x)

antisym : IsEquivalence _≈_ → Commutative _∙_ → Antisymmetric _≈_ _≤_
antisym isEq comm {x} {y} x≤y y≤x = begin
  x     ≈⟨  x≤y ⟩
  y ∙ x ≈⟨  comm y x ⟩
  x ∙ y ≈⟨ y≤x ⟨
  y     ∎
  where open ≈-Reasoning (record { isEquivalence = isEq })

total : Symmetric _≈_ → Transitive _≈_ → Selective _∙_ → Commutative _∙_ → Total _≤_
total sym trans sel comm x y =
  map (λ x∙y≈x → trans (sym x∙y≈x) (comm x y)) sym (sel x y)

trans : IsSemigroup _∙_ → Transitive _≤_
trans semi {x} {y} {z} x≤y y≤z = begin
  x           ≈⟨ x≤y ⟩
  y ∙ x       ≈⟨ ∙-cong y≤z S.refl ⟩
  (z ∙ y) ∙ x ≈⟨ assoc z y x ⟩
  z ∙ (y ∙ x) ≈⟨ ∙-cong S.refl (sym x≤y) ⟩
  z ∙ x       ∎
  where open module S = IsSemigroup semi; open ≈-Reasoning S.setoid

respʳ : IsMagma _∙_ → _≤_ Respectsʳ _≈_
respʳ magma {x} {y} {z} y≈z x≤y = begin
  x     ≈⟨ x≤y ⟩
  y ∙ x ≈⟨ ∙-cong y≈z M.refl ⟩
  z ∙ x ∎
  where open module M = IsMagma magma; open ≈-Reasoning M.setoid

respˡ : IsMagma _∙_ → _≤_ Respectsˡ _≈_
respˡ magma {x} {y} {z} y≈z y≤x = begin
  z     ≈⟨ sym y≈z ⟩
  y     ≈⟨ y≤x ⟩
  x ∙ y ≈⟨ ∙-cong M.refl y≈z ⟩
  x ∙ z ∎
  where open module M = IsMagma magma; open ≈-Reasoning M.setoid

resp₂ : IsMagma _∙_ →  _≤_ Respects₂ _≈_
resp₂ magma = respʳ magma , respˡ magma

dec : Decidable _≈_ → Decidable _≤_
dec _≟_ x y = x ≟ (y ∙ x)

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
-- Bundles

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
