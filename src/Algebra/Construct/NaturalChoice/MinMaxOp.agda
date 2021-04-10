------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of min and max operators specified over a total order
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Construct.NaturalChoice.Base
open import Data.Sum.Base as Sum using (inj₁; inj₂; [_,_])
open import Data.Product using (_,_)
open import Function.Base using (id; _∘_; flip)
open import Relation.Binary
open import Relation.Binary.Consequences

module Algebra.Construct.NaturalChoice.MinMaxOp
  {a ℓ₁ ℓ₂} {O : TotalPreorder a ℓ₁ ℓ₂}
  (minOp : MinOperator O)
  (maxOp : MaxOperator O)
  where

open TotalPreorder O renaming
  ( Carrier   to A
  ; _≲_       to _≤_
  ; ≲-resp-≈  to ≤-resp-≈
  ; ≲-respʳ-≈ to ≤-respʳ-≈
  ; ≲-respˡ-≈ to ≤-respˡ-≈
  )
open MinOperator minOp
open MaxOperator maxOp

open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Algebra.Consequences.Setoid Eq.setoid
open import Relation.Binary.Reasoning.Preorder preorder

------------------------------------------------------------------------
-- Re-export properties of individual operators

open import Algebra.Construct.NaturalChoice.MinOp minOp public
open import Algebra.Construct.NaturalChoice.MaxOp maxOp public

------------------------------------------------------------------------
-- Joint algebraic structures

⊓-distribˡ-⊔ : _⊓_ DistributesOverˡ _⊔_
⊓-distribˡ-⊔ x y z with total y z
... | inj₁ y≤z = begin-equality
  x ⊓ (y ⊔ z)       ≈⟨  ⊓-congˡ x (x≤y⇒x⊔y≈y y≤z) ⟩
  x ⊓ z             ≈˘⟨ x≤y⇒x⊔y≈y (⊓-monoʳ-≤ x y≤z) ⟩
  (x ⊓ y) ⊔ (x ⊓ z) ∎
... | inj₂ y≥z = begin-equality
  x ⊓ (y ⊔ z)       ≈⟨  ⊓-congˡ x (x≥y⇒x⊔y≈x y≥z) ⟩
  x ⊓ y             ≈˘⟨ x≥y⇒x⊔y≈x (⊓-monoʳ-≤ x y≥z) ⟩
  (x ⊓ y) ⊔ (x ⊓ z) ∎

⊓-distribʳ-⊔ : _⊓_ DistributesOverʳ _⊔_
⊓-distribʳ-⊔ = comm+distrˡ⇒distrʳ ⊔-cong ⊓-comm ⊓-distribˡ-⊔

⊓-distrib-⊔ : _⊓_ DistributesOver _⊔_
⊓-distrib-⊔ = ⊓-distribˡ-⊔ , ⊓-distribʳ-⊔

⊔-distribˡ-⊓ : _⊔_ DistributesOverˡ _⊓_
⊔-distribˡ-⊓ x y z with total y z
... | inj₁ y≤z = begin-equality
  x ⊔ (y ⊓ z)       ≈⟨  ⊔-congˡ x (x≤y⇒x⊓y≈x y≤z) ⟩
  x ⊔ y             ≈˘⟨ x≤y⇒x⊓y≈x (⊔-monoʳ-≤ x y≤z) ⟩
  (x ⊔ y) ⊓ (x ⊔ z) ∎
... | inj₂ y≥z = begin-equality
  x ⊔ (y ⊓ z)       ≈⟨  ⊔-congˡ x (x≥y⇒x⊓y≈y y≥z) ⟩
  x ⊔ z             ≈˘⟨ x≥y⇒x⊓y≈y (⊔-monoʳ-≤ x y≥z) ⟩
  (x ⊔ y) ⊓ (x ⊔ z) ∎

⊔-distribʳ-⊓ : _⊔_ DistributesOverʳ _⊓_
⊔-distribʳ-⊓ = comm+distrˡ⇒distrʳ ⊓-cong ⊔-comm ⊔-distribˡ-⊓

⊔-distrib-⊓ : _⊔_ DistributesOver _⊓_
⊔-distrib-⊓ = ⊔-distribˡ-⊓ , ⊔-distribʳ-⊓

⊓-absorbs-⊔ : _⊓_ Absorbs _⊔_
⊓-absorbs-⊔ x y with total x y
... | inj₁ x≤y = begin-equality
  x ⊓ (x ⊔ y)  ≈⟨ ⊓-congˡ x (x≤y⇒x⊔y≈y x≤y) ⟩
  x ⊓ y        ≈⟨ x≤y⇒x⊓y≈x x≤y ⟩
  x            ∎
... | inj₂ y≤x = begin-equality
  x ⊓ (x ⊔ y)  ≈⟨ ⊓-congˡ x (x≥y⇒x⊔y≈x y≤x) ⟩
  x ⊓ x        ≈⟨ ⊓-idem x ⟩
  x            ∎

⊔-absorbs-⊓ : _⊔_ Absorbs _⊓_
⊔-absorbs-⊓ x y with total x y
... | inj₁ x≤y = begin-equality
  x ⊔ (x ⊓ y)  ≈⟨ ⊔-congˡ x (x≤y⇒x⊓y≈x x≤y) ⟩
  x ⊔ x        ≈⟨ ⊔-idem x ⟩
  x            ∎
... | inj₂ y≤x = begin-equality
  x ⊔ (x ⊓ y)  ≈⟨ ⊔-congˡ x (x≥y⇒x⊓y≈y y≤x) ⟩
  x ⊔ y        ≈⟨ x≥y⇒x⊔y≈x y≤x ⟩
  x            ∎

⊔-⊓-absorptive : Absorptive _⊔_ _⊓_
⊔-⊓-absorptive = ⊔-absorbs-⊓ , ⊓-absorbs-⊔

⊓-⊔-absorptive : Absorptive _⊓_ _⊔_
⊓-⊔-absorptive = ⊓-absorbs-⊔ , ⊔-absorbs-⊓

⊔-⊓-isLattice : IsLattice _⊔_ _⊓_
⊔-⊓-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = ⊔-comm
  ; ∨-assoc       = ⊔-assoc
  ; ∨-cong        = ⊔-cong
  ; ∧-comm        = ⊓-comm
  ; ∧-assoc       = ⊓-assoc
  ; ∧-cong        = ⊓-cong
  ; absorptive    = ⊔-⊓-absorptive
  }

⊓-⊔-isLattice : IsLattice _⊓_ _⊔_
⊓-⊔-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = ⊓-comm
  ; ∨-assoc       = ⊓-assoc
  ; ∨-cong        = ⊓-cong
  ; ∧-comm        = ⊔-comm
  ; ∧-assoc       = ⊔-assoc
  ; ∧-cong        = ⊔-cong
  ; absorptive    = ⊓-⊔-absorptive
  }

⊓-⊔-isDistributiveLattice : IsDistributiveLattice _⊓_ _⊔_
⊓-⊔-isDistributiveLattice = record
  { isLattice    = ⊓-⊔-isLattice
  ; ∨-distribʳ-∧ = ⊓-distribʳ-⊔
  }

⊔-⊓-isDistributiveLattice : IsDistributiveLattice _⊔_ _⊓_
⊔-⊓-isDistributiveLattice = record
  { isLattice    = ⊔-⊓-isLattice
  ; ∨-distribʳ-∧ = ⊔-distribʳ-⊓
  }

⊔-⊓-lattice : Lattice _ _
⊔-⊓-lattice = record
  { isLattice = ⊔-⊓-isLattice
  }

⊓-⊔-lattice : Lattice _ _
⊓-⊔-lattice = record
  { isLattice = ⊓-⊔-isLattice
  }

⊔-⊓-distributiveLattice : DistributiveLattice _ _
⊔-⊓-distributiveLattice = record
  { isDistributiveLattice = ⊔-⊓-isDistributiveLattice
  }

⊓-⊔-distributiveLattice : DistributiveLattice _ _
⊓-⊔-distributiveLattice = record
  { isDistributiveLattice = ⊓-⊔-isDistributiveLattice
  }

------------------------------------------------------------------------
-- Other joint properties

private _≥_ = flip _≤_

antimono-≤-distrib-⊓ : ∀ {f} → f Preserves _≈_ ⟶ _≈_ → f Preserves _≤_ ⟶ _≥_ →
                       ∀ x y → f (x ⊓ y) ≈ f x ⊔ f y
antimono-≤-distrib-⊓ {f} cong antimono x y with total x y
... | inj₁ x≤y = begin-equality
  f (x ⊓ y)  ≈⟨ cong (x≤y⇒x⊓y≈x x≤y) ⟩
  f x        ≈˘⟨ x≥y⇒x⊔y≈x (antimono x≤y) ⟩
  f x ⊔ f y  ∎
... | inj₂ y≤x = begin-equality
  f (x ⊓ y)  ≈⟨ cong (x≥y⇒x⊓y≈y y≤x) ⟩
  f y        ≈˘⟨ x≤y⇒x⊔y≈y (antimono y≤x) ⟩
  f x ⊔ f y  ∎

antimono-≤-distrib-⊔ : ∀ {f} → f Preserves _≈_ ⟶ _≈_ → f Preserves _≤_ ⟶ _≥_ →
                       ∀ x y → f (x ⊔ y) ≈ f x ⊓ f y
antimono-≤-distrib-⊔ {f} cong antimono x y with total x y
... | inj₁ x≤y = begin-equality
  f (x ⊔ y)  ≈⟨ cong (x≤y⇒x⊔y≈y x≤y) ⟩
  f y        ≈˘⟨ x≥y⇒x⊓y≈y (antimono x≤y) ⟩
  f x ⊓ f y  ∎
... | inj₂ y≤x = begin-equality
  f (x ⊔ y)  ≈⟨ cong (x≥y⇒x⊔y≈x y≤x) ⟩
  f x        ≈˘⟨ x≤y⇒x⊓y≈x (antimono y≤x) ⟩
  f x ⊓ f y  ∎

x⊓y≤x⊔y : ∀ x y → x ⊓ y ≤ x ⊔ y
x⊓y≤x⊔y x y = begin
  x ⊓ y ∼⟨ x⊓y≤x x y ⟩
  x     ∼⟨ x≤x⊔y x y ⟩
  x ⊔ y ∎
