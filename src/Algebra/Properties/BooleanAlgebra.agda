------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.BooleanAlgebra
  {b₁ b₂} (B : BooleanAlgebra b₁ b₂)
  where

open BooleanAlgebra B
import Algebra.Properties.DistributiveLattice as DistribLatticeProperties
open import Algebra.Structures _≈_
open import Algebra.FunctionProperties _≈_
open import Algebra.FunctionProperties.Consequences setoid
open import Relation.Binary.Reasoning.Setoid setoid
open import Relation.Binary
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Data.Product using (_,_)

------------------------------------------------------------------------
-- Export properties from distributive lattices

open DistribLatticeProperties distributiveLattice public
  hiding (replace-equality)

------------------------------------------------------------------------
-- Some simple consequences

∨-complementˡ : LeftInverse ⊤ ¬_ _∨_
∨-complementˡ = comm+invʳ⇒invˡ ∨-comm ∨-complementʳ

∨-complement : Inverse ⊤ ¬_ _∨_
∨-complement = ∨-complementˡ , ∨-complementʳ

∧-complementˡ : LeftInverse ⊥ ¬_ _∧_
∧-complementˡ = comm+invʳ⇒invˡ ∧-comm ∧-complementʳ

∧-complement : Inverse ⊥ ¬_ _∧_
∧-complement = ∧-complementˡ , ∧-complementʳ

------------------------------------------------------------------------
-- The dual construction is also a boolean algebra

∧-∨-isBooleanAlgebra : IsBooleanAlgebra _∧_ _∨_ ¬_ ⊥ ⊤
∧-∨-isBooleanAlgebra = record
  { isDistributiveLattice = ∧-∨-isDistributiveLattice
  ; ∨-complementʳ         = ∧-complementʳ
  ; ∧-complementʳ         = ∨-complementʳ
  ; ¬-cong                = ¬-cong
  }

∧-∨-booleanAlgebra : BooleanAlgebra _ _
∧-∨-booleanAlgebra = record
  { isBooleanAlgebra = ∧-∨-isBooleanAlgebra
  }

------------------------------------------------------------------------
-- (∨, ∧, ⊥, ⊤) and (∧, ∨, ⊤, ⊥) are commutative semirings

∧-identityʳ : RightIdentity ⊤ _∧_
∧-identityʳ x = begin
  x ∧ ⊤          ≈⟨ ∧-congˡ (sym (∨-complementʳ _)) ⟩
  x ∧ (x ∨ ¬ x)  ≈⟨ ∧-absorbs-∨ _ _ ⟩
  x              ∎

∧-identityˡ : LeftIdentity ⊤ _∧_
∧-identityˡ = comm+idʳ⇒idˡ ∧-comm ∧-identityʳ

∧-identity : Identity ⊤ _∧_
∧-identity = ∧-identityˡ , ∧-identityʳ

∨-identityʳ : RightIdentity ⊥ _∨_
∨-identityʳ x = begin
  x ∨ ⊥          ≈⟨ ∨-congˡ $ sym (∧-complementʳ _) ⟩
  x ∨ x ∧ ¬ x    ≈⟨ ∨-absorbs-∧ _ _ ⟩
  x              ∎

∨-identityˡ : LeftIdentity ⊥ _∨_
∨-identityˡ = comm+idʳ⇒idˡ ∨-comm ∨-identityʳ

∨-identity : Identity ⊥ _∨_
∨-identity = ∨-identityˡ , ∨-identityʳ

∧-zeroʳ : RightZero ⊥ _∧_
∧-zeroʳ x = begin
  x ∧ ⊥          ≈˘⟨ ∧-congˡ (∧-complementʳ x) ⟩
  x ∧  x  ∧ ¬ x  ≈˘⟨ ∧-assoc x x (¬ x) ⟩
  (x ∧ x) ∧ ¬ x  ≈⟨  ∧-congʳ (∧-idempotent x) ⟩
  x       ∧ ¬ x  ≈⟨  ∧-complementʳ x ⟩
  ⊥              ∎

∧-zeroˡ : LeftZero ⊥ _∧_
∧-zeroˡ = comm+zeʳ⇒zeˡ ∧-comm ∧-zeroʳ

∧-zero : Zero ⊥ _∧_
∧-zero = ∧-zeroˡ , ∧-zeroʳ

∨-zeroʳ : ∀ x → x ∨ ⊤ ≈ ⊤
∨-zeroʳ x = begin
  x ∨ ⊤          ≈˘⟨ ∨-congˡ (∨-complementʳ x) ⟩
  x ∨  x  ∨ ¬ x  ≈˘⟨ ∨-assoc x x (¬ x) ⟩
  (x ∨ x) ∨ ¬ x  ≈⟨ ∨-congʳ (∨-idempotent x) ⟩
  x       ∨ ¬ x  ≈⟨ ∨-complementʳ x ⟩
  ⊤              ∎

∨-zeroˡ : LeftZero ⊤ _∨_
∨-zeroˡ = comm+zeʳ⇒zeˡ ∨-comm ∨-zeroʳ

∨-zero : Zero ⊤ _∨_
∨-zero = ∨-zeroˡ , ∨-zeroʳ

∨-⊥-isMonoid : IsMonoid _∨_ ⊥
∨-⊥-isMonoid = record
  { isSemigroup = ∨-isSemigroup
  ; identity    = ∨-identity
  }

∧-⊤-isMonoid : IsMonoid _∧_ ⊤
∧-⊤-isMonoid = record
  { isSemigroup = ∧-isSemigroup
  ; identity    = ∧-identity
  }

∨-⊥-isCommutativeMonoid : IsCommutativeMonoid _∨_ ⊥
∨-⊥-isCommutativeMonoid = record
  { isSemigroup = ∨-isSemigroup
  ; identityˡ   = ∨-identityˡ
  ; comm        = ∨-comm
  }

∧-⊤-isCommutativeMonoid : IsCommutativeMonoid _∧_ ⊤
∧-⊤-isCommutativeMonoid = record
  { isSemigroup = ∧-isSemigroup
  ; identityˡ   = ∧-identityˡ
  ; comm        = ∧-comm
  }

∨-∧-isCommutativeSemiring : IsCommutativeSemiring _∨_ _∧_ ⊥ ⊤
∨-∧-isCommutativeSemiring = record
  { +-isCommutativeMonoid = ∨-⊥-isCommutativeMonoid
  ; *-isCommutativeMonoid = ∧-⊤-isCommutativeMonoid
  ; distribʳ              = ∧-∨-distribʳ
  ; zeroˡ                 = ∧-zeroˡ
  }

∧-∨-isCommutativeSemiring : IsCommutativeSemiring _∧_ _∨_ ⊤ ⊥
∧-∨-isCommutativeSemiring = record
  { +-isCommutativeMonoid = ∧-⊤-isCommutativeMonoid
  ; *-isCommutativeMonoid = ∨-⊥-isCommutativeMonoid
  ; distribʳ = ∨-∧-distribʳ
  ; zeroˡ    = ∨-zeroˡ
  }

∨-∧-commutativeSemiring : CommutativeSemiring _ _
∨-∧-commutativeSemiring = record
  { isCommutativeSemiring = ∨-∧-isCommutativeSemiring
  }

∧-∨-commutativeSemiring : CommutativeSemiring _ _
∧-∨-commutativeSemiring = record
  { isCommutativeSemiring = ∧-∨-isCommutativeSemiring
  }

------------------------------------------------------------------------
-- Some other properties

-- I took the statement of this lemma (called Uniqueness of
-- Complements) from some course notes, "Boolean Algebra", written
-- by Gert Smolka.

private
  lemma : ∀ x y → x ∧ y ≈ ⊥ → x ∨ y ≈ ⊤ → ¬ x ≈ y
  lemma x y x∧y=⊥ x∨y=⊤ = begin
    ¬ x                ≈˘⟨ ∧-identityʳ _ ⟩
    ¬ x ∧ ⊤            ≈˘⟨ ∧-congˡ x∨y=⊤ ⟩
    ¬ x ∧ (x ∨ y)      ≈⟨  ∧-∨-distribˡ _ _ _ ⟩
    ¬ x ∧ x ∨ ¬ x ∧ y  ≈⟨  ∨-congʳ $ ∧-complementˡ _ ⟩
    ⊥ ∨ ¬ x ∧ y        ≈˘⟨ ∨-congʳ x∧y=⊥ ⟩
    x ∧ y ∨ ¬ x ∧ y    ≈˘⟨ ∧-∨-distribʳ _ _ _ ⟩
    (x ∨ ¬ x) ∧ y      ≈⟨  ∧-congʳ $ ∨-complementʳ _ ⟩
    ⊤ ∧ y              ≈⟨  ∧-identityˡ _ ⟩
    y                  ∎

⊥≉⊤ : ¬ ⊥ ≈ ⊤
⊥≉⊤ = lemma ⊥ ⊤ (∧-identityʳ _) (∨-zeroʳ _)

⊤≉⊥ : ¬ ⊤ ≈ ⊥
⊤≉⊥ = lemma ⊤ ⊥ (∧-zeroʳ _) (∨-identityʳ _)

¬-involutive : Involutive ¬_
¬-involutive x = lemma (¬ x) x (∧-complementˡ _) (∨-complementˡ _)

deMorgan₁ : ∀ x y → ¬ (x ∧ y) ≈ ¬ x ∨ ¬ y
deMorgan₁ x y = lemma (x ∧ y) (¬ x ∨ ¬ y) lem₁ lem₂
  where
  lem₁ = begin
    (x ∧ y) ∧ (¬ x ∨ ¬ y)          ≈⟨ ∧-∨-distribˡ _ _ _ ⟩
    (x ∧ y) ∧ ¬ x ∨ (x ∧ y) ∧ ¬ y  ≈⟨ ∨-congʳ $ ∧-congʳ $ ∧-comm _ _ ⟩
    (y ∧ x) ∧ ¬ x ∨ (x ∧ y) ∧ ¬ y  ≈⟨ ∧-assoc _ _ _ ⟨ ∨-cong ⟩ ∧-assoc _ _ _ ⟩
    y ∧ (x ∧ ¬ x) ∨ x ∧ (y ∧ ¬ y)  ≈⟨ (∧-congˡ $ ∧-complementʳ _) ⟨ ∨-cong ⟩
                                      (∧-congˡ $ ∧-complementʳ _) ⟩
    (y ∧ ⊥) ∨ (x ∧ ⊥)              ≈⟨ ∧-zeroʳ _ ⟨ ∨-cong ⟩ ∧-zeroʳ _ ⟩
    ⊥ ∨ ⊥                          ≈⟨ ∨-identityʳ _ ⟩
    ⊥                              ∎

  lem₃ = begin
    (x ∧ y) ∨ ¬ x          ≈⟨ ∨-∧-distribʳ _ _ _ ⟩
    (x ∨ ¬ x) ∧ (y ∨ ¬ x)  ≈⟨ ∧-congʳ $ ∨-complementʳ _ ⟩
    ⊤ ∧ (y ∨ ¬ x)          ≈⟨ ∧-identityˡ _ ⟩
    y ∨ ¬ x                ≈⟨ ∨-comm _ _ ⟩
    ¬ x ∨ y                ∎

  lem₂ = begin
    (x ∧ y) ∨ (¬ x ∨ ¬ y)  ≈˘⟨ ∨-assoc _ _ _ ⟩
    ((x ∧ y) ∨ ¬ x) ∨ ¬ y  ≈⟨ ∨-congʳ lem₃ ⟩
    (¬ x ∨ y) ∨ ¬ y        ≈⟨ ∨-assoc _ _ _ ⟩
    ¬ x ∨ (y ∨ ¬ y)        ≈⟨ ∨-congˡ $ ∨-complementʳ _ ⟩
    ¬ x ∨ ⊤                ≈⟨ ∨-zeroʳ _ ⟩
    ⊤                      ∎

deMorgan₂ : ∀ x y → ¬ (x ∨ y) ≈ ¬ x ∧ ¬ y
deMorgan₂ x y = begin
  ¬ (x ∨ y)          ≈˘⟨ ¬-cong $ ((¬-involutive _) ⟨ ∨-cong ⟩ (¬-involutive _)) ⟩
  ¬ (¬ ¬ x ∨ ¬ ¬ y)  ≈˘⟨ ¬-cong $ deMorgan₁ _ _ ⟩
  ¬ ¬ (¬ x ∧ ¬ y)    ≈⟨ ¬-involutive _ ⟩
  ¬ x ∧ ¬ y          ∎

-- One can replace the underlying equality with an equivalent one.

replace-equality : {_≈′_ : Rel Carrier b₂} →
                   (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) →
                   BooleanAlgebra _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { _≈_              = _≈′_
  ; _∨_              = _∨_
  ; _∧_              = _∧_
  ; ¬_               = ¬_
  ; ⊤                = ⊤
  ; ⊥                = ⊥
  ; isBooleanAlgebra =  record
    { isDistributiveLattice = DistributiveLattice.isDistributiveLattice
        (DistribLatticeProperties.replace-equality distributiveLattice ≈⇔≈′)
    ; ∨-complementʳ         = λ x → to ⟨$⟩ ∨-complementʳ x
    ; ∧-complementʳ         = λ x → to ⟨$⟩ ∧-complementʳ x
    ; ¬-cong                = λ i≈j → to ⟨$⟩ ¬-cong (from ⟨$⟩ i≈j)
    }
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})

------------------------------------------------------------------------
-- (⊕, ∧, id, ⊥, ⊤) is a commutative ring

-- This construction is parameterised over the definition of xor.

module XorRing
  (xor : Op₂ Carrier)
  (⊕-def : ∀ x y → xor x y ≈ (x ∨ y) ∧ ¬ (x ∧ y))
  where

  private
    infixl 6 _⊕_

    _⊕_ : Op₂ Carrier
    _⊕_ = xor

    helper : ∀ {x y u v} → x ≈ y → u ≈ v → x ∧ ¬ u ≈ y ∧ ¬ v
    helper x≈y u≈v = x≈y ⟨ ∧-cong ⟩ ¬-cong u≈v

  ⊕-cong : Congruent₂ _⊕_
  ⊕-cong {x} {y} {u} {v} x≈y u≈v = begin
    x ⊕ u                ≈⟨  ⊕-def _ _ ⟩
    (x ∨ u) ∧ ¬ (x ∧ u)  ≈⟨  helper (x≈y ⟨ ∨-cong ⟩ u≈v)
                                    (x≈y ⟨ ∧-cong ⟩ u≈v) ⟩
    (y ∨ v) ∧ ¬ (y ∧ v)  ≈˘⟨ ⊕-def _ _ ⟩
    y ⊕ v                ∎

  ⊕-comm : Commutative _⊕_
  ⊕-comm x y = begin
    x ⊕ y                ≈⟨  ⊕-def _ _ ⟩
    (x ∨ y) ∧ ¬ (x ∧ y)  ≈⟨  helper (∨-comm _ _) (∧-comm _ _) ⟩
    (y ∨ x) ∧ ¬ (y ∧ x)  ≈˘⟨ ⊕-def _ _ ⟩
    y ⊕ x                ∎

  ¬-distribˡ-⊕ : ∀ x y → ¬ (x ⊕ y) ≈ ¬ x ⊕ y
  ¬-distribˡ-⊕ x y = begin
    ¬ (x ⊕ y)                              ≈⟨ ¬-cong $ ⊕-def _ _ ⟩
    ¬ ((x ∨ y) ∧ (¬ (x ∧ y)))              ≈⟨ ¬-cong (∧-∨-distribʳ _ _ _) ⟩
    ¬ ((x ∧ ¬ (x ∧ y)) ∨ (y ∧ ¬ (x ∧ y)))  ≈⟨ ¬-cong $ ∨-congˡ $ ∧-congˡ $ ¬-cong (∧-comm _ _) ⟩
    ¬ ((x ∧ ¬ (x ∧ y)) ∨ (y ∧ ¬ (y ∧ x)))  ≈⟨ ¬-cong $ lem _ _ ⟨ ∨-cong ⟩ lem _ _ ⟩
    ¬ ((x ∧ ¬ y) ∨ (y ∧ ¬ x))              ≈⟨ deMorgan₂ _ _ ⟩
    ¬ (x ∧ ¬ y) ∧ ¬ (y ∧ ¬ x)              ≈⟨ ∧-congʳ $ deMorgan₁ _ _ ⟩
    (¬ x ∨ (¬ ¬ y)) ∧ ¬ (y ∧ ¬ x)          ≈⟨ helper (∨-congˡ $ ¬-involutive _) (∧-comm _ _) ⟩
    (¬ x ∨ y) ∧ ¬ (¬ x ∧ y)                ≈˘⟨ ⊕-def _ _ ⟩
    ¬ x ⊕ y                                ∎
    where
    lem : ∀ x y → x ∧ ¬ (x ∧ y) ≈ x ∧ ¬ y
    lem x y = begin
      x ∧ ¬ (x ∧ y)          ≈⟨ ∧-congˡ $ deMorgan₁ _ _ ⟩
      x ∧ (¬ x ∨ ¬ y)        ≈⟨ ∧-∨-distribˡ _ _ _ ⟩
      (x ∧ ¬ x) ∨ (x ∧ ¬ y)  ≈⟨ ∨-congʳ $ ∧-complementʳ _ ⟩
      ⊥ ∨ (x ∧ ¬ y)          ≈⟨ ∨-identityˡ _ ⟩
      x ∧ ¬ y                ∎

  ¬-distribʳ-⊕ : ∀ x y → ¬ (x ⊕ y) ≈ x ⊕ ¬ y
  ¬-distribʳ-⊕ x y = begin
    ¬ (x ⊕ y)  ≈⟨ ¬-cong $ ⊕-comm _ _ ⟩
    ¬ (y ⊕ x)  ≈⟨ ¬-distribˡ-⊕ _ _ ⟩
    ¬ y ⊕ x    ≈⟨ ⊕-comm _ _ ⟩
    x ⊕ ¬ y    ∎

  ⊕-annihilates-¬ : ∀ x y → x ⊕ y ≈ ¬ x ⊕ ¬ y
  ⊕-annihilates-¬ x y = begin
    x ⊕ y        ≈˘⟨ ¬-involutive _ ⟩
    ¬ ¬ (x ⊕ y)  ≈⟨  ¬-cong $ ¬-distribˡ-⊕ _ _ ⟩
    ¬ (¬ x ⊕ y)  ≈⟨  ¬-distribʳ-⊕ _ _ ⟩
    ¬ x ⊕ ¬ y    ∎

  ⊕-identityˡ : LeftIdentity ⊥ _⊕_
  ⊕-identityˡ x = begin
    ⊥ ⊕ x                ≈⟨ ⊕-def _ _ ⟩
    (⊥ ∨ x) ∧ ¬ (⊥ ∧ x)  ≈⟨ helper (∨-identityˡ _) (∧-zeroˡ _) ⟩
    x ∧ ¬ ⊥              ≈⟨ ∧-congˡ ⊥≉⊤ ⟩
    x ∧ ⊤                ≈⟨ ∧-identityʳ _ ⟩
    x                    ∎

  ⊕-identityʳ : RightIdentity ⊥ _⊕_
  ⊕-identityʳ _ = ⊕-comm _ _ ⟨ trans ⟩ ⊕-identityˡ _

  ⊕-identity : Identity ⊥ _⊕_
  ⊕-identity = ⊕-identityˡ , ⊕-identityʳ

  ⊕-inverseˡ : LeftInverse ⊥ id _⊕_
  ⊕-inverseˡ x = begin
    x ⊕ x               ≈⟨ ⊕-def _ _ ⟩
    (x ∨ x) ∧ ¬ (x ∧ x) ≈⟨ helper (∨-idempotent _) (∧-idempotent _) ⟩
    x ∧ ¬ x             ≈⟨ ∧-complementʳ _ ⟩
    ⊥                   ∎

  ⊕-inverseʳ : RightInverse ⊥ id _⊕_
  ⊕-inverseʳ _ = ⊕-comm _ _ ⟨ trans ⟩ ⊕-inverseˡ _

  ⊕-inverse : Inverse ⊥ id _⊕_
  ⊕-inverse = ⊕-inverseˡ , ⊕-inverseʳ

  ∧-distribˡ-⊕ : _∧_ DistributesOverˡ _⊕_
  ∧-distribˡ-⊕ x y z = begin
    x ∧ (y ⊕ z)                ≈⟨ ∧-congˡ $ ⊕-def _ _ ⟩
    x ∧ ((y ∨ z) ∧ ¬ (y ∧ z))  ≈˘⟨ ∧-assoc _ _ _ ⟩
    (x ∧ (y ∨ z)) ∧ ¬ (y ∧ z)  ≈⟨ ∧-congˡ $ deMorgan₁ _ _ ⟩
    (x ∧ (y ∨ z)) ∧
    (¬ y ∨ ¬ z)                ≈˘⟨ ∨-identityˡ _ ⟩
    ⊥ ∨
    ((x ∧ (y ∨ z)) ∧
    (¬ y ∨ ¬ z))               ≈⟨ ∨-congʳ lem₃ ⟩
    ((x ∧ (y ∨ z)) ∧ ¬ x) ∨
    ((x ∧ (y ∨ z)) ∧
    (¬ y ∨ ¬ z))               ≈˘⟨ ∧-∨-distribˡ _ _ _ ⟩
    (x ∧ (y ∨ z)) ∧
    (¬ x ∨ (¬ y ∨ ¬ z))        ≈˘⟨ ∧-congˡ $ ∨-congˡ (deMorgan₁ _ _) ⟩
    (x ∧ (y ∨ z)) ∧
    (¬ x ∨ ¬ (y ∧ z))          ≈˘⟨ ∧-congˡ (deMorgan₁ _ _) ⟩
    (x ∧ (y ∨ z)) ∧
    ¬ (x ∧ (y ∧ z))            ≈⟨ helper refl lem₁ ⟩
    (x ∧ (y ∨ z)) ∧
    ¬ ((x ∧ y) ∧ (x ∧ z))      ≈⟨ ∧-congʳ $ ∧-∨-distribˡ _ _ _ ⟩
    ((x ∧ y) ∨ (x ∧ z)) ∧
    ¬ ((x ∧ y) ∧ (x ∧ z))      ≈˘⟨ ⊕-def _ _ ⟩
    (x ∧ y) ⊕ (x ∧ z)          ∎
      where
      lem₂ = begin
        x ∧ (y ∧ z)  ≈˘⟨ ∧-assoc _ _ _ ⟩
        (x ∧ y) ∧ z  ≈⟨ ∧-congʳ $ ∧-comm _ _ ⟩
        (y ∧ x) ∧ z  ≈⟨ ∧-assoc _ _ _ ⟩
        y ∧ (x ∧ z)  ∎

      lem₁ = begin
        x ∧ (y ∧ z)        ≈˘⟨ ∧-congʳ (∧-idempotent _) ⟩
        (x ∧ x) ∧ (y ∧ z)  ≈⟨ ∧-assoc _ _ _ ⟩
        x ∧ (x ∧ (y ∧ z))  ≈⟨ ∧-congˡ lem₂ ⟩
        x ∧ (y ∧ (x ∧ z))  ≈˘⟨ ∧-assoc _ _ _ ⟩
        (x ∧ y) ∧ (x ∧ z)  ∎

      lem₃ = begin
        ⊥                      ≈˘⟨ ∧-zeroʳ _ ⟩
        (y ∨ z) ∧ ⊥            ≈˘⟨ ∧-congˡ (∧-complementʳ _) ⟩
        (y ∨ z) ∧ (x ∧ ¬ x)    ≈˘⟨ ∧-assoc _ _ _ ⟩
        ((y ∨ z) ∧ x) ∧ ¬ x    ≈⟨ ∧-comm _ _ ⟨ ∧-cong ⟩ refl  ⟩
        (x ∧ (y ∨ z)) ∧ ¬ x    ∎

  ∧-distribʳ-⊕ : _∧_ DistributesOverʳ _⊕_
  ∧-distribʳ-⊕ = comm+distrˡ⇒distrʳ ⊕-cong ∧-comm ∧-distribˡ-⊕

  ∧-distrib-⊕ : _∧_ DistributesOver _⊕_
  ∧-distrib-⊕ = ∧-distribˡ-⊕ , ∧-distribʳ-⊕

  private

    lemma₂ : ∀ x y u v →
             (x ∧ y) ∨ (u ∧ v) ≈
             ((x ∨ u) ∧ (y ∨ u)) ∧
             ((x ∨ v) ∧ (y ∨ v))
    lemma₂ x y u v = begin
        (x ∧ y) ∨ (u ∧ v)              ≈⟨ ∨-∧-distribˡ _ _ _ ⟩
        ((x ∧ y) ∨ u) ∧ ((x ∧ y) ∨ v)  ≈⟨ ∨-∧-distribʳ _ _ _
                                            ⟨ ∧-cong ⟩
                                          ∨-∧-distribʳ _ _ _ ⟩
        ((x ∨ u) ∧ (y ∨ u)) ∧
        ((x ∨ v) ∧ (y ∨ v))            ∎

  ⊕-assoc : Associative _⊕_
  ⊕-assoc x y z = sym $ begin
    x ⊕ (y ⊕ z)                                ≈⟨ refl ⟨ ⊕-cong ⟩ ⊕-def _ _ ⟩
    x ⊕ ((y ∨ z) ∧ ¬ (y ∧ z))                  ≈⟨ ⊕-def _ _ ⟩
      (x ∨ ((y ∨ z) ∧ ¬ (y ∧ z))) ∧
    ¬ (x ∧ ((y ∨ z) ∧ ¬ (y ∧ z)))              ≈⟨ lem₃ ⟨ ∧-cong ⟩ lem₄ ⟩
    (((x ∨ y) ∨ z) ∧ ((x ∨ ¬ y) ∨ ¬ z)) ∧
    (((¬ x ∨ ¬ y) ∨ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ≈⟨ ∧-assoc _ _ _ ⟩
    ((x ∨ y) ∨ z) ∧
    (((x ∨ ¬ y) ∨ ¬ z) ∧
     (((¬ x ∨ ¬ y) ∨ z) ∧ ((¬ x ∨ y) ∨ ¬ z)))  ≈⟨ ∧-congˡ lem₅ ⟩
    ((x ∨ y) ∨ z) ∧
    (((¬ x ∨ ¬ y) ∨ z) ∧
     (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z)))  ≈˘⟨ ∧-assoc _ _ _ ⟩
    (((x ∨ y) ∨ z) ∧ ((¬ x ∨ ¬ y) ∨ z)) ∧
    (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ≈⟨ lem₁ ⟨ ∧-cong ⟩ lem₂ ⟩
      (((x ∨ y) ∧ ¬ (x ∧ y)) ∨ z) ∧
    ¬ (((x ∨ y) ∧ ¬ (x ∧ y)) ∧ z)              ≈˘⟨ ⊕-def _ _ ⟩
    ((x ∨ y) ∧ ¬ (x ∧ y)) ⊕ z                  ≈˘⟨ ⊕-def _ _ ⟨ ⊕-cong ⟩ refl ⟩
    (x ⊕ y) ⊕ z                                ∎
    where
    lem₁ = begin
      ((x ∨ y) ∨ z) ∧ ((¬ x ∨ ¬ y) ∨ z)  ≈˘⟨ ∨-∧-distribʳ _ _ _ ⟩
      ((x ∨ y) ∧ (¬ x ∨ ¬ y)) ∨ z        ≈˘⟨ ∨-congʳ $ ∧-congˡ (deMorgan₁ _ _) ⟩
      ((x ∨ y) ∧ ¬ (x ∧ y)) ∨ z          ∎

    lem₂' = begin
      (x ∨ ¬ y) ∧ (¬ x ∨ y)              ≈˘⟨ ∧-identityˡ _ ⟨ ∧-cong ⟩ ∧-identityʳ _ ⟩
      (⊤ ∧ (x ∨ ¬ y)) ∧ ((¬ x ∨ y) ∧ ⊤)  ≈˘⟨  (∨-complementˡ _ ⟨ ∧-cong ⟩ ∨-comm _ _)
                                                ⟨ ∧-cong ⟩
                                              (∧-congˡ $ ∨-complementˡ _) ⟩
      ((¬ x ∨ x) ∧ (¬ y ∨ x)) ∧
      ((¬ x ∨ y) ∧ (¬ y ∨ y))            ≈˘⟨ lemma₂ _ _ _ _ ⟩
      (¬ x ∧ ¬ y) ∨ (x ∧ y)              ≈˘⟨ deMorgan₂ _ _ ⟨ ∨-cong ⟩ ¬-involutive _ ⟩
      ¬ (x ∨ y) ∨ ¬ ¬ (x ∧ y)            ≈˘⟨ deMorgan₁ _ _ ⟩
      ¬ ((x ∨ y) ∧ ¬ (x ∧ y))            ∎

    lem₂ = begin
      ((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z)  ≈˘⟨ ∨-∧-distribʳ _ _ _ ⟩
      ((x ∨ ¬ y) ∧ (¬ x ∨ y)) ∨ ¬ z          ≈⟨ ∨-congʳ lem₂' ⟩
      ¬ ((x ∨ y) ∧ ¬ (x ∧ y)) ∨ ¬ z          ≈˘⟨ deMorgan₁ _ _ ⟩
      ¬ (((x ∨ y) ∧ ¬ (x ∧ y)) ∧ z)          ∎

    lem₃ = begin
      x ∨ ((y ∨ z) ∧ ¬ (y ∧ z))          ≈⟨ ∨-congˡ $ ∧-congˡ $ deMorgan₁ _ _ ⟩
      x ∨ ((y ∨ z) ∧ (¬ y ∨ ¬ z))        ≈⟨ ∨-∧-distribˡ _ _ _ ⟩
      (x ∨ (y ∨ z)) ∧ (x ∨ (¬ y ∨ ¬ z))  ≈˘⟨ ∨-assoc _ _ _ ⟨ ∧-cong ⟩ ∨-assoc _ _ _ ⟩
      ((x ∨ y) ∨ z) ∧ ((x ∨ ¬ y) ∨ ¬ z)  ∎

    lem₄' = begin
      ¬ ((y ∨ z) ∧ ¬ (y ∧ z))    ≈⟨ deMorgan₁ _ _ ⟩
      ¬ (y ∨ z) ∨ ¬ ¬ (y ∧ z)    ≈⟨ deMorgan₂ _ _ ⟨ ∨-cong ⟩ ¬-involutive _ ⟩
      (¬ y ∧ ¬ z) ∨ (y ∧ z)      ≈⟨ lemma₂ _ _ _ _ ⟩
      ((¬ y ∨ y) ∧ (¬ z ∨ y)) ∧
      ((¬ y ∨ z) ∧ (¬ z ∨ z))    ≈⟨ (∨-complementˡ _ ⟨ ∧-cong ⟩ ∨-comm _ _)
                                      ⟨ ∧-cong ⟩
                                   (∧-congˡ $ ∨-complementˡ _) ⟩
      (⊤ ∧ (y ∨ ¬ z)) ∧
      ((¬ y ∨ z) ∧ ⊤)            ≈⟨ ∧-identityˡ _ ⟨ ∧-cong ⟩ ∧-identityʳ _ ⟩
      (y ∨ ¬ z) ∧ (¬ y ∨ z)      ∎

    lem₄ = begin
      ¬ (x ∧ ((y ∨ z) ∧ ¬ (y ∧ z)))  ≈⟨ deMorgan₁ _ _ ⟩
      ¬ x ∨ ¬ ((y ∨ z) ∧ ¬ (y ∧ z))  ≈⟨ ∨-congˡ lem₄' ⟩
      ¬ x ∨ ((y ∨ ¬ z) ∧ (¬ y ∨ z))  ≈⟨ ∨-∧-distribˡ _ _ _ ⟩
      (¬ x ∨ (y     ∨ ¬ z)) ∧
      (¬ x ∨ (¬ y ∨ z))              ≈˘⟨ ∨-assoc _ _ _ ⟨ ∧-cong ⟩ ∨-assoc _ _ _ ⟩
      ((¬ x ∨ y)     ∨ ¬ z) ∧
      ((¬ x ∨ ¬ y) ∨ z)              ≈⟨ ∧-comm _ _ ⟩
      ((¬ x ∨ ¬ y) ∨ z) ∧
      ((¬ x ∨ y)     ∨ ¬ z)          ∎

    lem₅ = begin
      ((x ∨ ¬ y) ∨ ¬ z) ∧
      (((¬ x ∨ ¬ y) ∨ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ≈˘⟨ ∧-assoc _ _ _ ⟩
      (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ ¬ y) ∨ z)) ∧
      ((¬ x ∨ y) ∨ ¬ z)                          ≈⟨ ∧-congʳ $ ∧-comm _ _ ⟩
      (((¬ x ∨ ¬ y) ∨ z) ∧ ((x ∨ ¬ y) ∨ ¬ z)) ∧
      ((¬ x ∨ y) ∨ ¬ z)                          ≈⟨ ∧-assoc _ _ _ ⟩
      ((¬ x ∨ ¬ y) ∨ z) ∧
      (((x ∨ ¬ y) ∨ ¬ z) ∧ ((¬ x ∨ y) ∨ ¬ z))    ∎

  ⊕-isMagma : IsMagma _⊕_
  ⊕-isMagma = record
    { isEquivalence = isEquivalence
    ; ∙-cong        = ⊕-cong
    }

  ⊕-isSemigroup : IsSemigroup _⊕_
  ⊕-isSemigroup = record
    { isMagma = ⊕-isMagma
    ; assoc   = ⊕-assoc
    }

  ⊕-⊥-isMonoid : IsMonoid _⊕_ ⊥
  ⊕-⊥-isMonoid = record
    { isSemigroup = ⊕-isSemigroup
    ; identity    = ⊕-identity
    }

  ⊕-⊥-isGroup : IsGroup _⊕_ ⊥ id
  ⊕-⊥-isGroup = record
    { isMonoid = ⊕-⊥-isMonoid
    ; inverse  = ⊕-inverse
    ; ⁻¹-cong  = id
    }

  ⊕-⊥-isAbelianGroup : IsAbelianGroup _⊕_ ⊥ id
  ⊕-⊥-isAbelianGroup = record
    { isGroup = ⊕-⊥-isGroup
    ; comm    = ⊕-comm
    }

  ⊕-∧-isRing : IsRing _⊕_ _∧_ id ⊥ ⊤
  ⊕-∧-isRing = record
    { +-isAbelianGroup = ⊕-⊥-isAbelianGroup
    ; *-isMonoid = ∧-⊤-isMonoid
    ; distrib = ∧-distrib-⊕
    }

  ⊕-∧-isCommutativeRing : IsCommutativeRing _⊕_ _∧_ id ⊥ ⊤
  ⊕-∧-isCommutativeRing = record
    { isRing = ⊕-∧-isRing
    ; *-comm = ∧-comm
    }

  ⊕-∧-commutativeRing : CommutativeRing _ _
  ⊕-∧-commutativeRing = record
    { isCommutativeRing = ⊕-∧-isCommutativeRing
    }

  ⊕-¬-distribˡ = ¬-distribˡ-⊕
  {-# WARNING_ON_USAGE ⊕-¬-distribˡ
  "Warning: ⊕-¬-distribˡ was deprecated in v1.1.
  Please use ¬-distribˡ-⊕ instead."
  #-}
  ⊕-¬-distribʳ = ¬-distribʳ-⊕
  {-# WARNING_ON_USAGE ⊕-¬-distribʳ
  "Warning: ⊕-¬-distribʳ was deprecated in v1.1.
  Please use ¬-distribʳ-⊕ instead."
  #-}
  isCommutativeRing = ⊕-∧-isCommutativeRing
  {-# WARNING_ON_USAGE isCommutativeRing
  "Warning: isCommutativeRing was deprecated in v1.1.
  Please use ⊕-∧-isCommutativeRing instead."
  #-}
  commutativeRing = ⊕-∧-commutativeRing
  {-# WARNING_ON_USAGE commutativeRing
  "Warning: commutativeRing was deprecated in v1.1.
  Please use ⊕-∧-commutativeRing instead."
  #-}


infixl 6 _⊕_

_⊕_ : Op₂ Carrier
x ⊕ y = (x ∨ y) ∧ ¬ (x ∧ y)

module DefaultXorRing = XorRing _⊕_ (λ _ _ → refl)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

¬⊥=⊤ = ⊥≉⊤
{-# WARNING_ON_USAGE ¬⊥=⊤
"Warning: ¬⊥=⊤ was deprecated in v1.1.
Please use ⊥≉⊤ instead."
#-}
¬⊤=⊥ = ⊤≉⊥
{-# WARNING_ON_USAGE ¬⊤=⊥
"Warning: ¬⊤=⊥ was deprecated in v1.1.
Please use ⊤≉⊥ instead."
#-}
