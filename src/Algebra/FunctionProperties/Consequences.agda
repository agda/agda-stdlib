------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of functions, such as associativity and
-- commutativity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; Setoid; Substitutive; Symmetric; Total)

module Algebra.FunctionProperties.Consequences
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

open import Algebra.FunctionProperties _≈_
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
import Relation.Binary.Consequences as Bin
open import Relation.Binary.Reasoning.Equational S
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Magma-like structures

module _ {_•_ : Op₂ A} (comm : Commutative _•_) where

  comm+cancelˡ⇒cancelʳ : LeftCancellative _•_ →  RightCancellative _•_
  comm+cancelˡ⇒cancelʳ cancelˡ {x} y z eq = cancelˡ x (begin
    x • y ≈⟨ comm x y ⟩
    y • x ≈⟨ eq ⟩
    z • x ≈⟨ comm z x ⟩
    x • z ∎)

  comm+cancelʳ⇒cancelˡ : RightCancellative _•_ → LeftCancellative _•_
  comm+cancelʳ⇒cancelˡ cancelʳ x {y} {z} eq = cancelʳ y z (begin
    y • x ≈⟨ comm y x ⟩
    x • y ≈⟨ eq ⟩
    x • z ≈⟨ comm x z ⟩
    z • x ∎)

------------------------------------------------------------------------
-- Monoid-like structures

module _ {_•_ : Op₂ A} (comm : Commutative _•_) {e : A} where

  comm+idˡ⇒idʳ : LeftIdentity e _•_ → RightIdentity e _•_
  comm+idˡ⇒idʳ idˡ x = begin
    x • e ≈⟨ comm x e ⟩
    e • x ≈⟨ idˡ x ⟩
    x     ∎

  comm+idʳ⇒idˡ : RightIdentity e _•_ → LeftIdentity e _•_
  comm+idʳ⇒idˡ idʳ x = begin
    e • x ≈⟨ comm e x ⟩
    x • e ≈⟨ idʳ x ⟩
    x     ∎

  comm+zeˡ⇒zeʳ : LeftZero e _•_ → RightZero e _•_
  comm+zeˡ⇒zeʳ zeˡ x = begin
    x • e ≈⟨ comm x e ⟩
    e • x ≈⟨ zeˡ x ⟩
    e     ∎

  comm+zeʳ⇒zeˡ : RightZero e _•_ → LeftZero e _•_
  comm+zeʳ⇒zeˡ zeʳ x = begin
    e • x ≈⟨ comm e x ⟩
    x • e ≈⟨ zeʳ x ⟩
    e     ∎

------------------------------------------------------------------------
-- Group-like structures

module _ {_•_ : Op₂ A} {_⁻¹ : Op₁ A} {e} (comm : Commutative _•_) where

  comm+invˡ⇒invʳ : LeftInverse e _⁻¹ _•_ → RightInverse e _⁻¹ _•_
  comm+invˡ⇒invʳ invˡ x = begin
    x • (x ⁻¹) ≈⟨ comm x (x ⁻¹) ⟩
    (x ⁻¹) • x ≈⟨ invˡ x ⟩
    e          ∎

  comm+invʳ⇒invˡ : RightInverse e _⁻¹ _•_ → LeftInverse e _⁻¹ _•_
  comm+invʳ⇒invˡ invʳ x = begin
    (x ⁻¹) • x ≈⟨ comm (x ⁻¹) x ⟩
    x • (x ⁻¹) ≈⟨ invʳ x ⟩
    e          ∎

module _ {_•_ : Op₂ A} {_⁻¹ : Op₁ A} {e} (cong : Congruent₂ _•_) where

  assoc+id+invʳ⇒invˡ-unique : Associative _•_ →
                              Identity e _•_ → RightInverse e _⁻¹ _•_ →
                              ∀ x y → (x • y) ≈ e → x ≈ (y ⁻¹)
  assoc+id+invʳ⇒invˡ-unique assoc (idˡ , idʳ) invʳ x y eq = begin
    x                ≈⟨ sym (idʳ x) ⟩
    x • e            ≈⟨ cong refl (sym (invʳ y)) ⟩
    x • (y • (y ⁻¹)) ≈⟨ sym (assoc x y (y ⁻¹)) ⟩
    (x • y) • (y ⁻¹) ≈⟨ cong eq refl ⟩
    e • (y ⁻¹)       ≈⟨ idˡ (y ⁻¹) ⟩
    y ⁻¹             ∎

  assoc+id+invˡ⇒invʳ-unique : Associative _•_ →
                              Identity e _•_ → LeftInverse e _⁻¹ _•_ →
                              ∀ x y → (x • y) ≈ e → y ≈ (x ⁻¹)
  assoc+id+invˡ⇒invʳ-unique assoc (idˡ , idʳ) invˡ x y eq = begin
    y                ≈⟨ sym (idˡ y) ⟩
    e • y            ≈⟨ cong (sym (invˡ x)) refl ⟩
    ((x ⁻¹) • x) • y ≈⟨ assoc (x ⁻¹) x y ⟩
    (x ⁻¹) • (x • y) ≈⟨ cong refl eq ⟩
    (x ⁻¹) • e       ≈⟨ idʳ (x ⁻¹) ⟩
    x ⁻¹             ∎

----------------------------------------------------------------------
-- Bisemigroup-like structures

module _ {_•_ _◦_ : Op₂ A}
         (◦-cong : Congruent₂ _◦_)
         (•-comm : Commutative _•_)
         where

  comm+distrˡ⇒distrʳ :  _•_ DistributesOverˡ _◦_ → _•_ DistributesOverʳ _◦_
  comm+distrˡ⇒distrʳ distrˡ x y z = begin
    (y ◦ z) • x       ≈⟨ •-comm (y ◦ z) x ⟩
    x • (y ◦ z)       ≈⟨ distrˡ x y z ⟩
    (x • y) ◦ (x • z) ≈⟨ ◦-cong (•-comm x y) (•-comm x z) ⟩
    (y • x) ◦ (z • x) ∎

  comm+distrʳ⇒distrˡ : _•_ DistributesOverʳ _◦_ → _•_ DistributesOverˡ _◦_
  comm+distrʳ⇒distrˡ distrˡ x y z = begin
    x • (y ◦ z)       ≈⟨ •-comm x (y ◦ z) ⟩
    (y ◦ z) • x       ≈⟨ distrˡ x y z ⟩
    (y • x) ◦ (z • x) ≈⟨ ◦-cong (•-comm y x) (•-comm z x) ⟩
    (x • y) ◦ (x • z) ∎

  comm⇒sym[distribˡ] : ∀ x → Symmetric (λ y z → (x ◦ (y • z)) ≈ ((x ◦ y) • (x ◦ z)))
  comm⇒sym[distribˡ] x {y} {z} prf = begin
    x ◦ (z • y)       ≈⟨ ◦-cong refl (•-comm z y) ⟩
    x ◦ (y • z)       ≈⟨ prf ⟩
    (x ◦ y) • (x ◦ z) ≈⟨ •-comm (x ◦ y) (x ◦ z) ⟩
    (x ◦ z) • (x ◦ y) ∎

----------------------------------------------------------------------
-- Ring-like structures

module _ {_+_ _*_ : Op₂ A}
         {_⁻¹ : Op₁ A} {0# : A}
         (+-cong : Congruent₂ _+_)
         (*-cong : Congruent₂ _*_)
         where

  assoc+distribʳ+idʳ+invʳ⇒zeˡ : Associative _+_ → _*_ DistributesOverʳ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# _⁻¹ _+_ →
                                LeftZero 0# _*_
  assoc+distribʳ+idʳ+invʳ⇒zeˡ +-assoc distribʳ idʳ invʳ  x = begin
    0# * x                                 ≈⟨ sym (idʳ _) ⟩
    (0# * x) + 0#                          ≈⟨ +-cong refl (sym (invʳ _)) ⟩
    (0# * x) + ((0# * x)  + ((0# * x)⁻¹))  ≈⟨ sym (+-assoc _ _ _) ⟩
    ((0# * x) +  (0# * x)) + ((0# * x)⁻¹)  ≈⟨ +-cong (sym (distribʳ _ _ _)) refl ⟩
    ((0# + 0#) * x) + ((0# * x)⁻¹)         ≈⟨ +-cong (*-cong (idʳ _) refl) refl ⟩
    (0# * x) + ((0# * x)⁻¹)                ≈⟨ invʳ _ ⟩
    0#                                     ∎

  assoc+distribˡ+idʳ+invʳ⇒zeʳ : Associative _+_ → _*_ DistributesOverˡ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# _⁻¹ _+_ →
                                RightZero 0# _*_
  assoc+distribˡ+idʳ+invʳ⇒zeʳ +-assoc distribˡ idʳ invʳ  x = begin
     x * 0#                                ≈⟨ sym (idʳ _) ⟩
     (x * 0#) + 0#                         ≈⟨ +-cong refl (sym (invʳ _)) ⟩
     (x * 0#) + ((x * 0#) + ((x * 0#)⁻¹))  ≈⟨ sym (+-assoc _ _ _) ⟩
     ((x * 0#) + (x * 0#)) + ((x * 0#)⁻¹)  ≈⟨ +-cong (sym (distribˡ _ _ _)) refl ⟩
     (x * (0# + 0#)) + ((x * 0#)⁻¹)        ≈⟨ +-cong (*-cong refl (idʳ _)) refl ⟩
     ((x * 0#) + ((x * 0#)⁻¹))             ≈⟨ invʳ _ ⟩
     0#                                    ∎

------------------------------------------------------------------------
-- Without Loss of Generality

module _ {p} {f : Op₂ A} {P : Pred A p}
         (≈-subst : Substitutive _≈_ p)
         (comm : Commutative f)
         where

  subst+comm⇒sym : Symmetric (λ a b → P (f a b))
  subst+comm⇒sym = ≈-subst P (comm _ _)

  wlog : ∀ {r} {_R_ : Rel _ r} → Total _R_ →
         (∀ a b → a R b → P (f a b)) →
         ∀ a b → P (f a b)
  wlog r-total = Bin.wlog r-total subst+comm⇒sym
