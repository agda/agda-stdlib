------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of functions, such as associativity and
-- commutativity, parameterized over a partial setoid.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
open import Relation.Binary.Partial

module Algebra.Partial.FunctionProperties.Consequences
  {a ℓ} {A : Set a} (S : PartialSetoid A ℓ) where

open PartialSetoid S

open import Algebra.Partial.FunctionProperties _≈_
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.Reasoning.PartialSetoid S

------------------------------------------------------------------------
-- Magma-like structures

module _ {_•_ : Op₂ A} (cong : Congruent₂ _•_) (comm : Commutative _•_) where

  comm+cancelˡ⇒cancelʳ : LeftCancellative _•_ → RightCancellative _•_
  comm+cancelˡ⇒cancelʳ cancelˡ {x} {y} {z} x≈x y≈y z≈z eq = cancelˡ x≈x y≈y z≈z (begin
    x • y ≈⟨ comm (x≈x) (y≈y) ⟩
    y • x ≈⟨ eq ⟩
    z • x ≈⟨ comm (z≈z) (x≈x) ⟩
    x • z ∎⟨ cong x≈x z≈z ⟩)

  comm+cancelʳ⇒cancelˡ : RightCancellative _•_ → LeftCancellative _•_
  comm+cancelʳ⇒cancelˡ cancelʳ {x} {y} {z} x≈x y≈y z≈z eq = cancelʳ x≈x y≈y z≈z (begin
    y • x ≈⟨ comm y≈y x≈x ⟩
    x • y ≈⟨ eq ⟩
    x • z ≈⟨ comm x≈x z≈z ⟩
    z • x ∎⟨ cong z≈z x≈x ⟩)

------------------------------------------------------------------------
-- Semigroup-like structures


------------------------------------------------------------------------
-- Monoid-like structures

module _ {_•_ : Op₂ A} (comm : Commutative _•_) {e : A} where

  comm+idˡ⇒idʳ : LeftIdentity e _•_ → RightIdentity e _•_
  comm+idˡ⇒idʳ idˡ {x} e≈e x≈x = begin
    x • e ≈⟨ comm x≈x e≈e ⟩
    e • x ≈⟨ idˡ e≈e x≈x ⟩
    x     ∎⟨ x≈x ⟩

  comm+idʳ⇒idˡ : RightIdentity e _•_ → LeftIdentity e _•_
  comm+idʳ⇒idˡ idʳ {x} e≈e x≈x = begin
    e • x ≈⟨ comm e≈e x≈x ⟩
    x • e ≈⟨ idʳ e≈e x≈x ⟩
    x     ∎⟨ x≈x ⟩

  comm+zeˡ⇒zeʳ : LeftZero e _•_ → RightZero e _•_
  comm+zeˡ⇒zeʳ zeˡ {x} e≈e x≈x = begin
    x • e ≈⟨ comm x≈x e≈e ⟩
    e • x ≈⟨ zeˡ e≈e x≈x ⟩
    e   ∎⟨ e≈e ⟩

  comm+zeʳ⇒zeˡ : RightZero e _•_ → LeftZero e _•_
  comm+zeʳ⇒zeˡ zeʳ {x} e≈e x≈x = begin
    e • x ≈⟨ comm e≈e x≈x ⟩
    x • e ≈⟨ zeʳ e≈e x≈x ⟩
    e     ∎⟨ e≈e ⟩

------------------------------------------------------------------------
-- Group-like structures

module _ {_•_ : Op₂ A} {_⁻¹ : Op₁ A} {e} (⁻¹-cong : Congruent₁ _⁻¹) (comm : Commutative _•_) where

  comm+invˡ⇒invʳ : LeftInverse e _⁻¹ _•_ → RightInverse e _⁻¹ _•_
  comm+invˡ⇒invʳ invˡ {x} e≈e x≈x = begin
    x • (x ⁻¹) ≈⟨ comm x≈x (⁻¹-cong x≈x) ⟩
    (x ⁻¹) • x ≈⟨ invˡ e≈e x≈x ⟩
    e          ∎⟨ e≈e ⟩

  comm+invʳ⇒invˡ : RightInverse e _⁻¹ _•_ → LeftInverse e _⁻¹ _•_
  comm+invʳ⇒invˡ invʳ {x} e≈e x≈x = begin
    (x ⁻¹) • x ≈⟨ comm (⁻¹-cong x≈x) x≈x ⟩
    x • (x ⁻¹) ≈⟨ invʳ e≈e x≈x ⟩
    e          ∎⟨ e≈e ⟩

module _ {_•_ : Op₂ A} {_⁻¹ : Op₁ A} {e} (⁻¹-cong : Congruent₁ _⁻¹) (•-cong : Congruent₂ _•_) where

  assoc+id+invʳ⇒invˡ-unique : Associative _•_ →
                              Identity e _•_ → RightInverse e _⁻¹ _•_ →
                              ∀ {x y} → (e ≈ e) → (x ≈ x) → (y ≈ y) → (x • y) ≈ e → x ≈ (y ⁻¹)
  assoc+id+invʳ⇒invˡ-unique assoc (idˡ , idʳ) invʳ {x} {y} e≈e x≈x y≈y eq = begin
    x                ≈⟨ sym (idʳ e≈e x≈x) ⟩
    x • e            ≈⟨ •-cong x≈x (sym (invʳ e≈e y≈y)) ⟩
    x • (y • (y ⁻¹)) ≈⟨ sym (assoc x≈x y≈y (⁻¹-cong y≈y)) ⟩
    (x • y) • (y ⁻¹) ≈⟨ •-cong eq (⁻¹-cong y≈y) ⟩
    e • (y ⁻¹)       ≈⟨ idˡ e≈e (⁻¹-cong y≈y) ⟩
    y ⁻¹             ∎⟨ ⁻¹-cong y≈y ⟩



  assoc+id+invˡ⇒invʳ-unique : Associative _•_ →
                              Identity e _•_ → LeftInverse e _⁻¹ _•_ →
                              ∀ {x y} → (e ≈ e) → (x ≈ x) → (y ≈ y) → (x • y) ≈ e → y ≈ (x ⁻¹)
  assoc+id+invˡ⇒invʳ-unique assoc (idˡ , idʳ) invˡ {x} {y} e≈e x≈x y≈y eq = begin
    y                ≈⟨ sym (idˡ e≈e y≈y) ⟩
    e • y            ≈⟨ •-cong (sym (invˡ e≈e x≈x)) y≈y ⟩
    ((x ⁻¹) • x) • y ≈⟨ assoc (⁻¹-cong x≈x) x≈x y≈y ⟩
    (x ⁻¹) • (x • y) ≈⟨ •-cong (⁻¹-cong x≈x) eq ⟩
    (x ⁻¹) • e       ≈⟨ idʳ e≈e (⁻¹-cong x≈x) ⟩
    x ⁻¹             ∎⟨ ⁻¹-cong x≈x ⟩

----------------------------------------------------------------------
-- Bisemigroup-like structures

module _ {_•_ _◦_ : Op₂ A}
         (◦-cong : Congruent₂ _◦_)
         (•-cong : Congruent₂ _•_)
         (•-comm : Commutative _•_)
         where

  comm+distrˡ⇒distrʳ :  _•_ DistributesOverˡ _◦_ → _•_ DistributesOverʳ _◦_
  comm+distrˡ⇒distrʳ distrˡ {x} {y} {z} x≈x y≈y z≈z = begin
    (y ◦ z) • x       ≈⟨ •-comm (◦-cong y≈y z≈z) x≈x ⟩
    x • (y ◦ z)       ≈⟨ distrˡ x≈x y≈y z≈z ⟩
    (x • y) ◦ (x • z) ≈⟨ ◦-cong (•-comm x≈x y≈y) (•-comm x≈x z≈z) ⟩
    (y • x) ◦ (z • x) ∎⟨ ◦-cong (•-cong y≈y x≈x) (•-cong z≈z x≈x) ⟩

  comm+distrʳ⇒distrˡ : _•_ DistributesOverʳ _◦_ → _•_ DistributesOverˡ _◦_
  comm+distrʳ⇒distrˡ distrˡ {x} {y} {z} x≈x y≈y z≈z = begin
    x • (y ◦ z)       ≈⟨ •-comm x≈x (◦-cong y≈y z≈z) ⟩
    (y ◦ z) • x       ≈⟨ distrˡ x≈x y≈y z≈z ⟩
    (y • x) ◦ (z • x) ≈⟨ ◦-cong (•-comm y≈y x≈x) (•-comm z≈z x≈x) ⟩
    (x • y) ◦ (x • z) ∎⟨ ◦-cong (•-cong x≈x y≈y) (•-cong x≈x z≈z) ⟩

  -- TODO: Implement Symmetric in Relation.Binary.PartialEquivalence
  -- comm⇒sym[distribˡ] : ∀ x → Symmetric (λ y z → (x ◦ (y • z)) ≈ ((x ◦ y) • (x ◦ z)))
  -- comm⇒sym[distribˡ] x {y} {z} prf = begin
  --   x ◦ (z • y)       ≈⟨ ◦-cong refl (•-comm z y) ⟩
  --   x ◦ (y • z)       ≈⟨ prf ⟩
  --   (x ◦ y) • (x ◦ z) ≈⟨ •-comm (x ◦ y) (x ◦ z) ⟩
  --   (x ◦ z) • (x ◦ y) ∎

----------------------------------------------------------------------
-- Ring-like structures

module _ {_+_ _*_ : Op₂ A}
         {_⁻¹ : Op₁ A} {0# : A}
         (⁻¹-cong : Congruent₁ _⁻¹)
         (+-cong : Congruent₂ _+_)
         (*-cong : Congruent₂ _*_)
         where

  assoc+distribʳ+idʳ+invʳ⇒zeˡ : Associative _+_ → _*_ DistributesOverʳ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# _⁻¹ _+_ →
                                LeftZero 0# _*_
  assoc+distribʳ+idʳ+invʳ⇒zeˡ +-assoc distribʳ idʳ invʳ {x} 0#≈0# x≈x = begin
    0# * x                                 ≈⟨ sym (idʳ 0#≈0# (*-cong 0#≈0# x≈x)) ⟩
    (0# * x) + 0#                          ≈⟨ +-cong (*-cong 0#≈0# x≈x) (sym (invʳ 0#≈0# (*-cong 0#≈0# x≈x))) ⟩
    (0# * x) + ((0# * x)  + ((0# * x)⁻¹))  ≈⟨ sym (+-assoc (*-cong 0#≈0# x≈x) (*-cong 0#≈0# x≈x) (⁻¹-cong (*-cong 0#≈0# x≈x))) ⟩
    ((0# * x) +  (0# * x)) + ((0# * x)⁻¹)  ≈⟨ +-cong (sym (distribʳ x≈x 0#≈0# 0#≈0#)) (⁻¹-cong (*-cong 0#≈0# x≈x)) ⟩
    ((0# + 0#) * x) + ((0# * x)⁻¹)         ≈⟨ +-cong (*-cong (idʳ 0#≈0# 0#≈0#) x≈x) (⁻¹-cong (*-cong 0#≈0# x≈x)) ⟩
    (0# * x) + ((0# * x)⁻¹)                ≈⟨ invʳ 0#≈0# (*-cong 0#≈0# x≈x) ⟩
    0#                                     ∎⟨ 0#≈0# ⟩

  assoc+distribˡ+idʳ+invʳ⇒zeʳ : Associative _+_ → _*_ DistributesOverˡ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# _⁻¹ _+_ →
                                RightZero 0# _*_
  assoc+distribˡ+idʳ+invʳ⇒zeʳ +-assoc distribˡ idʳ invʳ {x} 0#≈0# x≈x = begin
     x * 0#                                ≈⟨ sym (idʳ 0#≈0# (*-cong x≈x 0#≈0#)) ⟩
     (x * 0#) + 0#                         ≈⟨ +-cong (*-cong x≈x 0#≈0#) (sym (invʳ 0#≈0# (*-cong x≈x 0#≈0#))) ⟩
     (x * 0#) + ((x * 0#) + ((x * 0#)⁻¹))  ≈⟨ sym (+-assoc (*-cong x≈x 0#≈0#) (*-cong x≈x 0#≈0#) (⁻¹-cong (*-cong x≈x 0#≈0#))) ⟩
     ((x * 0#) + (x * 0#)) + ((x * 0#)⁻¹)  ≈⟨ +-cong (sym (distribˡ x≈x 0#≈0# 0#≈0#)) (⁻¹-cong (*-cong x≈x 0#≈0#)) ⟩
     (x * (0# + 0#)) + ((x * 0#)⁻¹)        ≈⟨ +-cong (*-cong x≈x (idʳ 0#≈0# 0#≈0#)) (⁻¹-cong (*-cong x≈x 0#≈0#)) ⟩
     ((x * 0#) + ((x * 0#)⁻¹))             ≈⟨ invʳ 0#≈0# (*-cong x≈x 0#≈0#) ⟩
     0#                                    ∎⟨ 0#≈0# ⟩

-- TODO: Implement this
-- ------------------------------------------------------------------------
-- -- Without Loss of Generality

-- module _ {p} {f : Op₂ A} {P : Pred A p}
--          (≈-subst : Substitutive _≈_ p)
--          (comm : Commutative f)
--          where

--   subst+comm⇒sym : Symmetric (λ a b → P (f a b))
--   subst+comm⇒sym = ≈-subst P (comm _ _)

--   wlog : ∀ {r} {_R_ : Rel _ r} → Total _R_ →
--          (∀ a b → a R b → P (f a b)) →
--          ∀ a b → P (f a b)
--   wlog r-total = Bin.wlog r-total subst+comm⇒sym
