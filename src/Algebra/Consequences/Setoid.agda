------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of functions, such as associativity and
-- commutativity, when the underlying relation is a setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions
  using (Substitutive; Symmetric; Total)

module Algebra.Consequences.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)
open import Algebra.Core
open import Algebra.Definitions _≈_
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Function.Base using (_$_; id; _∘_)
open import Function.Definitions
import Relation.Binary.Consequences as Bin
open import Relation.Binary.Reasoning.Setoid S
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Re-exports

-- Export base lemmas that don't require the setoid

open import Algebra.Consequences.Base public

------------------------------------------------------------------------
-- MiddleFourExchange

module _ {_∙_ : Op₂ A} (cong : Congruent₂ _∙_) where

  comm∧assoc⇒middleFour : Commutative _∙_ → Associative _∙_ →
                          _∙_ MiddleFourExchange _∙_
  comm∧assoc⇒middleFour comm assoc w x y z = begin
    (w ∙ x) ∙ (y ∙ z) ≈⟨ assoc w x (y ∙ z) ⟩
    w ∙ (x ∙ (y ∙ z)) ≈⟨ cong refl (sym (assoc x y z)) ⟩
    w ∙ ((x ∙ y) ∙ z) ≈⟨ cong refl (cong (comm x y) refl) ⟩
    w ∙ ((y ∙ x) ∙ z) ≈⟨ cong refl (assoc y x z) ⟩
    w ∙ (y ∙ (x ∙ z)) ≈⟨ sym (assoc w y (x ∙ z)) ⟩
    (w ∙ y) ∙ (x ∙ z) ∎

  identity∧middleFour⇒assoc : {e : A} → Identity e _∙_ →
                              _∙_ MiddleFourExchange _∙_ →
                              Associative _∙_
  identity∧middleFour⇒assoc {e} (identityˡ , identityʳ) middleFour x y z = begin
    (x ∙ y) ∙ z       ≈⟨ cong refl (sym (identityˡ z)) ⟩
    (x ∙ y) ∙ (e ∙ z) ≈⟨ middleFour x y e z ⟩
    (x ∙ e) ∙ (y ∙ z) ≈⟨ cong (identityʳ x) refl ⟩
    x ∙ (y ∙ z)       ∎

  identity∧middleFour⇒comm : {_+_ : Op₂ A} {e : A} → Identity e _+_ →
                             _∙_ MiddleFourExchange _+_ →
                             Commutative _∙_
  identity∧middleFour⇒comm {_+_} {e} (identityˡ , identityʳ) middleFour x y
    = begin
    x ∙ y             ≈⟨ sym (cong (identityˡ x) (identityʳ y)) ⟩
    (e + x) ∙ (y + e) ≈⟨ middleFour e x y e ⟩
    (e + y) ∙ (x + e) ≈⟨ cong (identityˡ y) (identityʳ x) ⟩
    y ∙ x             ∎

------------------------------------------------------------------------
-- SelfInverse

module _ {f : Op₁ A} (self : SelfInverse f) where

  selfInverse⇒involutive : Involutive f
  selfInverse⇒involutive = reflexive∧selfInverse⇒involutive _≈_ refl self

  selfInverse⇒congruent : Congruent _≈_ _≈_ f
  selfInverse⇒congruent {x} {y} x≈y = sym (self (begin
    f (f x) ≈⟨ selfInverse⇒involutive x ⟩
    x       ≈⟨ x≈y ⟩
    y       ∎))

  selfInverse⇒inverseᵇ : Inverseᵇ _≈_ _≈_ f f
  selfInverse⇒inverseᵇ = self ∘ sym , self ∘ sym

  selfInverse⇒surjective : Surjective _≈_ _≈_ f
  selfInverse⇒surjective y = f y , self ∘ sym

  selfInverse⇒injective : Injective _≈_ _≈_ f
  selfInverse⇒injective {x} {y} x≈y = begin
    x       ≈⟨ self x≈y ⟨
    f (f y) ≈⟨ selfInverse⇒involutive y ⟩
    y       ∎

  selfInverse⇒bijective : Bijective _≈_ _≈_ f
  selfInverse⇒bijective = selfInverse⇒injective , selfInverse⇒surjective

------------------------------------------------------------------------
-- Magma-like structures

module _ {_∙_ : Op₂ A} (comm : Commutative _∙_) where

  comm∧cancelˡ⇒cancelʳ : LeftCancellative _∙_ → RightCancellative _∙_
  comm∧cancelˡ⇒cancelʳ cancelˡ x y z eq = cancelˡ x y z $ begin
    x ∙ y ≈⟨ comm x y ⟩
    y ∙ x ≈⟨ eq ⟩
    z ∙ x ≈⟨ comm z x ⟩
    x ∙ z ∎

  comm∧cancelʳ⇒cancelˡ : RightCancellative _∙_ → LeftCancellative _∙_
  comm∧cancelʳ⇒cancelˡ cancelʳ x y z eq = cancelʳ x y z $ begin
    y ∙ x ≈⟨ comm y x ⟩
    x ∙ y ≈⟨ eq ⟩
    x ∙ z ≈⟨ comm x z ⟩
    z ∙ x ∎

------------------------------------------------------------------------
-- Monoid-like structures

module _ {_∙_ : Op₂ A} (comm : Commutative _∙_) {e : A} where

  comm∧idˡ⇒idʳ : LeftIdentity e _∙_ → RightIdentity e _∙_
  comm∧idˡ⇒idʳ idˡ x = begin
    x ∙ e ≈⟨ comm x e ⟩
    e ∙ x ≈⟨ idˡ x ⟩
    x     ∎

  comm∧idʳ⇒idˡ : RightIdentity e _∙_ → LeftIdentity e _∙_
  comm∧idʳ⇒idˡ idʳ x = begin
    e ∙ x ≈⟨ comm e x ⟩
    x ∙ e ≈⟨ idʳ x ⟩
    x     ∎

  comm∧idˡ⇒id : LeftIdentity e _∙_ → Identity e _∙_
  comm∧idˡ⇒id idˡ = idˡ , comm∧idˡ⇒idʳ idˡ

  comm∧idʳ⇒id : RightIdentity e _∙_ → Identity e _∙_
  comm∧idʳ⇒id idʳ = comm∧idʳ⇒idˡ idʳ , idʳ

  comm∧zeˡ⇒zeʳ : LeftZero e _∙_ → RightZero e _∙_
  comm∧zeˡ⇒zeʳ zeˡ x = begin
    x ∙ e ≈⟨ comm x e ⟩
    e ∙ x ≈⟨ zeˡ x ⟩
    e     ∎

  comm∧zeʳ⇒zeˡ : RightZero e _∙_ → LeftZero e _∙_
  comm∧zeʳ⇒zeˡ zeʳ x = begin
    e ∙ x ≈⟨ comm e x ⟩
    x ∙ e ≈⟨ zeʳ x ⟩
    e     ∎

  comm∧zeˡ⇒ze : LeftZero e _∙_ → Zero e _∙_
  comm∧zeˡ⇒ze zeˡ = zeˡ , comm∧zeˡ⇒zeʳ zeˡ

  comm∧zeʳ⇒ze : RightZero e _∙_ → Zero e _∙_
  comm∧zeʳ⇒ze zeʳ = comm∧zeʳ⇒zeˡ zeʳ , zeʳ

  comm∧almostCancelˡ⇒almostCancelʳ : AlmostLeftCancellative e _∙_ →
                                     AlmostRightCancellative e _∙_
  comm∧almostCancelˡ⇒almostCancelʳ cancelˡ-nonZero x y z x≉e yx≈zx =
    cancelˡ-nonZero x y z x≉e $ begin
      x ∙ y ≈⟨ comm x y ⟩
      y ∙ x ≈⟨ yx≈zx ⟩
      z ∙ x ≈⟨ comm z x ⟩
      x ∙ z ∎

  comm∧almostCancelʳ⇒almostCancelˡ : AlmostRightCancellative e _∙_ →
                                     AlmostLeftCancellative e _∙_
  comm∧almostCancelʳ⇒almostCancelˡ cancelʳ-nonZero x y z x≉e xy≈xz =
    cancelʳ-nonZero x y z x≉e $ begin
      y ∙ x ≈⟨ comm y x ⟩
      x ∙ y ≈⟨ xy≈xz ⟩
      x ∙ z ≈⟨ comm x z ⟩
      z ∙ x ∎

------------------------------------------------------------------------
-- Group-like structures

module _ {_∙_ : Op₂ A} {_⁻¹ : Op₁ A} {e} (comm : Commutative _∙_) where

  comm∧invˡ⇒invʳ : LeftInverse e _⁻¹ _∙_ → RightInverse e _⁻¹ _∙_
  comm∧invˡ⇒invʳ invˡ x = begin
    x ∙ (x ⁻¹) ≈⟨ comm x (x ⁻¹) ⟩
    (x ⁻¹) ∙ x ≈⟨ invˡ x ⟩
    e          ∎

  comm∧invˡ⇒inv : LeftInverse e _⁻¹ _∙_ → Inverse e _⁻¹ _∙_
  comm∧invˡ⇒inv invˡ = invˡ , comm∧invˡ⇒invʳ invˡ

  comm∧invʳ⇒invˡ : RightInverse e _⁻¹ _∙_ → LeftInverse e _⁻¹ _∙_
  comm∧invʳ⇒invˡ invʳ x = begin
    (x ⁻¹) ∙ x ≈⟨ comm (x ⁻¹) x ⟩
    x ∙ (x ⁻¹) ≈⟨ invʳ x ⟩
    e          ∎

  comm∧invʳ⇒inv : RightInverse e _⁻¹ _∙_ → Inverse e _⁻¹ _∙_
  comm∧invʳ⇒inv invʳ = comm∧invʳ⇒invˡ invʳ , invʳ

module _ {_∙_ : Op₂ A} {_⁻¹ : Op₁ A} {e} (cong : Congruent₂ _∙_) where

  assoc∧id∧invʳ⇒invˡ-unique : Associative _∙_ →
                              Identity e _∙_ → RightInverse e _⁻¹ _∙_ →
                              ∀ x y → (x ∙ y) ≈ e → x ≈ (y ⁻¹)
  assoc∧id∧invʳ⇒invˡ-unique assoc (idˡ , idʳ) invʳ x y eq = begin
    x                ≈⟨ sym (idʳ x) ⟩
    x ∙ e            ≈⟨ cong refl (sym (invʳ y)) ⟩
    x ∙ (y ∙ (y ⁻¹)) ≈⟨ sym (assoc x y (y ⁻¹)) ⟩
    (x ∙ y) ∙ (y ⁻¹) ≈⟨ cong eq refl ⟩
    e ∙ (y ⁻¹)       ≈⟨ idˡ (y ⁻¹) ⟩
    y ⁻¹             ∎

  assoc∧id∧invˡ⇒invʳ-unique : Associative _∙_ →
                              Identity e _∙_ → LeftInverse e _⁻¹ _∙_ →
                              ∀ x y → (x ∙ y) ≈ e → y ≈ (x ⁻¹)
  assoc∧id∧invˡ⇒invʳ-unique assoc (idˡ , idʳ) invˡ x y eq = begin
    y                ≈⟨ sym (idˡ y) ⟩
    e ∙ y            ≈⟨ cong (sym (invˡ x)) refl ⟩
    ((x ⁻¹) ∙ x) ∙ y ≈⟨ assoc (x ⁻¹) x y ⟩
    (x ⁻¹) ∙ (x ∙ y) ≈⟨ cong refl eq ⟩
    (x ⁻¹) ∙ e       ≈⟨ idʳ (x ⁻¹) ⟩
    x ⁻¹             ∎

------------------------------------------------------------------------
-- Bisemigroup-like structures

module _ {_∙_ _◦_ : Op₂ A}
         (◦-cong : Congruent₂ _◦_)
         (∙-comm : Commutative _∙_)
         where

  comm∧distrˡ⇒distrʳ :  _∙_ DistributesOverˡ _◦_ → _∙_ DistributesOverʳ _◦_
  comm∧distrˡ⇒distrʳ distrˡ x y z = begin
    (y ◦ z) ∙ x       ≈⟨ ∙-comm (y ◦ z) x ⟩
    x ∙ (y ◦ z)       ≈⟨ distrˡ x y z ⟩
    (x ∙ y) ◦ (x ∙ z) ≈⟨ ◦-cong (∙-comm x y) (∙-comm x z) ⟩
    (y ∙ x) ◦ (z ∙ x) ∎

  comm∧distrʳ⇒distrˡ : _∙_ DistributesOverʳ _◦_ → _∙_ DistributesOverˡ _◦_
  comm∧distrʳ⇒distrˡ distrˡ x y z = begin
    x ∙ (y ◦ z)       ≈⟨ ∙-comm x (y ◦ z) ⟩
    (y ◦ z) ∙ x       ≈⟨ distrˡ x y z ⟩
    (y ∙ x) ◦ (z ∙ x) ≈⟨ ◦-cong (∙-comm y x) (∙-comm z x) ⟩
    (x ∙ y) ◦ (x ∙ z) ∎

  comm∧distrˡ⇒distr :  _∙_ DistributesOverˡ _◦_ → _∙_ DistributesOver _◦_
  comm∧distrˡ⇒distr distrˡ = distrˡ , comm∧distrˡ⇒distrʳ distrˡ

  comm∧distrʳ⇒distr :  _∙_ DistributesOverʳ _◦_ → _∙_ DistributesOver _◦_
  comm∧distrʳ⇒distr distrʳ = comm∧distrʳ⇒distrˡ distrʳ , distrʳ

  comm⇒sym[distribˡ] : ∀ x → Symmetric (λ y z → (x ◦ (y ∙ z)) ≈ ((x ◦ y) ∙ (x ◦ z)))
  comm⇒sym[distribˡ] x {y} {z} prf = begin
    x ◦ (z ∙ y)       ≈⟨ ◦-cong refl (∙-comm z y) ⟩
    x ◦ (y ∙ z)       ≈⟨ prf ⟩
    (x ◦ y) ∙ (x ◦ z) ≈⟨ ∙-comm (x ◦ y) (x ◦ z) ⟩
    (x ◦ z) ∙ (x ◦ y) ∎


module _ {_∙_ _◦_ : Op₂ A}
         (∙-cong  : Congruent₂ _∙_)
         (∙-assoc : Associative _∙_)
         (◦-comm  : Commutative _◦_)
         where

  distrib∧absorbs⇒distribˡ : _∙_ Absorbs _◦_ →
                             _◦_ Absorbs _∙_ →
                             _◦_ DistributesOver _∙_ →
                             _∙_ DistributesOverˡ _◦_
  distrib∧absorbs⇒distribˡ ∙-absorbs-◦ ◦-absorbs-∙ (◦-distribˡ-∙ , ◦-distribʳ-∙) x y z = begin
    x ∙ (y ◦ z)                    ≈⟨ ∙-cong (∙-absorbs-◦ _ _) refl ⟨
    (x ∙ (x ◦ y)) ∙ (y ◦ z)        ≈⟨  ∙-cong (∙-cong refl (◦-comm _ _)) refl ⟩
    (x ∙ (y ◦ x)) ∙ (y ◦ z)        ≈⟨  ∙-assoc _ _ _ ⟩
    x ∙ ((y ◦ x) ∙ (y ◦ z))        ≈⟨ ∙-cong refl (◦-distribˡ-∙ _ _ _) ⟨
    x ∙ (y ◦ (x ∙ z))              ≈⟨ ∙-cong (◦-absorbs-∙ _ _) refl ⟨
    (x ◦ (x ∙ z)) ∙ (y ◦ (x ∙ z))  ≈⟨ ◦-distribʳ-∙ _ _ _ ⟨
    (x ∙ y) ◦ (x ∙ z)              ∎

------------------------------------------------------------------------
-- Ring-like structures

module _ {_+_ _*_ : Op₂ A}
         {_⁻¹ : Op₁ A} {0# : A}
         (+-cong : Congruent₂ _+_)
         (*-cong : Congruent₂ _*_)
         where

  assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ : Associative _+_ → _*_ DistributesOverʳ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# _⁻¹ _+_ →
                                LeftZero 0# _*_
  assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ +-assoc distribʳ idʳ invʳ  x = begin
    0# * x                                 ≈⟨ sym (idʳ _) ⟩
    (0# * x) + 0#                          ≈⟨ +-cong refl (sym (invʳ _)) ⟩
    (0# * x) + ((0# * x)  + ((0# * x)⁻¹))  ≈⟨ sym (+-assoc _ _ _) ⟩
    ((0# * x) +  (0# * x)) + ((0# * x)⁻¹)  ≈⟨ +-cong (sym (distribʳ _ _ _)) refl ⟩
    ((0# + 0#) * x) + ((0# * x)⁻¹)         ≈⟨ +-cong (*-cong (idʳ _) refl) refl ⟩
    (0# * x) + ((0# * x)⁻¹)                ≈⟨ invʳ _ ⟩
    0#                                     ∎

  assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ : Associative _+_ → _*_ DistributesOverˡ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# _⁻¹ _+_ →
                                RightZero 0# _*_
  assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ +-assoc distribˡ idʳ invʳ  x = begin
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

  subst∧comm⇒sym : Symmetric (λ a b → P (f a b))
  subst∧comm⇒sym = ≈-subst P (comm _ _)

  wlog : ∀ {r} {_R_ : Rel _ r} → Total _R_ →
         (∀ a b → a R b → P (f a b)) →
         ∀ a b → P (f a b)
  wlog r-total = Bin.wlog r-total subst∧comm⇒sym


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

comm+assoc⇒middleFour = comm∧assoc⇒middleFour
{-# WARNING_ON_USAGE comm+assoc⇒middleFour
"Warning: comm+assoc⇒middleFour was deprecated in v2.0.
Please use comm∧assoc⇒middleFour instead."
#-}
identity+middleFour⇒assoc = identity∧middleFour⇒assoc
{-# WARNING_ON_USAGE identity+middleFour⇒assoc
"Warning: identity+middleFour⇒assoc was deprecated in v2.0.
Please use identity∧middleFour⇒assoc instead."
#-}
identity+middleFour⇒comm = identity∧middleFour⇒comm
{-# WARNING_ON_USAGE identity+middleFour⇒comm
"Warning: identity+middleFour⇒comm was deprecated in v2.0.
Please use identity∧middleFour⇒comm instead."
#-}
comm+cancelˡ⇒cancelʳ = comm∧cancelˡ⇒cancelʳ
{-# WARNING_ON_USAGE comm+cancelˡ⇒cancelʳ
"Warning: comm+cancelˡ⇒cancelʳ was deprecated in v2.0.
Please use comm∧cancelˡ⇒cancelʳ instead."
#-}
comm+cancelʳ⇒cancelˡ = comm∧cancelʳ⇒cancelˡ
{-# WARNING_ON_USAGE comm+cancelʳ⇒cancelˡ
"Warning: comm+cancelʳ⇒cancelˡ was deprecated in v2.0.
Please use comm∧cancelʳ⇒cancelˡ instead."
#-}
comm+idˡ⇒idʳ = comm∧idˡ⇒idʳ
{-# WARNING_ON_USAGE comm+idˡ⇒idʳ
"Warning: comm+idˡ⇒idʳ was deprecated in v2.0.
Please use comm∧idˡ⇒idʳ instead."
#-}
comm+idʳ⇒idˡ = comm∧idʳ⇒idˡ
{-# WARNING_ON_USAGE comm+idʳ⇒idˡ
"Warning: comm+idʳ⇒idˡ was deprecated in v2.0.
Please use comm∧idʳ⇒idˡ instead."
#-}
comm+zeˡ⇒zeʳ = comm∧zeˡ⇒zeʳ
{-# WARNING_ON_USAGE comm+zeˡ⇒zeʳ
"Warning: comm+zeˡ⇒zeʳ was deprecated in v2.0.
Please use comm∧zeˡ⇒zeʳ instead."
#-}
comm+zeʳ⇒zeˡ = comm∧zeʳ⇒zeˡ
{-# WARNING_ON_USAGE comm+zeʳ⇒zeˡ
"Warning: comm+zeʳ⇒zeˡ was deprecated in v2.0.
Please use comm∧zeʳ⇒zeˡ instead."
#-}
comm+almostCancelˡ⇒almostCancelʳ = comm∧almostCancelˡ⇒almostCancelʳ
{-# WARNING_ON_USAGE comm+almostCancelˡ⇒almostCancelʳ
"Warning: comm+almostCancelˡ⇒almostCancelʳ was deprecated in v2.0.
Please use comm∧almostCancelˡ⇒almostCancelʳ instead."
#-}
comm+almostCancelʳ⇒almostCancelˡ = comm∧almostCancelʳ⇒almostCancelˡ
{-# WARNING_ON_USAGE comm+almostCancelʳ⇒almostCancelˡ
"Warning: comm+almostCancelʳ⇒almostCancelˡ was deprecated in v2.0.
Please use comm∧almostCancelʳ⇒almostCancelˡ instead."
#-}
comm+invˡ⇒invʳ = comm∧invˡ⇒invʳ
{-# WARNING_ON_USAGE comm+invˡ⇒invʳ
"Warning: comm+invˡ⇒invʳ was deprecated in v2.0.
Please use comm∧invˡ⇒invʳ instead."
#-}
comm+invʳ⇒invˡ = comm∧invʳ⇒invˡ
{-# WARNING_ON_USAGE comm+invʳ⇒invˡ
"Warning: comm+invʳ⇒invˡ was deprecated in v2.0.
Please use comm∧invʳ⇒invˡ instead."
#-}
comm+invˡ⇒inv = comm∧invˡ⇒inv
{-# WARNING_ON_USAGE comm+invˡ⇒inv
"Warning: comm+invˡ⇒inv was deprecated in v2.0.
Please use comm∧invˡ⇒inv instead."
#-}
comm+invʳ⇒inv = comm∧invʳ⇒inv
{-# WARNING_ON_USAGE comm+invʳ⇒inv
"Warning: comm+invʳ⇒inv was deprecated in v2.0.
Please use comm∧invʳ⇒inv instead."
#-}
comm+distrˡ⇒distrʳ = comm∧distrˡ⇒distrʳ
{-# WARNING_ON_USAGE comm+distrˡ⇒distrʳ
"Warning: comm+distrˡ⇒distrʳ was deprecated in v2.0.
Please use comm∧distrˡ⇒distrʳ instead."
#-}
comm+distrʳ⇒distrˡ = comm∧distrʳ⇒distrˡ
{-# WARNING_ON_USAGE comm+distrʳ⇒distrˡ
"Warning: comm+distrʳ⇒distrˡ was deprecated in v2.0.
Please use comm∧distrʳ⇒distrˡ instead."
#-}
assoc+distribʳ+idʳ+invʳ⇒zeˡ = assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ
{-# WARNING_ON_USAGE assoc+distribʳ+idʳ+invʳ⇒zeˡ
"Warning: assoc+distribʳ+idʳ+invʳ⇒zeˡ was deprecated in v2.0.
Please use assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ instead."
#-}
assoc+distribˡ+idʳ+invʳ⇒zeʳ = assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ
{-# WARNING_ON_USAGE assoc+distribˡ+idʳ+invʳ⇒zeʳ
"Warning: assoc+distribˡ+idʳ+invʳ⇒zeʳ was deprecated in v2.0.
Please use assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ instead."
#-}
assoc+id+invʳ⇒invˡ-unique = assoc∧id∧invʳ⇒invˡ-unique
{-# WARNING_ON_USAGE assoc+id+invʳ⇒invˡ-unique
"Warning: assoc+id+invʳ⇒invˡ-unique was deprecated in v2.0.
Please use assoc∧id∧invʳ⇒invˡ-unique instead."
#-}
assoc+id+invˡ⇒invʳ-unique = assoc∧id∧invˡ⇒invʳ-unique
{-# WARNING_ON_USAGE assoc+id+invˡ⇒invʳ-unique
"Warning: assoc+id+invˡ⇒invʳ-unique was deprecated in v2.0.
Please use assoc∧id∧invˡ⇒invʳ-unique instead."
#-}
subst+comm⇒sym = subst∧comm⇒sym
{-# WARNING_ON_USAGE subst+comm⇒sym
"Warning: subst+comm⇒sym was deprecated in v2.0.
Please use subst∧comm⇒sym instead."
#-}
