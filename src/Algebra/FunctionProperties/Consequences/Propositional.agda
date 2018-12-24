------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of functions, such as associativity and
-- commutativity (specialised to propositional equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.FunctionProperties.Consequences.Propositional
       {a} {A : Set a} where

open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Rel; Setoid; Symmetric; Total)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred)

open import Algebra.FunctionProperties {A = A} _≡_
import Algebra.FunctionProperties.Consequences (setoid A) as FP⇒

------------------------------------------------------------------------
-- Re-export all proofs that don't require congruence or substitutivity

open FP⇒ public
  hiding
  ( assoc+distribʳ+idʳ+invʳ⇒zeˡ
  ; assoc+distribˡ+idʳ+invʳ⇒zeʳ
  ; assoc+id+invʳ⇒invˡ-unique
  ; assoc+id+invˡ⇒invʳ-unique
  ; comm+distrˡ⇒distrʳ
  ; comm+distrʳ⇒distrˡ
  ; comm⇒sym[distribˡ]
  ; subst+comm⇒sym
  ; wlog
  )

------------------------------------------------------------------------
-- Group-like structures

module _ {_•_ _⁻¹ ε} where

  assoc+id+invʳ⇒invˡ-unique : Associative _•_ → Identity ε _•_ →
                              RightInverse ε _⁻¹ _•_ →
                              ∀ x y → (x • y) ≡ ε → x ≡ (y ⁻¹)
  assoc+id+invʳ⇒invˡ-unique = FP⇒.assoc+id+invʳ⇒invˡ-unique (cong₂ _)

  assoc+id+invˡ⇒invʳ-unique : Associative _•_ → Identity ε _•_ →
                              LeftInverse ε _⁻¹ _•_ →
                              ∀ x y → (x • y) ≡ ε → y ≡ (x ⁻¹)
  assoc+id+invˡ⇒invʳ-unique = FP⇒.assoc+id+invˡ⇒invʳ-unique (cong₂ _)

------------------------------------------------------------------------
-- Ring-like structures

module _ {_+_ _*_ -_ 0#} where

  assoc+distribʳ+idʳ+invʳ⇒zeˡ : Associative _+_ → _*_ DistributesOverʳ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                                LeftZero 0# _*_
  assoc+distribʳ+idʳ+invʳ⇒zeˡ =
    FP⇒.assoc+distribʳ+idʳ+invʳ⇒zeˡ (cong₂ _+_) (cong₂ _*_)

  assoc+distribˡ+idʳ+invʳ⇒zeʳ : Associative _+_ → _*_ DistributesOverˡ _+_ →
                                RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                                RightZero 0# _*_
  assoc+distribˡ+idʳ+invʳ⇒zeʳ =
    FP⇒.assoc+distribˡ+idʳ+invʳ⇒zeʳ (cong₂ _+_) (cong₂ _*_)

------------------------------------------------------------------------
-- Bisemigroup-like structures

module _ {_•_ _◦_ : Op₂ A} (•-comm : Commutative _•_) where

  comm+distrˡ⇒distrʳ : _•_ DistributesOverˡ _◦_ → _•_ DistributesOverʳ _◦_
  comm+distrˡ⇒distrʳ = FP⇒.comm+distrˡ⇒distrʳ (cong₂ _) •-comm

  comm+distrʳ⇒distrˡ : _•_ DistributesOverʳ _◦_ → _•_ DistributesOverˡ _◦_
  comm+distrʳ⇒distrˡ = FP⇒.comm+distrʳ⇒distrˡ (cong₂ _) •-comm

  comm⇒sym[distribˡ] : ∀ x → Symmetric (λ y z → (x ◦ (y • z)) ≡ ((x ◦ y) • (x ◦ z)))
  comm⇒sym[distribˡ] = FP⇒.comm⇒sym[distribˡ] (cong₂ _◦_) •-comm

------------------------------------------------------------------------
-- Without Loss of Generality

module _ {p} {P : Pred A p} where

  subst+comm⇒sym : ∀ {f} (f-comm : Commutative f) →
                   Symmetric (λ a b → P (f a b))
  subst+comm⇒sym = FP⇒.subst+comm⇒sym {P = P} subst

  wlog : ∀ {f} (f-comm : Commutative f) →
         ∀ {r} {_R_ : Rel _ r} → Total _R_ →
         (∀ a b → a R b → P (f a b)) →
         ∀ a b → P (f a b)
  wlog = FP⇒.wlog {P = P} subst

------------------------------------------------------------------------
-- Selectivity

sel⇒idem : ∀ {_•_ : Op₂ A} → Selective _•_ → Idempotent _•_
sel⇒idem sel x with sel x x
... | inj₁ x•x≈x = x•x≈x
... | inj₂ x•x≈x = x•x≈x
