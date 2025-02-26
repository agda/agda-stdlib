------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of functions, such as associativity and
-- commutativity (specialised to propositional equality)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Consequences.Propositional
  {a} {A : Set a} where

open import Algebra.Core using (Op₁; Op₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Symmetric; Total)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (setoid)
open import Relation.Unary using (Pred)

open import Algebra.Definitions {A = A} _≡_
import Algebra.Consequences.Setoid (setoid A) as Base

private
  variable
    e ε 0# : A
    f _⁻¹ -_ : Op₁ A
    _∙_ _◦_ _+_ _*_ : Op₂ A


------------------------------------------------------------------------
-- Re-export all proofs that don't require congruence or substitutivity

open Base public
  hiding
  ( comm∧assoc⇒middleFour
  ; identity∧middleFour⇒assoc
  ; identity∧middleFour⇒comm
  ; assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ
  ; assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ
  ; assoc∧id∧invʳ⇒invˡ-unique
  ; assoc∧id∧invˡ⇒invʳ-unique
  ; comm∧distrˡ⇒distrʳ
  ; comm∧distrʳ⇒distrˡ
  ; comm⇒sym[distribˡ]
  ; subst∧comm⇒sym
  ; wlog
-- plus all the deprecated versions of the above
  ; comm+assoc⇒middleFour
  ; identity+middleFour⇒assoc
  ; identity+middleFour⇒comm
  ; assoc+distribʳ+idʳ+invʳ⇒zeˡ
  ; assoc+distribˡ+idʳ+invʳ⇒zeʳ
  ; assoc+id+invʳ⇒invˡ-unique
  ; assoc+id+invˡ⇒invʳ-unique
  ; comm+distrˡ⇒distrʳ
  ; comm+distrʳ⇒distrˡ
  ; subst+comm⇒sym
  )

------------------------------------------------------------------------
-- Group-like structures

assoc∧id∧invʳ⇒invˡ-unique : Associative _∙_ → Identity ε _∙_ →
                            RightInverse ε _⁻¹ _∙_ →
                            ∀ x y → (x ∙ y) ≡ ε → x ≡ (y ⁻¹)
assoc∧id∧invʳ⇒invˡ-unique = Base.assoc∧id∧invʳ⇒invˡ-unique (cong₂ _)

assoc∧id∧invˡ⇒invʳ-unique : Associative _∙_ → Identity ε _∙_ →
                            LeftInverse ε _⁻¹ _∙_ →
                            ∀ x y → (x ∙ y) ≡ ε → y ≡ (x ⁻¹)
assoc∧id∧invˡ⇒invʳ-unique = Base.assoc∧id∧invˡ⇒invʳ-unique (cong₂ _)

------------------------------------------------------------------------
-- Ring-like structures

assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ : Associative _+_ → _*_ DistributesOverʳ _+_ →
                              RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                              LeftZero 0# _*_
assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ {_+_ = _+_} {_*_ = _*_} =
  Base.assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ (cong₂ _+_) (cong₂ _*_)

assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ : Associative _+_ → _*_ DistributesOverˡ _+_ →
                              RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                              RightZero 0# _*_
assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ {_+_ = _+_} {_*_ = _*_} =
  Base.assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ (cong₂ _+_) (cong₂ _*_)

------------------------------------------------------------------------
-- Bisemigroup-like structures

module _ (∙-comm : Commutative _∙_) where

  comm∧distrˡ⇒distrʳ : _∙_ DistributesOverˡ _◦_ → _∙_ DistributesOverʳ _◦_
  comm∧distrˡ⇒distrʳ = Base.comm+distrˡ⇒distrʳ (cong₂ _) ∙-comm

  comm∧distrʳ⇒distrˡ : _∙_ DistributesOverʳ _◦_ → _∙_ DistributesOverˡ _◦_
  comm∧distrʳ⇒distrˡ = Base.comm∧distrʳ⇒distrˡ (cong₂ _) ∙-comm

  comm⇒sym[distribˡ] : ∀ x → Symmetric (λ y z → (x ◦ (y ∙ z)) ≡ ((x ◦ y) ∙ (x ◦ z)))
  comm⇒sym[distribˡ] = Base.comm⇒sym[distribˡ] (cong₂ _) ∙-comm

------------------------------------------------------------------------
-- MiddleFourExchange

comm∧assoc⇒middleFour : Commutative _∙_ → Associative _∙_ →
                        _∙_ MiddleFourExchange _∙_
comm∧assoc⇒middleFour = Base.comm∧assoc⇒middleFour (cong₂ _)

identity∧middleFour⇒assoc : Identity e _∙_ →
                            _∙_ MiddleFourExchange _∙_ →
                            Associative _∙_
identity∧middleFour⇒assoc {_∙_ = _∙_} = Base.identity∧middleFour⇒assoc (cong₂ _∙_)

identity∧middleFour⇒comm : Identity e _+_ →
                           _∙_ MiddleFourExchange _+_ →
                           Commutative _∙_
identity∧middleFour⇒comm = Base.identity∧middleFour⇒comm (cong₂ _)

------------------------------------------------------------------------
-- Without Loss of Generality

module _ {p} {P : Pred A p} (∙-comm : Commutative _∙_) where

  subst∧comm⇒sym : Symmetric (λ a b → P (a ∙ b))
  subst∧comm⇒sym = Base.subst∧comm⇒sym {P = P} subst ∙-comm

  wlog : ∀ {r} {_R_ : Rel _ r} → Total _R_ →
         (∀ a b → a R b → P (a ∙ b)) →
         ∀ a b → P (a ∙ b)
  wlog = Base.wlog {P = P} subst ∙-comm


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
