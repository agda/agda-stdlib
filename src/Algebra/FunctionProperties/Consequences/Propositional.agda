------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of functions, such as associativity and
-- commutativity (specialised to propositional equality)
------------------------------------------------------------------------

module Algebra.FunctionProperties.Consequences.Propositional
       {a} (A : Set a) where

open import Relation.Binary using (Rel; Setoid; Symmetric; Total)
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties {A = A} _≡_

open import Algebra.FunctionProperties.Consequences (setoid A) as FP⇒
  hiding ( assoc+distribʳ+idʳ+invʳ⇒zeˡ
         ; assoc+distribˡ+idʳ+invʳ⇒zeʳ
         ; assoc+id+invʳ⇒invˡ-unique
         ; assoc+id+invˡ⇒invʳ-unique
         ; comm+distrˡ⇒distrʳ
         ; comm+distrʳ⇒distrˡ
         ; comm⇒sym[distribˡ]
         ; subst+comm⇒sym
         ; wlog
         )
  public

assoc+distribʳ+idʳ+invʳ⇒zeˡ : ∀ {_+_ _*_ -_ 0#} →
                            Associative _+_ → _*_ DistributesOverʳ _+_ →
                            RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                            LeftZero 0# _*_
assoc+distribʳ+idʳ+invʳ⇒zeˡ {_+_} {_*_} =
  FP⇒.assoc+distribʳ+idʳ+invʳ⇒zeˡ (cong₂ _+_) (cong₂ _*_)

assoc+distribˡ+idʳ+invʳ⇒zeʳ : ∀ {_+_ _*_ -_ 0#} →
                            Associative _+_ → _*_ DistributesOverˡ _+_ →
                            RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                            RightZero 0# _*_
assoc+distribˡ+idʳ+invʳ⇒zeʳ {_+_} {_*_} =
  FP⇒.assoc+distribˡ+idʳ+invʳ⇒zeʳ (cong₂ _+_) (cong₂ _*_)

assoc+id+invʳ⇒invˡ-unique : ∀ {_•_ _⁻¹ ε} →
  Associative _•_ → Identity ε _•_ → RightInverse ε _⁻¹ _•_ →
  ∀ x y → (x • y) ≡ ε → x ≡ (y ⁻¹)
assoc+id+invʳ⇒invˡ-unique =
  FP⇒.assoc+id+invʳ⇒invˡ-unique (cong₂ _)

assoc+id+invˡ⇒invʳ-unique : ∀ {_•_ _⁻¹ ε} →
  Associative _•_ → Identity ε _•_ → LeftInverse ε _⁻¹ _•_ →
  ∀ x y → (x • y) ≡ ε → y ≡ (x ⁻¹)
assoc+id+invˡ⇒invʳ-unique =
  FP⇒.assoc+id+invˡ⇒invʳ-unique (cong₂ _)

------------------------------------------------------------------------
-- Distributivity

comm+distrˡ⇒distrʳ : ∀ {_•_ _◦_} →
  Commutative _•_ → _•_ DistributesOverˡ _◦_ → _•_ DistributesOverʳ _◦_
comm+distrˡ⇒distrʳ = FP⇒.comm+distrˡ⇒distrʳ (cong₂ _)

comm+distrʳ⇒distrˡ : ∀ {_•_ _◦_} →
  Commutative _•_ → _•_ DistributesOverʳ _◦_ → _•_ DistributesOverˡ _◦_
comm+distrʳ⇒distrˡ = FP⇒.comm+distrʳ⇒distrˡ (cong₂ _)

comm⇒sym[distribˡ] : ∀ {_•_ _◦_} → Commutative _◦_ →
                     ∀ x → Symmetric (λ y z → (x • (y ◦ z)) ≡ ((x • y) ◦ (x • z)))
comm⇒sym[distribˡ] {_•_} = FP⇒.comm⇒sym[distribˡ] (cong₂ _•_)

------------------------------------------------------------------------
-- Without Loss of Generality

subst+comm⇒sym : ∀ {p f} {P : A → Set p} (f-comm : Commutative f) →
                 Symmetric (λ a b → P (f a b))
subst+comm⇒sym {P = P} = FP⇒.subst+comm⇒sym {P = P} subst

wlog : ∀ {p f} {P : A → Set p} (f-comm : Commutative f) →
       ∀ {r} {_R_ : Rel _ r} → Total _R_ →
       (∀ a b → a R b → P (f a b)) →
       ∀ a b → P (f a b)
wlog {P = P} = FP⇒.wlog {P = P} subst
