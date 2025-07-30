------------------------------------------------------------------------
-- The Agda standard library
--
-- Modular arithmetic on integers
------------------------------------------------------------------------

open import Data.Integer.Base

module Data.Integer.ModularArithmetic (m : ℤ) where

open import Algebra.Bundles
open import Data.Integer.DivMod
open import Data.Integer.Properties
open import Data.Fin.Base as Fin using (Fin)
import Data.Fin.Properties as Fin
open import Data.Nat.Base as ℕ using (zero; suc)
import Data.Nat.DivMod as ℕ
import Data.Nat.Properties as ℕ
open import Function.Base
open import Function.Bundles
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)
open import Relation.Nullary.Decidable

open import Algebra.Ideal.Construct.Principal +-*-commutativeRing

open import Algebra.Construct.Quotient.Ring +-*-ring ⟨ m ⟩


ℤ/mℤ : Ring _ _
ℤ/mℤ  = quotientRing

-- todo:
-- * chinese remainder theorem specialized to integers
-- * finiteness: for non-zero

module _ .{{_ : NonZero m}} where

  from-% : ∀ {x y} → x % m ≡ y % m → x ≋ y
  from-% {x} {y} x%m≡y%m = x / m - y / m by begin
    x - y                                                   ≡⟨ ≡.cong₂ _-_ (a≡a%n+[a/n]*n x m) (a≡a%n+[a/n]*n y m) ⟩
    (+ (x % m) + (x / m) * m) - (+ (y % m) + (y / m) * m)   ≡⟨ ≡.cong (λ z → (+ (x % m) + (x / m) * m) + z) (neg-distrib-+ (+ (y % m)) ((y / m) * m)) ⟩
    (+ (x % m) + (x / m) * m) + (- + (y % m) - (y / m) * m) ≡⟨ +-assoc (+ (x % m) + (x / m) * m) (- + (y % m)) (- ((y / m) * m)) ⟨
    ((+ (x % m) + (x / m) * m) - + (y % m)) - (y / m) * m   ≡⟨ ≡.cong (λ z → z - (y / m) * m) (+-assoc (+ (x % m)) ((x / m) * m) (- + (y % m))) ⟩
    (+ (x % m) + ((x / m) * m - + (y % m))) - (y / m) * m   ≡⟨ ≡.cong (λ z → (+ (x % m) + z) - (y / m) * m) (+-comm ((x / m) * m) (- + (y % m))) ⟩
    (+ (x % m) + (- + (y % m) + (x / m) * m)) - (y / m) * m ≡⟨ ≡.cong (λ z → z - (y / m) * m) (+-assoc (+ (x % m)) (- + (y % m)) ((x / m) * m)) ⟨
    ((+ (x % m) - + (y % m)) + (x / m) * m) - (y / m) * m   ≡⟨ +-assoc (+ (x % m) - + (y % m)) ((x / m) * m) (- ((y / m) * m)) ⟩
    (+ (x % m) - + (y % m)) + ((x / m) * m - (y / m) * m)   ≡⟨ ≡.cong₂ (λ a b → (+ a - + (y % m)) + ((x / m) * m + b)) x%m≡y%m (neg-distribˡ-* (y / m) m) ⟩
    (+ (y % m) - + (y % m)) + ((x / m) * m + - (y / m) * m) ≡⟨ ≡.cong₂ _+_ (+-inverseʳ (+ (y % m))) (≡.sym (*-distribʳ-+ m (x / m) (- (y / m)))) ⟩
    0ℤ + (x / m - y / m) * m                                ≡⟨ +-identityˡ ((x / m - y / m) * m) ⟩
    (x / m - y / m) * m                                     ∎
    where open ≡-Reasoning

  to-% : ∀ {x y} → x ≋ y → x % m ≡ y % m
  to-% {x} {y} (k by x-y≡km) = {!!}
    where
      open ≡-Reasoning
      lemma : x % m ⊖ y % m ≡ (k - (x / m) + (y / m)) * m
      lemma = begin
        x % m ⊖ y % m               ≡⟨ m-n≡m⊖n (x % m) (y % m) ⟨
        + (x % m) - + (y % m)       ≡⟨ {!!} ⟩
        (k - (x / m) + (y / m)) * m ∎

      bound : ∣ x % m ⊖ y % m ∣ ℕ.< ∣ m ∣
      bound = {!!}

  _≋?′_ : Decidable _≋_
  x ≋?′ y = map′ from-% to-% (x % m ℕ.≟ y % m)

  ℤ/mℤ-finite : Equivalence (Ring.setoid ℤ/mℤ) (≡.setoid (Fin ∣ m ∣))
  ℤ/mℤ-finite = record
    { to = λ n → Fin.fromℕ< (n%d<d n m)
    ; from = λ i → + Fin.toℕ i
    ; to-cong = λ x≋y → Fin.fromℕ<-cong _ _ (to-% x≋y) _ _
    ; from-cong = λ i≡j → Ring.reflexive ℤ/mℤ (≡.cong (+_ ∘ Fin.toℕ) i≡j)
    }
    where
      open ≡.≡-Reasoning

      -- x ≡ x % m + (x / m) * m
      -- y ≡ y % m + (y / m) * m
      -- x - y ≡ (x / m - y / m) * m + x % m - y % m
      -- x - y ≡ k * m
      -- something about x % m being smaller than m and at least 0?
      -- so k ≡ x / m - y / m
      -- and so x % m - y % m
      -- ∴ x % m ≡ y % m

_≋?_ : Decidable _≋_
-- need to check whether m is 0
_≋?_ with ℕ.nonZero? ∣ m ∣
... | yes p = _≋?′_ {{p}}
... | no ¬p = {!!}


        
