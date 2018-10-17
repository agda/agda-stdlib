------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural number division
------------------------------------------------------------------------

module Data.Nat.DivMod where

open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Fin.Properties using (toℕ-fromℕ≤)
open import Data.Nat as Nat
open import Data.Nat.DivMod.Core
open import Data.Nat.Properties using (≤⇒≤″; +-assoc; +-comm; +-identityʳ)
open import Function using (_$_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

------------------------------------------------------------------------
-- Basic operations

infixl 7 _div_ _%_

-- Integer division

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
(a div 0) {}
(a div suc n) = div-helper 0 n a n

-- Integer remainder (mod)

_%_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
(a % 0) {}
(a % suc n) = mod-helper 0 n a n

------------------------------------------------------------------------
-- Properties

a≡a%n+[a/n]*n : ∀ a n → a ≡ a % suc n + (a div (suc n)) * suc n
a≡a%n+[a/n]*n a n = division-lemma 0 0 a n

a%1≡0 : ∀ a → a % 1 ≡ 0
a%1≡0 = a[modₕ]1≡0

a%n<n : ∀ a n → a % suc n < suc n
a%n<n a n = s≤s (a[modₕ]n<n 0 a n)

n%n≡0 : ∀ n → suc n % suc n ≡ 0
n%n≡0 n = n[modₕ]n≡0 0 n

a%n%n≡a%n : ∀ a n → a % suc n % suc n ≡ a % suc n
a%n%n≡a%n a n = modₕ-idem 0 a n

[a+n]%n≡a%n : ∀ a n → (a + suc n) % suc n ≡ a % suc n
[a+n]%n≡a%n a n = a+n[modₕ]n≡a[modₕ]n 0 a n

[a+kn]%n≡a%n : ∀ a k n → (a + k * (suc n)) % suc n ≡ a % suc n
[a+kn]%n≡a%n a zero    n = cong (_% suc n) (+-identityʳ a)
[a+kn]%n≡a%n a (suc k) n = begin
  (a + (m + k * m)) % m ≡⟨ cong (_% m) (sym (+-assoc a m (k * m))) ⟩
  (a + m + k * m)   % m ≡⟨ [a+kn]%n≡a%n (a + m) k n ⟩
  (a + m)           % m ≡⟨ [a+n]%n≡a%n a n ⟩
  a                 % m ∎
  where m = suc n

kn%n≡0 : ∀ k n → k * (suc n) % suc n ≡ 0
kn%n≡0 = [a+kn]%n≡a%n 0

%-distribˡ-+ : ∀ a b n → (a + b) % suc n ≡ (a % suc n + b % suc n) % suc n
%-distribˡ-+ a b n = begin
  (a + b)                           % m ≡⟨ cong (λ v → (v + b) % m) (a≡a%n+[a/n]*n a n) ⟩
  (a % m +  a div m * m + b)        % m ≡⟨ cong (_% m) (+-assoc (a % m) _ b) ⟩
  (a % m + (a div m * m + b))       % m ≡⟨ cong (λ v → (a % m + v) % m) (+-comm _ b) ⟩
  (a % m + (b + a div m * m))       % m ≡⟨ cong (_% m) (sym (+-assoc (a % m) b _)) ⟩
  (a % m +  b + a div m * m)        % m ≡⟨ [a+kn]%n≡a%n (a % m + b) (a div m) n ⟩
  (a % m +  b)                      % m ≡⟨ cong (λ v → (a % m + v) % m) (a≡a%n+[a/n]*n b n) ⟩
  (a % m + (b % m + (b div m) * m)) % m ≡⟨ sym (cong (_% m) (+-assoc (a % m) (b % m) _)) ⟩
  (a % m +  b % m + (b div m) * m)  % m ≡⟨ [a+kn]%n≡a%n (a % m + b % m) (b div m) n ⟩
  (a % m +  b % m)                  % m ∎
  where m = suc n

------------------------------------------------------------------------
--  A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
(a mod 0) {}
(a mod suc n) = fromℕ≤ (a%n<n a n)

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
(a divMod 0) {}
(a divMod suc n) = result (a div suc n) (a mod suc n) $ begin
  a                                   ≡⟨ a≡a%n+[a/n]*n a n ⟩
  a % suc n                + [a/n]*n  ≡⟨ cong (_+ [a/n]*n) (sym (toℕ-fromℕ≤ (a%n<n a n))) ⟩
  toℕ (fromℕ≤ (a%n<n a n)) + [a/n]*n  ∎
  where
  [a/n]*n = a div suc n * suc n
