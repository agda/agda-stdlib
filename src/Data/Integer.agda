------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers
------------------------------------------------------------------------

module Data.Integer where

import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
import Data.Nat.Show as ℕ
open import Data.Sign as Sign using (Sign)
open import Data.String.Base using (String; _++_)
open import Function
open import Data.Sum
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- Integers, basic types and operations

open import Data.Integer.Base public

------------------------------------------------------------------------
-- Conversions

-- Decimal string representation.

show : ℤ → String
show i = showSign (sign i) ++ ℕ.show ∣ i ∣
  where
  showSign : Sign → String
  showSign Sign.- = "-"
  showSign Sign.+ = ""

------------------------------------------------------------------------
-- Properties of the view of integers as sign + absolute value

◃-cong : ∀ {i j} → sign i ≡ sign j → ∣ i ∣ ≡ ∣ j ∣ → i ≡ j
◃-cong {i} {j} sign-≡ abs-≡ = begin
  i               ≡⟨ sym $ ◃-left-inverse i ⟩
  sign i ◃ ∣ i ∣  ≡⟨ cong₂ _◃_ sign-≡ abs-≡ ⟩
  sign j ◃ ∣ j ∣  ≡⟨ ◃-left-inverse j ⟩
  j               ∎

signAbs : ∀ i → SignAbs i
signAbs i = subst SignAbs (◃-left-inverse i) (sign i ◂ ∣ i ∣)

------------------------------------------------------------------------
-- Equality is decidable

infix 4 _≟_

_≟_ : Decidable {A = ℤ} _≡_
i ≟ j with Sign._≟_ (sign i) (sign j) | ℕ._≟_ ∣ i ∣ ∣ j ∣
i ≟ j | yes sign-≡ | yes abs-≡ = yes (◃-cong sign-≡ abs-≡)
i ≟ j | no  sign-≢ | _         = no (sign-≢ ∘ cong sign)
i ≟ j | _          | no abs-≢  = no (abs-≢  ∘ cong ∣_∣)

------------------------------------------------------------------------
-- Ordering is decidable

infix  4 _≤?_

_≤?_ : Decidable _≤_
-[1+ m ] ≤? -[1+ n ] = Dec.map′ -≤- drop‿-≤- (ℕ._≤?_ n m)
-[1+ m ] ≤? +    n   = yes -≤+
+    m   ≤? -[1+ n ] = no λ ()
+    m   ≤? +    n   = Dec.map′ +≤+ drop‿+≤+ (ℕ._≤?_ m n)
