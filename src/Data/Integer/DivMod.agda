------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

module Data.Integer.DivMod where

open import Data.Nat.Base as ℕ using (ℕ)
import Data.Nat.Properties as NProp
import Data.Nat.DivMod as NDM
open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as FProp
import Data.Sign as S
open import Data.Integer as ℤ
open import Data.Integer.Properties
open import Function

open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

infixl 7 _divℕ_ _modℕ_
_divℕ_ : (dividend : ℤ) (divisor : ℕ) {≢0 : False (divisor ℕ.≟ 0)} → ℤ
(+ n      divℕ d) {d≠0} = + (n NDM.div d) {d≠0}
(-[1+ n ] divℕ d) {d≠0} with (ℕ.suc n NDM.divMod d) {d≠0}
... | NDM.result q Fin.zero    eq = - (+ q)
... | NDM.result q (Fin.suc r) eq = -[1+ q ]

_modℕ_ : (dividend : ℤ) (divisor : ℕ) {≠0 : False (divisor ℕ.≟ 0)} → ℕ
(+ n      modℕ d) {d≠0} = (n NDM.% d) {d≠0}
(-[1+ n ] modℕ d) {d≠0} with (ℕ.suc n NDM.divMod d) {d≠0}
... | NDM.result q Fin.zero    eq = 0
... | NDM.result q (Fin.suc r) eq = d ℕ.∸ ℕ.suc (Fin.toℕ r)

a≡a%n+[a/n]*n : ∀ a n → let sn = ℕ.suc n in a ≡ + (a modℕ sn) + (a divℕ sn) * + sn
a≡a%n+[a/n]*n (+ n) d = let sd = ℕ.suc d in begin
  + n
    ≡⟨ cong +_ (NDM.a≡a%n+[a/n]*n n d) ⟩
  + (n NDM.% sd ℕ.+ n NDM.div sd ℕ.* sd)
    ≡⟨ pos-+-commute (n NDM.% sd) (n NDM.div sd ℕ.* sd) ⟩
  + (n NDM.% sd) + + (n NDM.div sd ℕ.* sd)
    ≡⟨ cong (_+_ (+ (+ n modℕ sd))) (sym (pos-distrib-* (n NDM.div sd) sd)) ⟩
  + (+ n modℕ sd) + + n divℕ sd * + sd ∎ where open ≡-Reasoning
a≡a%n+[a/n]*n -[1+ n ] d with (ℕ.suc n) NDM.divMod (ℕ.suc d)
... | NDM.result q Fin.zero    eq = let sd = ℕ.suc d in begin
  -[1+ n ]            ≡⟨ cong (-_ ∘′ +_) eq ⟩
  - + (q ℕ.* sd)      ≡⟨ cong -_ (sym (pos-distrib-* q sd)) ⟩
  - (+ q * + sd)      ≡⟨ neg-distribˡ-* (+ q) (+ sd) ⟩
  - (+ q) * + sd      ≡⟨ sym (+-identityˡ (- (+ q) * + sd)) ⟩
  + 0 + - (+ q) * + sd ∎ where open ≡-Reasoning
... | NDM.result q (Fin.suc r) eq = begin
  let sd = ℕ.suc d; sr = ℕ.suc (Fin.toℕ r); sq = ℕ.suc q in
  -[1+ n ]
    ≡⟨ cong (-_ ∘′ +_) eq ⟩
  - + (sr ℕ.+ q ℕ.* sd)
    ≡⟨ cong -_ (pos-+-commute sr (q ℕ.* sd)) ⟩
  - (+ sr + + (q ℕ.* sd))
    ≡⟨ neg-distrib-+ (+ sr) (+ (q ℕ.* sd)) ⟩
  - + sr - + (q ℕ.* sd)
    ≡⟨ cong (_-_ (- + sr)) (sym (pos-distrib-* q sd)) ⟩
  - + sr - (+ q) * (+ sd)
    ≡⟨⟩
  - + sr - pred (+ sq) * (+ sd)
    ≡⟨ cong (_-_ (- + sr)) (*-distribʳ-+ (+ sd) (- + 1)  (+ sq)) ⟩
  - + sr - (- (+ 1) * + sd + (+ sq * + sd))
    ≡⟨ cong (_+_ (- (+ sr))) (neg-distrib-+ (- (+ 1) * + sd) (+ sq * + sd)) ⟩
  - + sr + (- (-[1+ 0 ] * + sd) + - (+ sq * + sd))
    ≡⟨ cong₂ (λ p q → - + sr + (- p + q)) (-1*n≡-n (+ sd))
                                            (neg-distribˡ-* (+ sq) (+ sd)) ⟩
  - + sr + ((- - + sd) + -[1+ q ] * + sd)
    ≡⟨ sym (+-assoc (- + sr) (- - + sd) (-[1+ q ] * + sd)) ⟩
  (+ sd - + sr) + -[1+ q ] * + sd
    ≡⟨ cong (_+ -[1+ q ] * + sd) (fin-inv d r) ⟩
  + (sd ℕ.∸ sr) + -[1+ q ] * + sd
    ∎ where

    open ≡-Reasoning

    fin-inv : ∀ d (k : Fin d) → + (ℕ.suc d) - + ℕ.suc (Fin.toℕ k) ≡ + (d ℕ.∸ Fin.toℕ k)
    fin-inv (ℕ.suc n) Fin.zero    = refl
    fin-inv (ℕ.suc n) (Fin.suc k) = ⊖-≥ {n} {Fin.toℕ k} (NProp.<⇒≤ (FProp.toℕ<n k))
