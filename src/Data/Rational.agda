------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

module Data.Rational where

import Algebra
import Data.Sign as S
open import Data.Empty
open import Data.Unit using (⊤; tt)
import Data.Bool.Properties as Bool
open import Function
open import Data.Product
open import Data.Integer as ℤ using (ℤ; ∣_∣; +_; -[1+_]; _◃_; sign)
open import Data.Integer.Divisibility as ℤDiv using (Coprime)
import Data.Integer.Properties as ℤ
open import Data.Nat.GCD
open import Data.Nat.Divisibility as ℕDiv using (_∣_ ; divides ; ∣-antisym)
import Data.Nat.Coprimality as C
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties using (*-assoc ; *-comm)
open import Data.Nat.Show renaming (show to ℕshow)
open import Data.Sum
open import Data.String using (String; _++_)
import Level
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; subst; cong; cong₂)
-- open P.≡-Reasoning

infix  8 -_ 1/_
infixl 7 _*_ _/_
infixl 6 _-_ _+_

------------------------------------------------------------------------
-- The definition

-- Rational numbers in reduced form. Note that there is exactly one
-- representative for every rational number. (This is the reason for
-- using "True" below. If Agda had proof irrelevance, then it would
-- suffice to use "isCoprime : Coprime numerator denominator".)

record ℚ : Set where
  constructor mkℚ
  field
    numerator     : ℤ
    denominator-1 : ℕ
    .isCoprime    : C.Coprime ∣ numerator ∣ (suc denominator-1)

  denominator : ℤ
  denominator = + suc denominator-1

-- Constructs rational numbers. The arguments have to be in reduced
-- form and the denominator has to be non-zero.

infix 4 _≢0
_≢0 : ℕ → Set
n ≢0 = False (n ℕ.≟ 0)

infixl 7 _÷_
_÷_ : (numerator : ℤ) (denominator : ℕ)
      .{coprime : True (C.coprime? ∣ numerator ∣ denominator)}
      {≢0 : denominator ≢0} →
      ℚ
(n ÷ zero)  {≢0 = ()}
(n ÷ suc d) {c} = record
  { numerator     = n
  ; denominator-1 = d
  ; isCoprime     = toWitness c
  }

private

  -- Note that the implicit arguments do not need to be given for
  -- concrete inputs:

  0/1 : ℚ
  0/1 = + 0 ÷ 1

  -½ : ℚ
  -½ = (ℤ.- + 1) ÷ 2

------------------------------------------------------------------------
-- Two useful lemmas to help with operations on rationals

-- normalize takes two natural numbers, say 6 and 21 and their gcd 3, and
-- returns them normalized as 2 and 7 and a proof that they are coprime

-- introducing a notation for that nasty pattern
pattern ⟨_&_∧_&_⟩ p eqp q eqq = GCD.is (divides p eqp , divides q eqq) _

normalize : ∀ m n g {m≢0 : m ≢0} {n≢0 : n ≢0} {g≢0 : g ≢0} → GCD m n g →
            Σ[ p ∈ ℕ ] Σ[ q ∈ ℕ ] C.Coprime (suc p) (suc q) × m ℕ.* suc q ≡ n ℕ.* suc p
normalize 0 n g {m≢0 = ()} _
normalize m 0 g {n≢0 = ()} _
normalize m n 0 {g≢0 = ()} _
normalize (suc _) n g ⟨ 0 & () ∧ q & n≡qg' ⟩
normalize m (suc _) g ⟨ p & m≡pg' ∧ 0 & () ⟩
normalize m@(suc _) n@(suc _) (suc g) G@(⟨ suc p & m≡pg' ∧ suc q & n≡qg' ⟩)
  with Bézout.identity G
normalize m@(suc _) n@(suc _) (suc g) ⟨ suc p & m≡pg' ∧ suc q & n≡qg' ⟩
  | Bézout.+- x y bezout-eq = p , q , pr , eq where

  open P.≡-Reasoning

  eq : m ℕ.* suc q ≡ n ℕ.* suc p
  eq = begin
    m ℕ.* suc q                 ≡⟨ cong (ℕ._* suc q) m≡pg' ⟩
    suc p ℕ.* suc g ℕ.* suc q   ≡⟨ *-assoc (suc p) (suc g) (suc q) ⟩
    suc p ℕ.* (suc g ℕ.* suc q) ≡⟨ cong (suc p ℕ.*_) (*-comm (suc g) (suc q)) ⟩
    suc p ℕ.* (suc q ℕ.* suc g) ≡⟨ cong (suc p ℕ.*_) (P.sym n≡qg') ⟩
    suc p ℕ.* n                 ≡⟨ *-comm (suc p) n ⟩
    n ℕ.* suc p                 ∎

  pr : C.Coprime (suc p) (suc q)
  pr = C.Bézout-coprime {d = g} $ Bézout.+- x y $ begin
    suc g ℕ.+ y ℕ.* (suc q ℕ.* suc g) ≡⟨ cong ((suc g ℕ.+_) ∘′ (y ℕ.*_)) (P.sym n≡qg') ⟩
    suc g ℕ.+ y ℕ.* n                 ≡⟨ bezout-eq ⟩
    x ℕ.* m                           ≡⟨ cong (x ℕ.*_) m≡pg' ⟩
    x ℕ.* (suc p ℕ.* suc g)           ∎
normalize m@(suc _) n@(suc _) (suc g) G@(⟨ suc p & m≡pg' ∧ suc q & n≡qg' ⟩)
  | Bézout.-+ x y bezout-eq = p , q , pr , eq where

  open P.≡-Reasoning

  eq : m ℕ.* suc q ≡ n ℕ.* suc p
  eq = begin
    m ℕ.* suc q                 ≡⟨ cong (ℕ._* suc q) m≡pg' ⟩
    suc p ℕ.* suc g ℕ.* suc q   ≡⟨ *-assoc (suc p) (suc g) (suc q) ⟩
    suc p ℕ.* (suc g ℕ.* suc q) ≡⟨ cong (suc p ℕ.*_) (*-comm (suc g) (suc q)) ⟩
    suc p ℕ.* (suc q ℕ.* suc g) ≡⟨ cong (suc p ℕ.*_) (P.sym n≡qg') ⟩
    suc p ℕ.* n                 ≡⟨ *-comm (suc p) n ⟩
    n ℕ.* suc p                 ∎

  pr : C.Coprime (suc p) (suc q)
  pr = C.Bézout-coprime {d = g} $′ Bézout.-+ x y $′ begin
    suc g ℕ.+ x ℕ.* (suc p ℕ.* suc g) ≡⟨ cong (λ h → suc g ℕ.+ x ℕ.* h) (P.sym m≡pg') ⟩
    suc g ℕ.+ x ℕ.* m             ≡⟨ bezout-eq ⟩
    y ℕ.* n                       ≡⟨ cong (y ℕ.*_) n≡qg' ⟩
    y ℕ.* (suc q ℕ.* suc g)       ∎

-- a version of gcd that returns a proof that the result is non-zero given
-- that one of the inputs is non-zero

gcd≢0 : (m n : ℕ) {m≢0 : m ≢0} → Σ[ d ∈ ℕ ] GCD m n d × d ≢0
gcd≢0 m  n {m≢0} with gcd m n
gcd≢0 m  n {m≢0} | (0 , GCD.is (0|m , _) _) with ℕDiv.0∣⇒≡0 0|m
gcd≢0 .0 n {()}  | (0 , GCD.is (0|m , _) _) | refl
gcd≢0 m  n       | (suc d , G)  = (suc d , G , tt)

pattern +0       = + 0
pattern +[1+_] n = + suc n

norm-mkℚ : (n : ℤ) (d : ℕ) → d ≢0 → ℚ
norm-mkℚ -[1+ n ] d d≢0 =
  let (q , gcd , q≢0)      = gcd≢0 (suc n) d
      (n′ , d′ , prf , eq) = normalize (suc n) d q {_} {d≢0} {q≢0} gcd
  in mkℚ -[1+ n′ ] d′ prf
norm-mkℚ +0       d d≢0 = 0/1
norm-mkℚ +[1+ n ] d d≢0 =
  let (q , gcd , q≢0)             = gcd≢0 (suc n) d
      (n′ , d′ , prf , eq) = normalize (suc n) d q {_} {d≢0} {q≢0} gcd
  in mkℚ (+ suc n′) d′ prf

------------------------------------------------------------------------------
-- Operations on rationals: unary -, reciprocal, multiplication, addition

-- unary negation

-_ : ℚ → ℚ
- mkℚ -[1+ n ] d prf = mkℚ +[1+ n ] d prf
- mkℚ +0       d prf = mkℚ +0       d prf
- mkℚ +[1+ n ] d prf = mkℚ -[1+ n ] d prf

-- reciprocal: requires a proof that the numerator is not zero

1/_ : (p : ℚ) → .{n≢0 : ∣ ℚ.numerator p ∣ ≢0} → ℚ
(1/ mkℚ +0 d prf) {()}
1/ mkℚ +[1+ n ] d prf = mkℚ +[1+ d ] n (C.sym prf)
1/ mkℚ -[1+ n ] d prf = mkℚ -[1+ d ] n (C.sym prf)

-- multiplication

_*_ : ℚ → ℚ → ℚ
mkℚ +0 d₁ prf₁ * mkℚ n₂ d₂ prf₂ = 0/1
mkℚ n₁ d₁ prf₁ * mkℚ +0 d₂ prf₂ = 0/1
mkℚ n₁ d₁ prf₁ * mkℚ n₂ d₂ prf₂ = norm-mkℚ (n₁ ℤ.* n₂) (suc d₁ ℕ.* suc d₂) _

_+_ : ℚ → ℚ → ℚ
mkℚ n₁ d₁ prf₁ + mkℚ n₂ d₂ prf₂
  with (n₁ ℤ.* +[1+ d₂ ]) ℤ.+ (n₂ ℤ.* +[1+ d₁ ])
     | (n₁ ℤ.* +[1+ d₂ ]) ℤ.+ (n₂ ℤ.* +[1+ d₁ ]) ℤ.≟ + 0
... | p | yes p≡0 = 0/1
... | p | no  p≢0 = norm-mkℚ p (suc d₁ ℕ.* suc d₂) _

-- subtraction

_-_ : ℚ → ℚ → ℚ
p₁ - p₂ = p₁ + (- p₂)

-- division

_/_ : (p₁ p₂ : ℚ) → {n≢0 : ∣ ℚ.numerator p₂ ∣ ≢0} → ℚ
_/_ p₁ p₂ {n≢0} = p₁ * (1/_ p₂ {n≢0})

-- conventional printed representation

show : ℚ → String
show p = ℤ.show (ℚ.numerator p) ++ "/" ++ ℕshow (ℕ.suc (ℚ.denominator-1 p))

------------------------------------------------------------------------
-- Equality

-- Equality of rational numbers.

infix 4 _≃_

_≃_ : Rel ℚ Level.zero
p ≃ q = ℚ.numerator p ℤ.* ℚ.denominator q
      ≡ ℚ.numerator q ℤ.* ℚ.denominator p

-- _≃_ coincides with propositional equality.

≡⇒≃ : _≡_ ⇒ _≃_
≡⇒≃ refl = refl

≃⇒≡ : _≃_ ⇒ _≡_
≃⇒≡ {i = p} {j = q} =
  (helper (numerator p) (numerator q)
         (denominator-1 p) (denominator-1 q)
         (isCoprime p) (isCoprime q))
  where
    open ℚ

    module _ (n₁ n₂ : ℤ) (d₁ d₂ : ℕ)
             .(c₁ : C.Coprime ∣ n₁ ∣ (suc d₁))
             .(c₂ : C.Coprime ∣ n₂ ∣ (suc d₂))
             (eq : n₁ ℤ.* + suc d₂ ≡ n₂ ℤ.* + suc d₁) where

      open P.≡-Reasoning

      1+d₁∣1+d₂ : suc d₁ ∣ suc d₂
      1+d₁∣1+d₂ = ℤDiv.coprime-divisor (+ suc d₁) n₁ (+ suc d₂)
                  (C.sym (recompute (C.coprime? ∣ n₁ ∣ (suc d₁)) c₁)) $
                  ℕDiv.divides ∣ n₂ ∣ $ begin
                    ∣ n₁ ℤ.* + suc d₂ ∣  ≡⟨ cong ∣_∣ eq ⟩
                    ∣ n₂ ℤ.* + suc d₁ ∣  ≡⟨ ℤ.abs-*-commute n₂ (+ suc d₁) ⟩
                    ∣ n₂ ∣ ℕ.* suc d₁    ∎

      1+d₂∣1+d₁ : suc d₂ ∣ suc d₁
      1+d₂∣1+d₁ = ℤDiv.coprime-divisor (+ suc d₂) n₂ (+ suc d₁)
                  (C.sym (recompute (C.coprime? ∣ n₂ ∣ (suc d₂)) c₂)) $
                  ℕDiv.divides ∣ n₁ ∣ (begin
                    ∣ n₂ ℤ.* + suc d₁ ∣  ≡⟨ cong ∣_∣ (P.sym eq) ⟩
                    ∣ n₁ ℤ.* + suc d₂ ∣  ≡⟨ ℤ.abs-*-commute n₁ (+ suc d₂) ⟩
                    ∣ n₁ ∣ ℕ.* suc d₂    ∎)

      .c₁′ : True (C.coprime? ∣ n₁ ∣ (suc d₁))
      c₁′ = fromWitness {P = C.Coprime ∣ n₁ ∣ (suc d₁)} c₁

      .c₂′ : True (C.coprime? ∣ n₂ ∣ (suc d₂))
      c₂′ = fromWitness {P = C.Coprime ∣ n₂ ∣ (suc d₂)} c₂

      helper : (n₁ ÷ suc d₁) {c₁′} ≡ (n₂ ÷ suc d₂) {c₂′}
      helper     with ∣-antisym 1+d₁∣1+d₂ 1+d₂∣1+d₁
      ... | refl with ℤ.*-cancelʳ-≡ n₁ n₂ (+ suc d₁) (λ ()) eq
      ... | refl = refl

------------------------------------------------------------------------
-- Equality is decidable

infix 4 _≟_

_≟_ : Decidable {A = ℚ} _≡_
p ≟ q with ℚ.numerator p ℤ.* ℚ.denominator q ℤ.≟
           ℚ.numerator q ℤ.* ℚ.denominator p
... | yes pq≃qp = yes (≃⇒≡ pq≃qp)
... | no ¬pq≃qp = no (¬pq≃qp ∘ ≡⇒≃)

------------------------------------------------------------------------
-- Ordering

infix 4 _≤_ _≤?_

data _≤_ : ℚ → ℚ → Set where
  *≤* : ∀ {p q} →
        ℚ.numerator p ℤ.* ℚ.denominator q ℤ.≤
        ℚ.numerator q ℤ.* ℚ.denominator p →
        p ≤ q

drop-*≤* : ∀ {p q} → p ≤ q →
           ℚ.numerator p ℤ.* ℚ.denominator q ℤ.≤
           ℚ.numerator q ℤ.* ℚ.denominator p
drop-*≤* (*≤* pq≤qp) = pq≤qp

_≤?_ : Decidable _≤_
p ≤? q with ℚ.numerator p ℤ.* ℚ.denominator q ℤ.≤?
            ℚ.numerator q ℤ.* ℚ.denominator p
p ≤? q | yes pq≤qp = yes (*≤* pq≤qp)
p ≤? q | no ¬pq≤qp = no (λ { (*≤* pq≤qp) → ¬pq≤qp pq≤qp })

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive refl = *≤* ℤ.≤-refl

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-trans : Transitive _≤_
≤-trans {i = mkℚ n₁ d₁ c₁} {j = mkℚ n₂ d₂ c₂} {k = mkℚ n₃ d₃ c₃} (*≤* eq₁) (*≤* eq₂)
  = *≤* $ ℤ.*-cancelʳ-≤-pos (n₁ ℤ.* + suc d₃) (n₃ ℤ.* + suc d₁) d₂ $ begin
  let sd₁ = + suc d₁; sd₂ = + suc d₂; sd₃ = + suc d₃ in
  (n₁ ℤ.* sd₃) ℤ.* sd₂ ≡⟨ ℤ.*-assoc n₁ sd₃ sd₂ ⟩
  n₁ ℤ.* (sd₃ ℤ.* sd₂) ≡⟨ cong (n₁ ℤ.*_) (ℤ.*-comm sd₃ sd₂) ⟩
  n₁ ℤ.* (sd₂ ℤ.* sd₃) ≡⟨ P.sym (ℤ.*-assoc n₁ sd₂ sd₃) ⟩
  (n₁ ℤ.* sd₂) ℤ.* sd₃ ≤⟨ ℤ.*-monoʳ-≤-pos d₃ eq₁ ⟩
  (n₂ ℤ.* sd₁) ℤ.* sd₃ ≡⟨ cong (ℤ._* sd₃) (ℤ.*-comm n₂ sd₁) ⟩
  (sd₁ ℤ.* n₂) ℤ.* sd₃ ≡⟨ ℤ.*-assoc sd₁ n₂ sd₃ ⟩
  sd₁ ℤ.* (n₂ ℤ.* sd₃) ≤⟨ ℤ.*-monoˡ-≤-pos d₁ eq₂ ⟩
  sd₁ ℤ.* (n₃ ℤ.* sd₂) ≡⟨ P.sym (ℤ.*-assoc sd₁ n₃ sd₂) ⟩
  (sd₁ ℤ.* n₃) ℤ.* sd₂ ≡⟨ cong (ℤ._* sd₂) (ℤ.*-comm sd₁ n₃) ⟩
  (n₃ ℤ.* sd₁) ℤ.* sd₂ ∎

  where open ℤ.≤-Reasoning

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym (*≤* le₁) (*≤* le₂) = ≃⇒≡ (ℤ.≤-antisym le₁ le₂)

≤-total : Total _≤_
≤-total p q =
    [ inj₁ ∘′ *≤* , inj₂ ∘′ *≤* ]′
      (ℤ.≤-total (ℚ.numerator p ℤ.* ℚ.denominator q)
                 (ℚ.numerator q ℤ.* ℚ.denominator p))

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = P.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-preorder : Preorder _ _ _
≤-preorder = record
  { isPreorder = ≤-isPreorder
  }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

≤-decTotalOrder : DecTotalOrder _ _ _
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }

------------------------------------------------------------------------------
-- A few constants and some small tests

0ℚ 1ℚ : ℚ
0ℚ = + 0 ÷ 1
1ℚ = + 1 ÷ 1

private

  p₀ p₁ p₂ p₃ : ℚ
  p₀ = + 1 ÷ 2
  p₁ = + 1 ÷ 3
  p₂ = -[1+ 2 ] ÷ 4
  p₃ = + 3 ÷ 4

  test₀ = show p₂
  test₁ = show (- p₂)
  test₂ = show (1/ p₂)
  test₃ = show (p₀ + p₀)
  test₄ = show (p₁ * p₂)
