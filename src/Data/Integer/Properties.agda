------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about integers
------------------------------------------------------------------------

module Data.Integer.Properties where

open import Algebra
import Algebra.Morphism as Morphism
import Algebra.Properties.AbelianGroup
open import Data.Integer renaming (suc to sucℤ)
open import Data.Nat
  using (ℕ; suc; zero; _∸_; s≤s; z≤n; ≤-pred)
  hiding (module ℕ)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_;
    _<_ to _ℕ<_; _≥_ to _ℕ≥_; _≰_ to _ℕ≰_; _≤?_ to _ℕ≤?_)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Solver
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Sign as Sign using () renaming (_*_ to _𝕊*_)
import Data.Sign.Properties as 𝕊ₚ
open import Function using (_∘_; _$_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.PartialOrderReasoning as POR
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Algebra.FunctionProperties (_≡_ {A = ℤ})
open import Algebra.FunctionProperties.Consequences (setoid ℤ)
open import Algebra.Structures (_≡_ {A = ℤ})
open Morphism.Definitions ℤ ℕ _≡_
open ≡-Reasoning
open +-*-Solver

------------------------------------------------------------------------
-- Equality

+-injective : ∀ {m n} → + m ≡ + n → m ≡ n
+-injective refl = refl

-[1+-injective : ∀ {m n} → -[1+ m ] ≡ -[1+ n ] → m ≡ n
-[1+-injective refl = refl

≡-decSetoid : DecSetoid _ _
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- Properties of -_

neg-involutive : ∀ n → - - n ≡ n
neg-involutive (+ zero)   = refl
neg-involutive (+ suc n)  = refl
neg-involutive (-[1+ n ]) = refl

neg-injective : ∀ {m n} → - m ≡ - n → m ≡ n
neg-injective {m} {n} -m≡-n = begin
  m     ≡⟨ sym (neg-involutive m) ⟩
  - - m ≡⟨ cong -_ -m≡-n ⟩
  - - n ≡⟨ neg-involutive n ⟩
  n ∎

------------------------------------------------------------------------
-- Properties of ∣_∣

∣n∣≡0⇒n≡0 : ∀ {n} → ∣ n ∣ ≡ 0 → n ≡ + 0
∣n∣≡0⇒n≡0 {+ .zero}   refl = refl
∣n∣≡0⇒n≡0 { -[1+ n ]} ()

∣-n∣≡∣n∣ : ∀ n → ∣ - n ∣ ≡ ∣ n ∣
∣-n∣≡∣n∣ (+ zero)   = refl
∣-n∣≡∣n∣ (+ suc n)  = refl
∣-n∣≡∣n∣ (-[1+ n ]) = refl

------------------------------------------------------------------------
-- Properties of sign and _◃_

+◃n≡+n : ∀ n → Sign.+ ◃ n ≡ + n
+◃n≡+n zero    = refl
+◃n≡+n (suc _) = refl

-◃n≡-n : ∀ n → Sign.- ◃ n ≡ - + n
-◃n≡-n zero    = refl
-◃n≡-n (suc _) = refl

sign-◃ : ∀ s n → sign (s ◃ suc n) ≡ s
sign-◃ Sign.- _ = refl
sign-◃ Sign.+ _ = refl

abs-◃ : ∀ s n → ∣ s ◃ n ∣ ≡ n
abs-◃ _      zero    = refl
abs-◃ Sign.- (suc n) = refl
abs-◃ Sign.+ (suc n) = refl

signₙ◃∣n∣≡n : ∀ n → sign n ◃ ∣ n ∣ ≡ n
signₙ◃∣n∣≡n (+ n)      = +◃n≡+n n
signₙ◃∣n∣≡n (-[1+ n ]) = refl

sign-cong : ∀ {s₁ s₂ n₁ n₂} →
            s₁ ◃ suc n₁ ≡ s₂ ◃ suc n₂ → s₁ ≡ s₂
sign-cong {s₁} {s₂} {n₁} {n₂} eq = begin
  s₁                  ≡⟨ sym $ sign-◃ s₁ n₁ ⟩
  sign (s₁ ◃ suc n₁)  ≡⟨ cong sign eq ⟩
  sign (s₂ ◃ suc n₂)  ≡⟨ sign-◃ s₂ n₂ ⟩
  s₂                  ∎

abs-cong : ∀ {s₁ s₂ n₁ n₂} → s₁ ◃ n₁ ≡ s₂ ◃ n₂ → n₁ ≡ n₂
abs-cong {s₁} {s₂} {n₁} {n₂} eq = begin
  n₁           ≡⟨ sym $ abs-◃ s₁ n₁ ⟩
  ∣ s₁ ◃ n₁ ∣  ≡⟨ cong ∣_∣ eq ⟩
  ∣ s₂ ◃ n₂ ∣  ≡⟨ abs-◃ s₂ n₂ ⟩
  n₂           ∎

∣s◃m∣*∣t◃n∣≡m*n : ∀ s t m n → ∣ s ◃ m ∣ ℕ* ∣ t ◃ n ∣ ≡ m ℕ* n
∣s◃m∣*∣t◃n∣≡m*n s t m n = cong₂ _ℕ*_ (abs-◃ s m) (abs-◃ t n)

------------------------------------------------------------------------
-- Properties of _⊖_

n⊖n≡0 : ∀ n → n ⊖ n ≡ + 0
n⊖n≡0 zero    = refl
n⊖n≡0 (suc n) = n⊖n≡0 n

⊖-swap : ∀ a b → a ⊖ b ≡ - (b ⊖ a)
⊖-swap zero    zero    = refl
⊖-swap (suc _) zero    = refl
⊖-swap zero    (suc _) = refl
⊖-swap (suc a) (suc b) = ⊖-swap a b

⊖-≥ : ∀ {m n} → m ℕ≥ n → m ⊖ n ≡ + (m ∸ n)
⊖-≥ z≤n       = refl
⊖-≥ (s≤s n≤m) = ⊖-≥ n≤m

⊖-< : ∀ {m n} → m ℕ< n → m ⊖ n ≡ - + (n ∸ m)
⊖-< {zero}  (s≤s z≤n) = refl
⊖-< {suc m} (s≤s m<n) = ⊖-< m<n

⊖-≰ : ∀ {m n} → n ℕ≰ m → m ⊖ n ≡ - + (n ∸ m)
⊖-≰ = ⊖-< ∘ ℕₚ.≰⇒>

∣⊖∣-< : ∀ {m n} → m ℕ< n → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-< {zero}  (s≤s z≤n) = refl
∣⊖∣-< {suc n} (s≤s m<n) = ∣⊖∣-< m<n

∣⊖∣-≰ : ∀ {m n} → n ℕ≰ m → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-≰ = ∣⊖∣-< ∘ ℕₚ.≰⇒>

sign-⊖-< : ∀ {m n} → m ℕ< n → sign (m ⊖ n) ≡ Sign.-
sign-⊖-< {zero}  (s≤s z≤n) = refl
sign-⊖-< {suc n} (s≤s m<n) = sign-⊖-< m<n

sign-⊖-≰ : ∀ {m n} → n ℕ≰ m → sign (m ⊖ n) ≡ Sign.-
sign-⊖-≰ = sign-⊖-< ∘ ℕₚ.≰⇒>

-[n⊖m]≡-m+n : ∀ m n → - (m ⊖ n) ≡ (- (+ m)) + (+ n)
-[n⊖m]≡-m+n zero    zero    = refl
-[n⊖m]≡-m+n zero    (suc n) = refl
-[n⊖m]≡-m+n (suc m) zero    = refl
-[n⊖m]≡-m+n (suc m) (suc n) = sym (⊖-swap n m)

∣m⊖n∣≡∣n⊖m∣ : ∀ x y → ∣ x ⊖ y ∣ ≡ ∣ y ⊖ x ∣
∣m⊖n∣≡∣n⊖m∣ zero    zero    = refl
∣m⊖n∣≡∣n⊖m∣ zero    (suc _) = refl
∣m⊖n∣≡∣n⊖m∣ (suc _) zero    = refl
∣m⊖n∣≡∣n⊖m∣ (suc x) (suc y) = ∣m⊖n∣≡∣n⊖m∣ x y

+-cancelˡ-⊖ : ∀ a b c → (a ℕ+ b) ⊖ (a ℕ+ c) ≡ b ⊖ c
+-cancelˡ-⊖ zero    b c = refl
+-cancelˡ-⊖ (suc a) b c = +-cancelˡ-⊖ a b c

------------------------------------------------------------------------
-- Properties of _-_

neg-minus-pos : ∀ x y → -[1+ x ] - (+ y) ≡ -[1+ (y ℕ+ x) ]
neg-minus-pos x       zero    = refl
neg-minus-pos zero    (suc y) = cong (-[1+_] ∘ suc) (sym (ℕₚ.+-identityʳ y))
neg-minus-pos (suc x) (suc y) = cong (-[1+_] ∘ suc) (ℕₚ.+-comm (suc x) y)

[+m]-[+n]≡m⊖n : ∀ x y → (+ x) - (+ y) ≡ x ⊖ y
[+m]-[+n]≡m⊖n zero    zero    = refl
[+m]-[+n]≡m⊖n zero    (suc y) = refl
[+m]-[+n]≡m⊖n (suc x) zero    = cong (+_ ∘ suc) (ℕₚ.+-identityʳ x)
[+m]-[+n]≡m⊖n (suc x) (suc y) = refl

∣m-n∣≡∣n-m∣ : (x y : ℤ) → ∣ x - y ∣ ≡ ∣ y - x ∣
∣m-n∣≡∣n-m∣ -[1+ x ] -[1+ y ] = ∣m⊖n∣≡∣n⊖m∣ y x
∣m-n∣≡∣n-m∣ -[1+ x ] (+ y)    = begin
  ∣ -[1+ x ] - (+ y) ∣   ≡⟨ cong ∣_∣ (neg-minus-pos x y) ⟩
  suc (y ℕ+ x)           ≡⟨ sym (ℕₚ.+-suc y x) ⟩
  y ℕ+ suc x             ∎
∣m-n∣≡∣n-m∣ (+ x)    -[1+ y ] = begin
  x ℕ+ suc y             ≡⟨ ℕₚ.+-suc x y ⟩
  suc (x ℕ+ y)           ≡⟨ cong ∣_∣ (sym (neg-minus-pos y x)) ⟩
  ∣ -[1+ y ] + - (+ x) ∣ ∎
∣m-n∣≡∣n-m∣ (+ x)     (+ y) = begin
  ∣ (+ x) - (+ y) ∣ ≡⟨ cong ∣_∣ ([+m]-[+n]≡m⊖n x y) ⟩
  ∣ x ⊖ y ∣         ≡⟨ ∣m⊖n∣≡∣n⊖m∣ x y ⟩
  ∣ y ⊖ x ∣         ≡⟨ cong ∣_∣ (sym ([+m]-[+n]≡m⊖n y x)) ⟩
  ∣ (+ y) - (+ x) ∣ ∎

------------------------------------------------------------------------
-- Properties of _+_

+-comm : Commutative _+_
+-comm -[1+ a ] -[1+ b ] = cong (-[1+_] ∘ suc) (ℕₚ.+-comm a b)
+-comm (+   a ) (+   b ) = cong +_ (ℕₚ.+-comm a b)
+-comm -[1+ _ ] (+   _ ) = refl
+-comm (+   _ ) -[1+ _ ] = refl

+-identityˡ : LeftIdentity (+ 0) _+_
+-identityˡ -[1+ _ ] = refl
+-identityˡ (+   _ ) = refl

+-identityʳ : RightIdentity (+ 0) _+_
+-identityʳ = comm+idˡ⇒idʳ +-comm +-identityˡ

+-identity : Identity (+ 0) _+_
+-identity = +-identityˡ , +-identityʳ

distribˡ-⊖-+-pos : ∀ a b c → b ⊖ c + + a ≡ b ℕ+ a ⊖ c
distribˡ-⊖-+-pos _ zero    zero    = refl
distribˡ-⊖-+-pos _ zero    (suc _) = refl
distribˡ-⊖-+-pos _ (suc _) zero    = refl
distribˡ-⊖-+-pos a (suc b) (suc c) = distribˡ-⊖-+-pos a b c

distribˡ-⊖-+-neg : ∀ a b c → b ⊖ c + -[1+ a ] ≡ b ⊖ (suc c ℕ+ a)
distribˡ-⊖-+-neg _ zero    zero    = refl
distribˡ-⊖-+-neg _ zero    (suc _) = refl
distribˡ-⊖-+-neg _ (suc _) zero    = refl
distribˡ-⊖-+-neg a (suc b) (suc c) = distribˡ-⊖-+-neg a b c

distribʳ-⊖-+-pos : ∀ a b c → + a + (b ⊖ c) ≡ a ℕ+ b ⊖ c
distribʳ-⊖-+-pos a b c = begin
  + a + (b ⊖ c) ≡⟨ +-comm (+ a) (b ⊖ c) ⟩
  (b ⊖ c) + + a ≡⟨ distribˡ-⊖-+-pos a b c ⟩
  b ℕ+ a ⊖ c    ≡⟨ cong (_⊖ c) (ℕₚ.+-comm b a) ⟩
  a ℕ+ b ⊖ c    ∎

distribʳ-⊖-+-neg : ∀ a b c → -[1+ a ] + (b ⊖ c) ≡ b ⊖ (suc a ℕ+ c)
distribʳ-⊖-+-neg a b c = begin
  -[1+ a ] + (b ⊖ c) ≡⟨ +-comm -[1+ a ] (b ⊖ c) ⟩
  (b ⊖ c) + -[1+ a ] ≡⟨ distribˡ-⊖-+-neg a b c ⟩
  b ⊖ suc (c ℕ+ a)   ≡⟨ cong (λ x → b ⊖ suc x) (ℕₚ.+-comm c a) ⟩
  b ⊖ suc (a ℕ+ c)   ∎

+-assoc : Associative _+_
+-assoc (+ zero) y z rewrite +-identityˡ      y  | +-identityˡ (y + z) = refl
+-assoc x (+ zero) z rewrite +-identityʳ  x      | +-identityˡ      z  = refl
+-assoc x y (+ zero) rewrite +-identityʳ (x + y) | +-identityʳ  y      = refl
+-assoc -[1+ a ]  -[1+ b ]  (+ suc c) = sym (distribʳ-⊖-+-neg a c b)
+-assoc -[1+ a ]  (+ suc b) (+ suc c) = distribˡ-⊖-+-pos (suc c) b a
+-assoc (+ suc a) -[1+ b ]  -[1+ c ]  = distribˡ-⊖-+-neg c a b
+-assoc (+ suc a) -[1+ b ] (+ suc c)
  rewrite distribˡ-⊖-+-pos (suc c) a b
        | distribʳ-⊖-+-pos (suc a) c b
        | sym (ℕₚ.+-assoc a 1 c)
        | ℕₚ.+-comm a 1
        = refl
+-assoc (+ suc a) (+ suc b) -[1+ c ]
  rewrite distribʳ-⊖-+-pos (suc a) b c
        | sym (ℕₚ.+-assoc a 1 b)
        | ℕₚ.+-comm a 1
        = refl
+-assoc -[1+ a ] -[1+ b ] -[1+ c ]
  rewrite sym (ℕₚ.+-assoc a 1 (b ℕ+ c))
        | ℕₚ.+-comm a 1
        | ℕₚ.+-assoc a b c
        = refl
+-assoc -[1+ a ] (+ suc b) -[1+ c ]
  rewrite distribʳ-⊖-+-neg a b c
        | distribˡ-⊖-+-neg c b a
        = refl
+-assoc (+ suc a) (+ suc b) (+ suc c)
  rewrite ℕₚ.+-assoc (suc a) (suc b) (suc c)
        = refl

+-inverseˡ : LeftInverse (+ 0) -_ _+_
+-inverseˡ -[1+ n ]  = n⊖n≡0 n
+-inverseˡ (+ zero)  = refl
+-inverseˡ (+ suc n) = n⊖n≡0 n

+-inverseʳ : RightInverse (+ 0) -_ _+_
+-inverseʳ = comm+invˡ⇒invʳ +-comm +-inverseˡ

+-inverse : Inverse (+ 0) -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = +-assoc
  ; ∙-cong        = cong₂ _+_
  }

+-0-isMonoid : IsMonoid _+_ (+ 0)
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ (+ 0)
+-0-isCommutativeMonoid = record
  { isSemigroup = +-isSemigroup
  ; identityˡ   = +-identityˡ
  ; comm        = +-comm
  }

+-0-commutativeMonoid : CommutativeMonoid _ _
+-0-commutativeMonoid = record
  { Carrier             = ℤ
  ; _≈_                 = _≡_
  ; _∙_                 = _+_
  ; ε                   = + 0
  ; isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-isGroup : IsGroup _+_ (+ 0) (-_)
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse  = +-inverse
  ; ⁻¹-cong  = cong (-_)
  }

+-isAbelianGroup : IsAbelianGroup _+_ (+ 0) (-_)
+-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm    = +-comm
  }

+-0-abelianGroup : AbelianGroup _ _
+-0-abelianGroup = record
  { Carrier = ℤ
  ; _≈_ = _≡_
  ; _∙_ = _+_
  ; ε = + 0
  ; _⁻¹ = -_
  ; isAbelianGroup = +-isAbelianGroup
  }

-- Other properties of _+_

n≢1+n : ∀ {n} → n ≢ sucℤ n
n≢1+n {+ _}           ()
n≢1+n { -[1+ 0 ]}     ()
n≢1+n { -[1+ suc n ]} ()

1-[1+n]≡-n : ∀ n → sucℤ -[1+ n ] ≡ - (+ n)
1-[1+n]≡-n zero    = refl
1-[1+n]≡-n (suc n) = refl

neg-distrib-+ : ∀ m n → - (m + n) ≡ (- m) + (- n)
neg-distrib-+ (+ zero)  (+ zero)  = refl
neg-distrib-+ (+ zero)  (+ suc n) = refl
neg-distrib-+ (+ suc m) (+ zero)  = cong -[1+_] (ℕₚ.+-identityʳ m)
neg-distrib-+ (+ suc m) (+ suc n) = cong -[1+_] (ℕₚ.+-suc m n)
neg-distrib-+ -[1+ m ]  -[1+ n ]  = cong (λ v → + suc v) (sym (ℕₚ.+-suc m n))
neg-distrib-+ (+   m)   -[1+ n ]  = -[n⊖m]≡-m+n m (suc n)
neg-distrib-+ -[1+ m ]  (+   n)   =
  trans (-[n⊖m]≡-m+n n (suc m)) (+-comm (- + n) (+ suc m))

◃-distrib-+ : ∀ s m n → s ◃ (m ℕ+ n) ≡ (s ◃ m) + (s ◃ n)
◃-distrib-+ Sign.- m n = begin
  Sign.- ◃ (m ℕ+ n)           ≡⟨ -◃n≡-n (m ℕ+ n) ⟩
  - (+ (m ℕ+ n))              ≡⟨⟩
  - ((+ m) + (+ n))           ≡⟨ neg-distrib-+ (+ m) (+ n) ⟩
  (- (+ m)) + (- (+ n))       ≡⟨ sym (cong₂ _+_ (-◃n≡-n m) (-◃n≡-n n)) ⟩
  (Sign.- ◃ m) + (Sign.- ◃ n) ∎
◃-distrib-+ Sign.+ m n = begin
  Sign.+ ◃ (m ℕ+ n)           ≡⟨ +◃n≡+n (m ℕ+ n) ⟩
  + (m ℕ+ n)                  ≡⟨⟩
  (+ m) + (+ n)               ≡⟨ sym (cong₂ _+_ (+◃n≡+n m) (+◃n≡+n n)) ⟩
  (Sign.+ ◃ m) + (Sign.+ ◃ n) ∎

+-minus-telescope : ∀ x y z → (x - y) + (y - z) ≡ x - z
+-minus-telescope x y z = begin
  (x - y) + (y - z)   ≡⟨ +-assoc x (- y) (y - z) ⟩
  x + (- y + (y - z)) ≡⟨ cong (λ v → x + v) (sym (+-assoc (- y) y _)) ⟩
  x + ((- y + y) - z) ≡⟨ sym (+-assoc x (- y + y) (- z)) ⟩
  x + (- y + y) - z   ≡⟨ cong (λ a → x + a - z) (+-inverseˡ y) ⟩
  x + (+ 0) - z       ≡⟨ cong (_- z) (+-identityʳ x) ⟩
  x - z               ∎

------------------------------------------------------------------------
-- Properties of _*_

*-comm : Commutative _*_
*-comm -[1+ a ] -[1+ b ] rewrite ℕₚ.*-comm (suc a) (suc b) = refl
*-comm -[1+ a ] (+   b ) rewrite ℕₚ.*-comm (suc a) b       = refl
*-comm (+   a ) -[1+ b ] rewrite ℕₚ.*-comm a       (suc b) = refl
*-comm (+   a ) (+   b ) rewrite ℕₚ.*-comm a       b       = refl

*-identityˡ : LeftIdentity (+ 1) _*_
*-identityˡ (+ zero ) = refl
*-identityˡ -[1+  n ] rewrite ℕₚ.+-identityʳ n = refl
*-identityˡ (+ suc n) rewrite ℕₚ.+-identityʳ n = refl

*-identityʳ : RightIdentity (+ 1) _*_
*-identityʳ = comm+idˡ⇒idʳ *-comm *-identityˡ

*-identity : Identity (+ 1) _*_
*-identity = *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero (+ 0) _*_
*-zeroˡ n = refl

*-zeroʳ : RightZero (+ 0) _*_
*-zeroʳ = comm+zeˡ⇒zeʳ *-comm *-zeroˡ

*-zero : Zero (+ 0) _*_
*-zero = *-zeroˡ , *-zeroʳ

private
  lemma : ∀ a b c → c ℕ+ (b ℕ+ a ℕ* suc b) ℕ* suc c
                  ≡ c ℕ+ b ℕ* suc c ℕ+ a ℕ* suc (c ℕ+ b ℕ* suc c)
  lemma =
    solve 3 (λ a b c → c :+ (b :+ a :* (con 1 :+ b)) :* (con 1 :+ c)
                    := c :+ b :* (con 1 :+ c) :+
                       a :* (con 1 :+ (c :+ b :* (con 1 :+ c))))
            refl

*-assoc : Associative _*_
*-assoc (+ zero) _ _ = refl
*-assoc x (+ zero) z rewrite ℕₚ.*-zeroʳ ∣ x ∣ = refl
*-assoc x y (+ zero) rewrite
    ℕₚ.*-zeroʳ ∣ y ∣
  | ℕₚ.*-zeroʳ ∣ x ∣
  | ℕₚ.*-zeroʳ ∣ sign x 𝕊* sign y ◃ ∣ x ∣ ℕ* ∣ y ∣ ∣
  = refl
*-assoc -[1+ a  ] -[1+ b  ] (+ suc c) = cong (+_ ∘ suc) (lemma a b c)
*-assoc -[1+ a  ] (+ suc b) -[1+ c  ] = cong (+_ ∘ suc) (lemma a b c)
*-assoc (+ suc a) (+ suc b) (+ suc c) = cong (+_ ∘ suc) (lemma a b c)
*-assoc (+ suc a) -[1+ b  ] -[1+ c  ] = cong (+_ ∘ suc) (lemma a b c)
*-assoc -[1+ a  ] -[1+ b  ] -[1+ c  ] = cong -[1+_]     (lemma a b c)
*-assoc -[1+ a  ] (+ suc b) (+ suc c) = cong -[1+_]     (lemma a b c)
*-assoc (+ suc a) -[1+ b  ] (+ suc c) = cong -[1+_]     (lemma a b c)
*-assoc (+ suc a) (+ suc b) -[1+ c  ] = cong -[1+_]     (lemma a b c)

private

  -- lemma used to prove distributivity.
  distrib-lemma :
    ∀ a b c → (c ⊖ b) * -[1+ a ] ≡ a ℕ+ b ℕ* suc a ⊖ (a ℕ+ c ℕ* suc a)
  distrib-lemma a b c
    rewrite +-cancelˡ-⊖ a (b ℕ* suc a) (c ℕ* suc a)
          | ⊖-swap (b ℕ* suc a) (c ℕ* suc a)
    with b ℕ≤? c
  ... | yes b≤c
    rewrite ⊖-≥ b≤c
          | ⊖-≥ (ℕₚ.*-mono-≤ b≤c (ℕₚ.≤-refl {x = suc a}))
          | -◃n≡-n ((c ∸ b) ℕ* suc a)
          | ℕₚ.*-distribʳ-∸ (suc a) c b
          = refl
  ... | no b≰c
    rewrite sign-⊖-≰ b≰c
          | ∣⊖∣-≰ b≰c
          | +◃n≡+n ((b ∸ c) ℕ* suc a)
          | ⊖-≰ (b≰c ∘ ℕₚ.*-cancelʳ-≤ b c a)
          | neg-involutive (+ (b ℕ* suc a ∸ c ℕ* suc a))
          | ℕₚ.*-distribʳ-∸ (suc a) b c
          = refl

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ (+ zero) y z
  rewrite ℕₚ.*-zeroʳ ∣ y ∣
        | ℕₚ.*-zeroʳ ∣ z ∣
        | ℕₚ.*-zeroʳ ∣ y + z ∣
        = refl
*-distribʳ-+ x (+ zero) z
  rewrite +-identityˡ z
        | +-identityˡ (sign z 𝕊* sign x ◃ ∣ z ∣ ℕ* ∣ x ∣)
        = refl
*-distribʳ-+ x y (+ zero)
  rewrite +-identityʳ y
        | +-identityʳ (sign y 𝕊* sign x ◃ ∣ y ∣ ℕ* ∣ x ∣)
        = refl
*-distribʳ-+ -[1+ a ] -[1+ b ] -[1+ c ] = cong (+_) $
  solve 3 (λ a b c → (con 2 :+ b :+ c) :* (con 1 :+ a)
                  := (con 1 :+ b) :* (con 1 :+ a) :+
                     (con 1 :+ c) :* (con 1 :+ a))
          refl a b c
*-distribʳ-+ (+ suc a) (+ suc b) (+ suc c) = cong (+_) $
  solve 3 (λ a b c → (con 1 :+ b :+ (con 1 :+ c)) :* (con 1 :+ a)
                  := (con 1 :+ b) :* (con 1 :+ a) :+
                     (con 1 :+ c) :* (con 1 :+ a))
        refl a b c
*-distribʳ-+ -[1+ a ] (+ suc b) (+ suc c) = cong -[1+_] $
  solve 3 (λ a b c → a :+ (b :+ (con 1 :+ c)) :* (con 1 :+ a)
                   := (con 1 :+ b) :* (con 1 :+ a) :+
                      (a :+ c :* (con 1 :+ a)))
         refl a b c
*-distribʳ-+ (+ suc a) -[1+ b ] -[1+ c ] = cong -[1+_] $
  solve 3 (λ a b c → a :+ (con 1 :+ a :+ (b :+ c) :* (con 1 :+ a))
                  := (con 1 :+ b) :* (con 1 :+ a) :+
                     (a :+ c :* (con 1 :+ a)))
         refl a b c
*-distribʳ-+ -[1+ a ] -[1+ b ] (+ suc c) = distrib-lemma a b c
*-distribʳ-+ -[1+ a ] (+ suc b) -[1+ c ] = distrib-lemma a c b
*-distribʳ-+ (+ suc a) -[1+ b ] (+ suc c) with b ℕ≤? c
... | yes b≤c
  rewrite +-cancelˡ-⊖ a (c ℕ* suc a) (b ℕ* suc a)
        | ⊖-≥ b≤c
        | +-comm (- (+ (a ℕ+ b ℕ* suc a))) (+ (a ℕ+ c ℕ* suc a))
        | ⊖-≥ (ℕₚ.*-mono-≤ b≤c (ℕₚ.≤-refl {x = suc a}))
        | ℕₚ.*-distribʳ-∸ (suc a) c b
        | +◃n≡+n (c ℕ* suc a ∸ b ℕ* suc a)
        = refl
... | no b≰c
  rewrite +-cancelˡ-⊖ a (c ℕ* suc a) (b ℕ* suc a)
        | sign-⊖-≰ b≰c
        | ∣⊖∣-≰ b≰c
        | -◃n≡-n ((b ∸ c) ℕ* suc a)
        | ⊖-≰ (b≰c ∘ ℕₚ.*-cancelʳ-≤ b c a)
        | ℕₚ.*-distribʳ-∸ (suc a) b c
        = refl
*-distribʳ-+ (+ suc c) (+ suc a) -[1+ b ] with b ℕ≤? a
... | yes b≤a
  rewrite +-cancelˡ-⊖ c (a ℕ* suc c) (b ℕ* suc c)
        | ⊖-≥ b≤a
        | ⊖-≥ (ℕₚ.*-mono-≤ b≤a (ℕₚ.≤-refl {x = suc c}))
        | +◃n≡+n ((a ∸ b) ℕ* suc c)
        | ℕₚ.*-distribʳ-∸ (suc c) a b
        = refl
... | no b≰a
  rewrite +-cancelˡ-⊖ c (a ℕ* suc c) (b ℕ* suc c)
        | sign-⊖-≰ b≰a
        | ∣⊖∣-≰ b≰a
        | ⊖-≰ (b≰a ∘ ℕₚ.*-cancelʳ-≤ b a c)
        | -◃n≡-n ((b ∸ a) ℕ* suc c)
        | ℕₚ.*-distribʳ-∸ (suc c) b a
        = refl

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = *-assoc
  ; ∙-cong        = cong₂ _*_
  }

*-1-isMonoid : IsMonoid _*_ (+ 1)
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ (+ 1)
*-1-isCommutativeMonoid = record
  { isSemigroup = *-isSemigroup
  ; identityˡ   = *-identityˡ
  ; comm        = *-comm
  }

*-1-commutativeMonoid : CommutativeMonoid _ _
*-1-commutativeMonoid = record
  { Carrier             = ℤ
  ; _≈_                 = _≡_
  ; _∙_                 = _*_
  ; ε                   = + 1
  ; isCommutativeMonoid = *-1-isCommutativeMonoid
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ (+ 0) (+ 1)
+-*-isCommutativeSemiring = record
  { +-isCommutativeMonoid = +-0-isCommutativeMonoid
  ; *-isCommutativeMonoid = *-1-isCommutativeMonoid
  ; distribʳ              = *-distribʳ-+
  ; zeroˡ                 = *-zeroˡ
  }

+-*-isRing : IsRing _+_ _*_ -_ (+ 0) (+ 1)
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-isMonoid       = *-1-isMonoid
  ; distrib          = IsCommutativeSemiring.distrib
                         +-*-isCommutativeSemiring
  }

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ (+ 0) (+ 1)
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

+-*-commutativeRing : CommutativeRing _ _
+-*-commutativeRing = record
  { Carrier           = ℤ
  ; _≈_               = _≡_
  ; _+_               = _+_
  ; _*_               = _*_
  ; -_                = -_
  ; 0#                = + 0
  ; 1#                = + 1
  ; isCommutativeRing = +-*-isCommutativeRing
  }

-- Other properties of _*_

abs-*-commute : Homomorphic₂ ∣_∣ _*_ _ℕ*_
abs-*-commute i j = abs-◃ _ _

pos-distrib-* : ∀ x y → (+ x) * (+ y) ≡ + (x ℕ* y)
pos-distrib-* zero    y       = refl
pos-distrib-* (suc x) zero    = pos-distrib-* x zero
pos-distrib-* (suc x) (suc y) = refl

◃-distrib-* :  ∀ s t m n → (s 𝕊* t) ◃ (m ℕ* n) ≡ (s ◃ m) * (t ◃ n)
◃-distrib-* s t zero    zero    = refl
◃-distrib-* s t zero    (suc n) = refl
◃-distrib-* s t (suc m) zero    =
  trans
    (cong₂ _◃_ (𝕊ₚ.*-comm s t) (ℕₚ.*-comm m 0))
    (*-comm (t ◃ zero) (s ◃ suc m))
◃-distrib-* s t (suc m) (suc n) =
  sym (cong₂ _◃_
    (cong₂ _𝕊*_ (sign-◃ s m) (sign-◃ t n))
    (∣s◃m∣*∣t◃n∣≡m*n s t (suc m) (suc n)))

*-cancelʳ-≡ : ∀ i j k → k ≢ + 0 → i * k ≡ j * k → i ≡ j
*-cancelʳ-≡ i j k            ≢0 eq with signAbs k
*-cancelʳ-≡ i j .(+ 0)       ≢0 eq | s ◂ zero  = contradiction refl ≢0
*-cancelʳ-≡ i j .(s ◃ suc n) ≢0 eq | s ◂ suc n
  with ∣ s ◃ suc n ∣ | abs-◃ s (suc n) | sign (s ◃ suc n) | sign-◃ s n
...  | .(suc n)      | refl            | .s               | refl =
  ◃-cong (sign-i≡sign-j i j eq) $
         ℕₚ.*-cancelʳ-≡ ∣ i ∣ ∣ j ∣ $ abs-cong eq
  where
  sign-i≡sign-j : ∀ i j →
                  (sign i 𝕊* s) ◃ (∣ i ∣ ℕ* suc n) ≡
                  (sign j 𝕊* s) ◃ (∣ j ∣ ℕ* suc n) →
                  sign i ≡ sign j
  sign-i≡sign-j i              j              eq with signAbs i | signAbs j
  sign-i≡sign-j .(+ 0)         .(+ 0)         eq | s₁ ◂ zero   | s₂ ◂ zero   = refl
  sign-i≡sign-j .(+ 0)         .(s₂ ◃ suc n₂) eq | s₁ ◂ zero   | s₂ ◂ suc n₂
    with ∣ s₂ ◃ suc n₂ ∣ | abs-◃ s₂ (suc n₂)
  ... | .(suc n₂) | refl
    with abs-cong {s₁} {sign (s₂ ◃ suc n₂) 𝕊* s} {0} {suc n₂ ℕ* suc n} eq
  ...   | ()
  sign-i≡sign-j .(s₁ ◃ suc n₁) .(+ 0)         eq | s₁ ◂ suc n₁ | s₂ ◂ zero
    with ∣ s₁ ◃ suc n₁ ∣ | abs-◃ s₁ (suc n₁)
  ... | .(suc n₁) | refl
    with abs-cong {sign (s₁ ◃ suc n₁) 𝕊* s} {s₁} {suc n₁ ℕ* suc n} {0} eq
  ...   | ()
  sign-i≡sign-j .(s₁ ◃ suc n₁) .(s₂ ◃ suc n₂) eq | s₁ ◂ suc n₁ | s₂ ◂ suc n₂
    with ∣ s₁ ◃ suc n₁ ∣ | abs-◃ s₁ (suc n₁)
       | sign (s₁ ◃ suc n₁) | sign-◃ s₁ n₁
       | ∣ s₂ ◃ suc n₂ ∣ | abs-◃ s₂ (suc n₂)
       | sign (s₂ ◃ suc n₂) | sign-◃ s₂ n₂
  ... | .(suc n₁) | refl | .s₁ | refl | .(suc n₂) | refl | .s₂ | refl =
    𝕊ₚ.*-cancelʳ-≡ s₁ s₂ (sign-cong eq)

*-cancelʳ-≤-pos : ∀ m n o → m * + suc o ≤ n * + suc o → m ≤ n
*-cancelʳ-≤-pos (-[1+ m ]) (-[1+ n ]) o (-≤- n≤m) =
  -≤- (≤-pred (ℕₚ.*-cancelʳ-≤ (suc n) (suc m) o (s≤s n≤m)))
*-cancelʳ-≤-pos -[1+ _ ]   (+ _)      _ _         = -≤+
*-cancelʳ-≤-pos (+ 0)      -[1+ _ ]   _ ()
*-cancelʳ-≤-pos (+ suc _)  -[1+ _ ]   _ ()
*-cancelʳ-≤-pos (+ 0)      (+ 0)      _ _         = +≤+ z≤n
*-cancelʳ-≤-pos (+ 0)      (+ suc _)  _ _         = +≤+ z≤n
*-cancelʳ-≤-pos (+ suc _)  (+ 0)      _ (+≤+ ())
*-cancelʳ-≤-pos (+ suc m)  (+ suc n)  o (+≤+ m≤n) =
  +≤+ (ℕₚ.*-cancelʳ-≤ (suc m) (suc n) o m≤n)

*-monoʳ-≤-pos : ∀ n → (_* + suc n) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-pos _ (-≤+             {n = 0})         = -≤+
*-monoʳ-≤-pos _ (-≤+             {n = suc _})     = -≤+
*-monoʳ-≤-pos x (-≤-                         n≤m) =
  -≤- (≤-pred (ℕₚ.*-mono-≤ (s≤s n≤m) (ℕₚ.≤-refl {x = suc x})))
*-monoʳ-≤-pos _ (+≤+ {m = 0}     {n = 0}     m≤n) = +≤+ m≤n
*-monoʳ-≤-pos _ (+≤+ {m = 0}     {n = suc _} m≤n) = +≤+ z≤n
*-monoʳ-≤-pos _ (+≤+ {m = suc _} {n = 0}     ())
*-monoʳ-≤-pos x (+≤+ {m = suc _} {n = suc _} m≤n) =
  +≤+ ((ℕₚ.*-mono-≤ m≤n (ℕₚ.≤-refl {x = suc x})))

-1*n≡-n : ∀ n → -[1+ 0 ] * n ≡ - n
-1*n≡-n (+ zero)  = refl
-1*n≡-n (+ suc n) = cong -[1+_] (ℕₚ.+-identityʳ n)
-1*n≡-n -[1+ n ]  = cong (λ v → + suc v) (ℕₚ.+-identityʳ n)

------------------------------------------------------------------------
-- Properties _≤_

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive { -[1+ n ]} refl = -≤- ℕₚ.≤-refl
≤-reflexive {+ n}       refl = +≤+ ℕₚ.≤-refl

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-trans : Transitive _≤_
≤-trans -≤+       (+≤+ n≤m) = -≤+
≤-trans (-≤- n≤m) -≤+       = -≤+
≤-trans (-≤- n≤m) (-≤- k≤n) = -≤- (ℕₚ.≤-trans k≤n n≤m)
≤-trans (+≤+ m≤n) (+≤+ n≤k) = +≤+ (ℕₚ.≤-trans m≤n n≤k)

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym -≤+       ()
≤-antisym (-≤- n≤m) (-≤- m≤n) = cong -[1+_] $ ℕₚ.≤-antisym m≤n n≤m
≤-antisym (+≤+ m≤n) (+≤+ n≤m) = cong (+_)   $ ℕₚ.≤-antisym m≤n n≤m

≤-total : Total _≤_
≤-total (-[1+ m ]) (-[1+ n ]) with ℕₚ.≤-total m n
... | inj₁ m≤n = inj₂ (-≤- m≤n)
... | inj₂ n≤m = inj₁ (-≤- n≤m)
≤-total (-[1+ m ]) (+    n  ) = inj₁ -≤+
≤-total (+    m  ) (-[1+ n ]) = inj₂ -≤+
≤-total (+    m  ) (+    n  ) with ℕₚ.≤-total m n
... | inj₁ m≤n = inj₁ (+≤+ m≤n)
... | inj₂ n≤m = inj₂ (+≤+ n≤m)

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym  = ≤-antisym
  }

≤-poset : Poset _ _ _
≤-poset = record
  { Carrier = ℤ
  ; _≈_ = _≡_
  ; _≤_ = _≤_
  ; isPartialOrder = ≤-isPartialOrder
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
  { Carrier         = ℤ
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = ≤-isDecTotalOrder
  }

≤-step : ∀ {n m} → n ≤ m → n ≤ sucℤ m
≤-step -≤+             = -≤+
≤-step (+≤+ m≤n)       = +≤+ (ℕₚ.≤-step m≤n)
≤-step (-≤- z≤n)       = -≤+
≤-step (-≤- (s≤s n≤m)) = -≤- (ℕₚ.≤-step n≤m)

n≤1+n : ∀ n → n ≤ (+ 1) + n
n≤1+n n = ≤-step ≤-refl

≤-irrelevance : Irrelevant _≤_
≤-irrelevance -≤+       -≤+         = refl
≤-irrelevance (-≤- n≤m₁) (-≤- n≤m₂) = cong -≤- (ℕₚ.≤-irrelevance n≤m₁ n≤m₂)
≤-irrelevance (+≤+ n≤m₁) (+≤+ n≤m₂) = cong +≤+ (ℕₚ.≤-irrelevance n≤m₁ n≤m₂)

------------------------------------------------------------------------
-- Properties _<_

-<+ : ∀ {m n} → -[1+ m ] < + n
-<+ {0}     = +≤+ z≤n
-<+ {suc _} = -≤+

<-irrefl : Irreflexive _≡_ _<_
<-irrefl { + n}          refl (+≤+ 1+n≤n) = ℕₚ.<-irrefl refl 1+n≤n
<-irrefl { -[1+ zero  ]} refl ()
<-irrefl { -[1+ suc n ]} refl (-≤- 1+n≤n) = ℕₚ.<-irrefl refl 1+n≤n

<-asym : Asymmetric _<_
<-asym {+ n}           {+ m}           (+≤+ n<m) (+≤+ m<n) =
  ℕₚ.<-asym n<m m<n
<-asym {+ n}           { -[1+ m ]}     ()        _
<-asym { -[1+ n ]}     {+_ n₁}         _         ()
<-asym { -[1+ 0 ]}     { -[1+_] _}     ()        _
<-asym { -[1+ _ ]}     { -[1+_] 0}     _         ()
<-asym { -[1+ suc n ]} { -[1+ suc m ]} (-≤- n<m) (-≤- m<n) =
  ℕₚ.<-asym n<m m<n

<-trans : Transitive _<_
<-trans { + m}          {_}             (+≤+ m<n) (+≤+ n<o) =
  +≤+ (ℕₚ.<-trans m<n n<o)
<-trans { -[1+ 0     ]} {_}             (+≤+ m<n) (+≤+ n<o) = +≤+ z≤n
<-trans { -[1+ suc m ]} {+ n}           m<n       (+≤+ m≤n) = -≤+
<-trans { -[1+ suc m ]} { -[1+ 0 ]}     m<n       (+≤+ m≤n) = -≤+
<-trans { -[1+ suc m ]} { -[1+ suc n ]} (-≤- n≤m) -≤+       = -≤+
<-trans { -[1+ suc m ]} { -[1+ suc n ]} (-≤- n<m) (-≤- o≤n) =
  -≤- (ℕₚ.≤-trans o≤n (ℕₚ.<⇒≤ n<m))

<-cmp : Trichotomous _≡_ _<_
<-cmp (+ m) (+ n) with ℕₚ.<-cmp m n
... | tri< m<n m≢n m≯n =
  tri< (+≤+ m<n)         (m≢n ∘ +-injective) (m≯n ∘ drop‿+≤+)
... | tri≈ m≮n m≡n m≯n =
  tri≈ (m≮n ∘ drop‿+≤+) (cong (+_) m≡n)     (m≯n ∘ drop‿+≤+)
... | tri> m≮n m≢n m>n =
  tri> (m≮n ∘ drop‿+≤+) (m≢n ∘ +-injective) (+≤+ m>n)
<-cmp (+_ m)       -[1+ 0 ]     = tri> (λ())     (λ()) (+≤+ z≤n)
<-cmp (+_ m)       -[1+ suc n ] = tri> (λ())     (λ()) -≤+
<-cmp -[1+ 0 ]     (+ n)        = tri< (+≤+ z≤n) (λ()) (λ())
<-cmp -[1+ suc m ] (+ n)        = tri< -≤+       (λ()) (λ())
<-cmp -[1+ 0 ]     -[1+ 0 ]     = tri≈ (λ())     refl  (λ())
<-cmp -[1+ 0 ]     -[1+ suc n ] = tri> (λ())     (λ()) (-≤- z≤n)
<-cmp -[1+ suc m ] -[1+ 0 ]     = tri< (-≤- z≤n) (λ()) (λ())
<-cmp -[1+ suc m ] -[1+ suc n ] with ℕₚ.<-cmp (suc m) (suc n)
... | tri< m<n m≢n m≯n =
  tri> (m≯n ∘ s≤s ∘ drop‿-≤-) (m≢n ∘ -[1+-injective) (-≤- (≤-pred m<n))
... | tri≈ m≮n m≡n m≯n =
  tri≈ (m≯n ∘ s≤s ∘ drop‿-≤-) (cong -[1+_] m≡n) (m≮n ∘ s≤s ∘ drop‿-≤-)
... | tri> m≮n m≢n m>n =
  tri< (-≤- (≤-pred m>n)) (m≢n ∘ -[1+-injective) (m≮n ∘ s≤s ∘ drop‿-≤-)

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = λ {i} → <-trans {i}
  ; compare       = <-cmp
  }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { Carrier            = ℤ
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = <-isStrictTotalOrder
  }

n≮n : ∀ {n} → n ≮ n
n≮n {+ n}           (+≤+ n<n) =  contradiction n<n ℕₚ.1+n≰n
n≮n { -[1+ 0 ]}     ()
n≮n { -[1+ suc n ]} (-≤- n<n) =  contradiction n<n ℕₚ.1+n≰n

<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ m<n =  ≤-trans (n≤1+n _) m<n

≰→> : ∀ {x y} → x ≰ y → x > y
≰→> {+ m}           {+ n}           m≰n =  +≤+ (ℕₚ.≰⇒> (m≰n ∘ +≤+))
≰→> {+ m}           { -[1+ n ]}     _   =  -<+ {n} {m}
≰→> { -[1+ m ]}     {+ _}           m≰n =  contradiction -≤+ m≰n
≰→> { -[1+ 0 ]}     { -[1+ 0 ]}     m≰n =  contradiction ≤-refl m≰n
≰→> { -[1+ suc _ ]} { -[1+ 0 ]}     m≰n =  contradiction (-≤- z≤n) m≰n
≰→> { -[1+ m ]}     { -[1+ suc n ]} m≰n with m ℕ≤? n
... | yes m≤n  = -≤- m≤n
... | no  m≰n' = contradiction (-≤- (ℕₚ.≰⇒> m≰n')) m≰n

<-irrelevance : Irrelevant _<_
<-irrelevance = ≤-irrelevance

------------------------------------------------------------------------
-- Modules for reasoning about integer number relations

-- A module for reasoning about the _≤_ relation
module ≤-Reasoning = POR ≤-poset hiding (_≈⟨_⟩_)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

inverseˡ = +-inverseˡ
{-# WARNING_ON_USAGE inverseˡ
"Warning: inverseˡ was deprecated in v0.15.
Please use +-inverseˡ instead."
#-}
inverseʳ = +-inverseʳ
{-# WARNING_ON_USAGE inverseʳ
"Warning: inverseʳ was deprecated in v0.15.
Please use +-inverseʳ instead."
#-}
distribʳ = *-distribʳ-+
{-# WARNING_ON_USAGE distribʳ
"Warning: distribʳ was deprecated in v0.15.
Please use *-distribʳ-+ instead."
#-}
isCommutativeSemiring = +-*-isCommutativeSemiring
{-# WARNING_ON_USAGE isCommutativeSemiring
"Warning: isCommutativeSemiring was deprecated in v0.15.
Please use +-*-isCommutativeSemiring instead."
#-}
commutativeRing = +-*-commutativeRing
{-# WARNING_ON_USAGE commutativeRing
"Warning: commutativeRing was deprecated in v0.15.
Please use +-*-commutativeRing instead."
#-}
*-+-right-mono = *-monoʳ-≤-pos
{-# WARNING_ON_USAGE *-+-right-mono
"Warning: *-+-right-mono was deprecated in v0.15.
Please use *-monoʳ-≤-pos instead."
#-}
cancel-*-+-right-≤ = *-cancelʳ-≤-pos
{-# WARNING_ON_USAGE cancel-*-+-right-≤
"Warning: cancel-*-+-right-≤ was deprecated in v0.15.
Please use *-cancelʳ-≤-pos instead."
#-}
cancel-*-right = *-cancelʳ-≡
{-# WARNING_ON_USAGE cancel-*-right
"Warning: cancel-*-right was deprecated in v0.15.
Please use *-cancelʳ-≡ instead."
#-}
doubleNeg = neg-involutive
{-# WARNING_ON_USAGE doubleNeg
"Warning: doubleNeg was deprecated in v0.15.
Please use neg-involutive instead."
#-}
-‿involutive = neg-involutive
{-# WARNING_ON_USAGE -‿involutive
"Warning: -‿involutive was deprecated in v0.15.
Please use neg-involutive instead."
#-}
+-⊖-left-cancel = +-cancelˡ-⊖
{-# WARNING_ON_USAGE +-⊖-left-cancel
"Warning: +-⊖-left-cancel was deprecated in v0.15.
Please use +-cancelˡ-⊖ instead."
#-}
