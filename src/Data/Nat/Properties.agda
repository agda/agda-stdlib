------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties about natural number operations
------------------------------------------------------------------------

-- See README.Nat for some examples showing how this module can be
-- used.

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Properties where

open import Axiom.UniquenessOfIdentityProofs
open import Algebra
open import Algebra.Morphism
open import Algebra.FunctionProperties.Consequences.Propositional
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Bool.Properties using (T?)
open import Data.Empty
open import Data.Nat.Base
open import Data.Product
open import Data.Sum
open import Data.Unit using (tt)
open import Function
open import Function.Injection using (_↣_)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using (True; via-injection; map′)
open import Relation.Nullary.Negation using (contradiction)

open import Algebra.FunctionProperties {A = ℕ} _≡_
  hiding (LeftCancellative; RightCancellative; Cancellative)
open import Algebra.FunctionProperties
  using (LeftCancellative; RightCancellative; Cancellative)
open import Algebra.Structures {A = ℕ} _≡_

------------------------------------------------------------------------
-- Properties of _≡_
------------------------------------------------------------------------

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

≡ᵇ⇒≡ : ∀ m n → T (m ≡ᵇ n) → m ≡ n
≡ᵇ⇒≡ zero    zero    _  = refl
≡ᵇ⇒≡ (suc m) (suc n) eq = cong suc (≡ᵇ⇒≡ m n eq)

≡⇒≡ᵇ : ∀ m n → m ≡ n → T (m ≡ᵇ n)
≡⇒≡ᵇ zero    zero    eq = _
≡⇒≡ᵇ (suc m) (suc n) eq = ≡⇒≡ᵇ m n (suc-injective eq)

-- NB: we use the builtin function `_≡ᵇ_` here so that the function
-- quickly decides whether to return `yes` or `no`. It still takes
-- a linear amount of time to generate the proof if it is inspected.
-- We expect the main benefit to be visible in compiled code as the
-- backend erases proofs.

infix 4 _≟_
_≟_ : Decidable {A = ℕ} _≡_
m ≟ n = map′ (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n) (T? (m ≡ᵇ n))

≡-irrelevant : Irrelevant {A = ℕ} _≡_
≡-irrelevant = Decidable⇒UIP.≡-irrelevant _≟_

≟-diag : ∀ {m n} (eq : m ≡ n) → (m ≟ n) ≡ yes eq
≟-diag = ≡-≟-identity _≟_

≡-isDecEquivalence : IsDecEquivalence (_≡_ {A = ℕ})
≡-isDecEquivalence = record
  { isEquivalence = isEquivalence
  ; _≟_           = _≟_
  }

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = record
  { Carrier          = ℕ
  ; _≈_              = _≡_
  ; isDecEquivalence = ≡-isDecEquivalence
  }

1+n≢0 : ∀ {n} → suc n ≢ 0
1+n≢0 ()

------------------------------------------------------------------------
-- Properties of _<ᵇ_
------------------------------------------------------------------------

<ᵇ⇒< : ∀ m n → T (m <ᵇ n) → m < n
<ᵇ⇒< zero    (suc n) m<n = s≤s z≤n
<ᵇ⇒< (suc m) (suc n) m<n = s≤s (<ᵇ⇒< m n m<n)

<⇒<ᵇ : ∀ {m n} → m < n → T (m <ᵇ n)
<⇒<ᵇ (s≤s z≤n)       = tt
<⇒<ᵇ (s≤s (s≤s m<n)) = <⇒<ᵇ (s≤s m<n)

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n

------------------------------------------------------------------------
-- Relational properties of _≤_

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive {zero}  refl = z≤n
≤-reflexive {suc m} refl = s≤s (≤-reflexive refl)

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

≤-trans : Transitive _≤_
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

≤-total : Total _≤_
≤-total zero    _       = inj₁ z≤n
≤-total _       zero    = inj₂ z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | inj₁ m≤n = inj₁ (s≤s m≤n)
... | inj₂ n≤m = inj₂ (s≤s n≤m)

≤-irrelevant : Irrelevant _≤_
≤-irrelevant z≤n        z≤n        = refl
≤-irrelevant (s≤s m≤n₁) (s≤s m≤n₂) = cong s≤s (≤-irrelevant m≤n₁ m≤n₂)

-- NB: we use the builtin function `_<ᵇ_` here so that the function
-- quickly decides whether to return `yes` or `no`. It still takes
-- a linear amount of time to generate the proof if it is inspected.
-- We expect the main benefit to be visible in compiled code as the
-- backend erases proofs.

infix 4 _≤?_ _≥?_

_≤?_ : Decidable _≤_
zero  ≤? _     = yes z≤n
suc m ≤? n with T? (m <ᵇ n)
... | yes m<n = yes (<ᵇ⇒< m n m<n)
... | no  m≮n = no  (m≮n ∘ <⇒<ᵇ)

_≥?_ : Decidable _≥_
_≥?_ = flip _≤?_

------------------------------------------------------------------------
-- Structures

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
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

------------------------------------------------------------------------
-- Packages

≤-preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder = record
  { isPreorder = ≤-isPreorder
  }

≤-poset : Poset 0ℓ 0ℓ 0ℓ
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

≤-totalOrder : TotalOrder 0ℓ 0ℓ 0ℓ
≤-totalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  }

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }

------------------------------------------------------------------------
-- Other properties of _≤_

s≤s-injective : ∀ {m n} {p q : m ≤ n} → s≤s p ≡ s≤s q → p ≡ q
s≤s-injective refl = refl

≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step z≤n       = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

n≤1+n : ∀ n → n ≤ 1 + n
n≤1+n _ = ≤-step ≤-refl

1+n≰n : ∀ {n} → 1 + n ≰ n
1+n≰n (s≤s le) = 1+n≰n le

n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
n≤0⇒n≡0 z≤n = refl

------------------------------------------------------------------------
-- Properties of _<_
------------------------------------------------------------------------

-- Relationships between the various relations

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (s≤s m≤n) = ≤-trans m≤n (≤-step ≤-refl)

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ m<n refl = 1+n≰n m<n

≤⇒≯ : _≤_ ⇒ _≯_
≤⇒≯ (s≤s m≤n) (s≤s n≤m) = ≤⇒≯ m≤n n≤m

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ (s≤s m+1≤n) (s≤s n≤m) = <⇒≱ m+1≤n n≤m

<⇒≯ : _<_ ⇒ _≯_
<⇒≯ (s≤s m<n) (s≤s n<m) = <⇒≯ m<n n<m

≰⇒≮ : _≰_ ⇒ _≮_
≰⇒≮ m≰n 1+m≤n = m≰n (<⇒≤ 1+m≤n)

≰⇒> : _≰_ ⇒ _>_
≰⇒> {zero}          z≰n = contradiction z≤n z≰n
≰⇒> {suc m} {zero}  _   = s≤s z≤n
≰⇒> {suc m} {suc n} m≰n = s≤s (≰⇒> (m≰n ∘ s≤s))

≰⇒≥ : _≰_ ⇒ _≥_
≰⇒≥ = <⇒≤ ∘ ≰⇒>

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ {_}     {zero}  _       = z≤n
≮⇒≥ {zero}  {suc j} 1≮j+1   = contradiction (s≤s z≤n) 1≮j+1
≮⇒≥ {suc i} {suc j} i+1≮j+1 = s≤s (≮⇒≥ (i+1≮j+1 ∘ s≤s))

≤∧≢⇒< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤∧≢⇒< {_} {zero}  z≤n       m≢n     = contradiction refl m≢n
≤∧≢⇒< {_} {suc n} z≤n       m≢n     = s≤s z≤n
≤∧≢⇒< {_} {suc n} (s≤s m≤n) 1+m≢1+n =
  s≤s (≤∧≢⇒< m≤n (1+m≢1+n ∘ cong suc))

------------------------------------------------------------------------
-- Relational properties of _<_

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (s≤s n<n) = <-irrefl refl n<n

<-asym : Asymmetric _<_
<-asym (s≤s n<m) (s≤s m<n) = <-asym n<m m<n

<-trans : Transitive _<_
<-trans (s≤s i≤j) (s≤s j<k) = s≤s (≤-trans i≤j (≤-trans (n≤1+n _) j<k))

<-transʳ : Trans _≤_ _<_ _<_
<-transʳ m≤n (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

<-transˡ : Trans _<_ _≤_ _<_
<-transˡ (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

-- NB: we use the builtin function `_<ᵇ_` here so that the function
-- quickly decides which constructor to return. It still takes a
-- linear amount of time to generate the proof if it is inspected.
-- We expect the main benefit to be visible in compiled code as the
-- backend erases proofs.

<-cmp : Trichotomous _≡_ _<_
<-cmp m n with m ≟ n | T? (m <ᵇ n)
... | yes m≡n | _       = tri≈ (<-irrefl m≡n) m≡n (<-irrefl (sym m≡n))
... | no  m≢n | yes m<n = tri< (<ᵇ⇒< m n m<n) m≢n (<⇒≯ (<ᵇ⇒< m n m<n))
... | no  m≢n | no  m≮n = tri> (m≮n ∘ <⇒<ᵇ)   m≢n (≤∧≢⇒< (≮⇒≥ (m≮n ∘ <⇒<ᵇ)) (m≢n ∘ sym))

infix 4 _<?_ _>?_

_<?_ : Decidable _<_
x <? y = suc x ≤? y

_>?_ : Decidable _>_
_>?_ = flip _<?_

<-irrelevant : Irrelevant _<_
<-irrelevant = ≤-irrelevant

<-resp₂-≡ : _<_ Respects₂ _≡_
<-resp₂-≡ = subst (_ <_) , subst (_< _)

------------------------------------------------------------------------
-- Packages

<-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = <-resp₂-≡
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

<-strictPartialOrder : StrictPartialOrder 0ℓ 0ℓ 0ℓ
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

<-strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
<-strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  }

------------------------------------------------------------------------
-- Other properties of _<_

n≮n : ∀ n → n ≮ n
n≮n n = <-irrefl (refl {x = n})

m<n⇒n≢0 : ∀ {m n} → m < n → n ≢ 0
m<n⇒n≢0 (s≤s m≤n) ()

n≢0⇒n>0 : ∀ {n} → n ≢ 0 → n > 0
n≢0⇒n>0 {zero}  0≢0 =  contradiction refl 0≢0
n≢0⇒n>0 {suc n} _   =  s≤s z≤n

------------------------------------------------------------------------
-- A module for reasoning about the _≤_ and _<_ relations
------------------------------------------------------------------------

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    (resp₂ _<_)
    <⇒≤
    <-transˡ
    <-transʳ
    public
    hiding (_≈⟨_⟩_)

open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of pred
------------------------------------------------------------------------

pred-mono : pred Preserves _≤_ ⟶ _≤_
pred-mono z≤n      = z≤n
pred-mono (s≤s le) = le

≤pred⇒≤ : ∀ {m n} → m ≤ pred n → m ≤ n
≤pred⇒≤ {m} {zero}  le = le
≤pred⇒≤ {m} {suc n} le = ≤-step le

≤⇒pred≤ : ∀ {m n} → m ≤ n → pred m ≤ n
≤⇒pred≤ {zero}  le = le
≤⇒pred≤ {suc m} le = ≤-trans (n≤1+n m) le

<⇒≤pred : ∀ {m n} → m < n → m ≤ pred n
<⇒≤pred (s≤s le) = le

m≢0⇒suc[pred[m]]≡m : ∀ {m} → m ≢ 0 → suc (pred m) ≡ m
m≢0⇒suc[pred[m]]≡m {zero}  m≢0 = ⊥-elim (m≢0 refl)
m≢0⇒suc[pred[m]]≡m {suc m} m≢0 = refl

------------------------------------------------------------------------
-- Properties of _+_
------------------------------------------------------------------------

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

------------------------------------------------------------------------
-- Algebraic properties of _+_

+-assoc : Associative _+_
+-assoc zero    _ _ = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

+-identityˡ : LeftIdentity 0 _+_
+-identityˡ _ = refl

+-identityʳ : RightIdentity 0 _+_
+-identityʳ zero    = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

+-identity : Identity 0 _+_
+-identity = +-identityˡ , +-identityʳ

+-comm : Commutative _+_
+-comm zero    n = sym (+-identityʳ n)
+-comm (suc m) n = begin-equality
  suc m + n   ≡⟨⟩
  suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m) ≡⟨ sym (+-suc n m) ⟩
  n + suc m   ∎

+-cancelˡ-≡ : LeftCancellative _≡_ _+_
+-cancelˡ-≡ zero    eq = eq
+-cancelˡ-≡ (suc m) eq = +-cancelˡ-≡ m (cong pred eq)

+-cancelʳ-≡ : RightCancellative _≡_ _+_
+-cancelʳ-≡ = comm+cancelˡ⇒cancelʳ +-comm +-cancelˡ-≡

+-cancel-≡ : Cancellative _≡_ _+_
+-cancel-≡ = +-cancelˡ-≡ , +-cancelʳ-≡

------------------------------------------------------------------------
-- Structures

+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-0-isMonoid : IsMonoid _+_ 0
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0
+-0-isCommutativeMonoid = record
  { isSemigroup = +-isSemigroup
  ; identityˡ    = +-identityˡ
  ; comm        = +-comm
  }

------------------------------------------------------------------------
-- Packages

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

------------------------------------------------------------------------
-- Other properties of _+_ and _≡_

m≢1+m+n : ∀ m {n} → m ≢ suc (m + n)
m≢1+m+n (suc m) eq = m≢1+m+n m (cong pred eq)

m≢1+n+m : ∀ m {n} → m ≢ suc (n + m)
m≢1+n+m m m≡1+n+m = m≢1+m+n m (trans m≡1+n+m (cong suc (+-comm _ m)))

i+1+j≢i : ∀ i {j} → i + suc j ≢ i
i+1+j≢i (suc i) = (i+1+j≢i i) ∘ suc-injective

i+j≡0⇒i≡0 : ∀ i {j} → i + j ≡ 0 → i ≡ 0
i+j≡0⇒i≡0 zero    eq = refl

i+j≡0⇒j≡0 : ∀ i {j} → i + j ≡ 0 → j ≡ 0
i+j≡0⇒j≡0 i {j} i+j≡0 = i+j≡0⇒i≡0 j (trans (+-comm j i) (i+j≡0))

------------------------------------------------------------------------
-- Properties of _+_ and _≤_/_<_

+-cancelˡ-≤ : LeftCancellative _≤_ _+_
+-cancelˡ-≤ zero    le       = le
+-cancelˡ-≤ (suc m) (s≤s le) = +-cancelˡ-≤ m le

+-cancelʳ-≤ : RightCancellative _≤_ _+_
+-cancelʳ-≤ {m} n o le =
  +-cancelˡ-≤ m (subst₂ _≤_ (+-comm n m) (+-comm o m) le)

+-cancel-≤ : Cancellative _≤_ _+_
+-cancel-≤ = +-cancelˡ-≤ , +-cancelʳ-≤

+-cancelˡ-< : LeftCancellative _<_ _+_
+-cancelˡ-< x {y} {z} = +-cancelˡ-≤ x ∘ subst (_≤ x + z) (sym (+-suc x y))

+-cancelʳ-< : RightCancellative _<_ _+_
+-cancelʳ-< y z y+x<z+x = +-cancelʳ-≤ (suc y) z y+x<z+x

+-cancel-< : Cancellative _<_ _+_
+-cancel-< = +-cancelˡ-< , +-cancelʳ-<

≤-stepsˡ : ∀ {m n} o → m ≤ n → m ≤ o + n
≤-stepsˡ zero    m≤n = m≤n
≤-stepsˡ (suc o) m≤n = ≤-step (≤-stepsˡ o m≤n)

≤-stepsʳ : ∀ {m n} o → m ≤ n → m ≤ n + o
≤-stepsʳ {m} o m≤n = subst (m ≤_) (+-comm o _) (≤-stepsˡ o m≤n)

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero    n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)

n≤m+n : ∀ m n → n ≤ m + n
n≤m+n m zero    = z≤n
n≤m+n m (suc n) = subst (suc n ≤_) (sym (+-suc m n)) (s≤s (n≤m+n m n))

m+n≤o⇒m≤o : ∀ m {n o} → m + n ≤ o → m ≤ o
m+n≤o⇒m≤o zero    m+n≤o       = z≤n
m+n≤o⇒m≤o (suc m) (s≤s m+n≤o) = s≤s (m+n≤o⇒m≤o m m+n≤o)

m+n≤o⇒n≤o : ∀ m {n o} → m + n ≤ o → n ≤ o
m+n≤o⇒n≤o zero    n≤o   = n≤o
m+n≤o⇒n≤o (suc m) m+n<o = m+n≤o⇒n≤o m (<⇒≤ m+n<o)

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {_} {m} z≤n       o≤p = ≤-trans o≤p (n≤m+n m _)
+-mono-≤ {_} {_} (s≤s m≤n) o≤p = s≤s (+-mono-≤ m≤n o≤p)

+-monoˡ-≤ : ∀ n → (_+ n) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ n m≤o = +-mono-≤ m≤o (≤-refl {n})

+-monoʳ-≤ : ∀ n → (n +_) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ n m≤o = +-mono-≤ (≤-refl {n}) m≤o

+-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {_} {suc y} (s≤s z≤n)       u≤v = s≤s (≤-stepsˡ y u≤v)
+-mono-<-≤ {_} {_}     (s≤s (s≤s x<y)) u≤v = s≤s (+-mono-<-≤ (s≤s x<y) u≤v)

+-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {_} {y} z≤n       u<v = ≤-trans u<v (n≤m+n y _)
+-mono-≤-< {_} {_} (s≤s x≤y) u<v = s≤s (+-mono-≤-< x≤y u<v)

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< x≤y = +-mono-≤-< (<⇒≤ x≤y)

+-monoˡ-< : ∀ n → (_+ n) Preserves _<_ ⟶ _<_
+-monoˡ-< n = +-monoˡ-≤ n

+-monoʳ-< : ∀ n → (n +_) Preserves _<_ ⟶ _<_
+-monoʳ-< zero    m≤o = m≤o
+-monoʳ-< (suc n) m≤o = s≤s (+-monoʳ-< n m≤o)

i+1+j≰i : ∀ i {j} → i + suc j ≰ i
i+1+j≰i (suc i) le = i+1+j≰i i (≤-pred le)

m+n≮n : ∀ m n → m + n ≮ n
m+n≮n zero    n                   = n≮n n
m+n≮n (suc m) (suc n) (s≤s m+n<n) = m+n≮n m (suc n) (≤-step m+n<n)

m+n≮m : ∀ m n → m + n ≮ m
m+n≮m m n = subst (_≮ m) (+-comm n m) (m+n≮n n m)

------------------------------------------------------------------------
-- Properties of _*_
------------------------------------------------------------------------

+-*-suc : ∀ m n → m * suc n ≡ m + m * n
+-*-suc zero    n = refl
+-*-suc (suc m) n = begin-equality
  suc m * suc n         ≡⟨⟩
  suc n + m * suc n     ≡⟨ cong (suc n +_) (+-*-suc m n) ⟩
  suc n + (m + m * n)   ≡⟨⟩
  suc (n + (m + m * n)) ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
  suc (n + m + m * n)   ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m) ⟩
  suc (m + n + m * n)   ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
  suc (m + (n + m * n)) ≡⟨⟩
  suc m + suc m * n     ∎

------------------------------------------------------------------------
-- Algebraic properties of _*_

*-identityˡ : LeftIdentity 1 _*_
*-identityˡ x = +-identityʳ x

*-identityʳ : RightIdentity 1 _*_
*-identityʳ zero    = refl
*-identityʳ (suc x) = cong suc (*-identityʳ x)

*-identity : Identity 1 _*_
*-identity = *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero 0 _*_
*-zeroˡ _ = refl

*-zeroʳ : RightZero 0 _*_
*-zeroʳ zero    = refl
*-zeroʳ (suc n) = *-zeroʳ n

*-zero : Zero 0 _*_
*-zero = *-zeroˡ , *-zeroʳ

*-comm : Commutative _*_
*-comm zero    n = sym (*-zeroʳ n)
*-comm (suc m) n = begin-equality
  suc m * n  ≡⟨⟩
  n + m * n  ≡⟨ cong (n +_) (*-comm m n) ⟩
  n + n * m  ≡⟨ sym (+-*-suc n m) ⟩
  n * suc m  ∎

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ m zero    o = refl
*-distribʳ-+ m (suc n) o = begin-equality
  (suc n + o) * m     ≡⟨⟩
  m + (n + o) * m     ≡⟨ cong (m +_) (*-distribʳ-+ m n o) ⟩
  m + (n * m + o * m) ≡⟨ sym (+-assoc m (n * m) (o * m)) ⟩
  m + n * m + o * m   ≡⟨⟩
  suc n * m + o * m   ∎

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ = comm+distrʳ⇒distrˡ *-comm *-distribʳ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-assoc : Associative _*_
*-assoc zero    n o = refl
*-assoc (suc m) n o = begin-equality
  (suc m * n) * o     ≡⟨⟩
  (n + m * n) * o     ≡⟨ *-distribʳ-+ o n (m * n) ⟩
  n * o + (m * n) * o ≡⟨ cong (n * o +_) (*-assoc m n o) ⟩
  n * o + m * (n * o) ≡⟨⟩
  suc m * (n * o)     ∎

------------------------------------------------------------------------
-- Structures

*-isMagma : IsMagma _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _*_
  }

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-1-isMonoid : IsMonoid _*_ 1
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1
*-1-isCommutativeMonoid = record
  { isSemigroup = *-isSemigroup
  ; identityˡ    = *-identityˡ
  ; comm        = *-comm
  }

*-+-isSemiring : IsSemiring _+_ _*_ 0 1
*-+-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-0-isCommutativeMonoid
    ; *-isMonoid            = *-1-isMonoid
    ; distrib               = *-distrib-+
    }
  ; zero = *-zero
  }

*-+-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ 0 1
*-+-isCommutativeSemiring = record
  { +-isCommutativeMonoid = +-0-isCommutativeMonoid
  ; *-isCommutativeMonoid = *-1-isCommutativeMonoid
  ; distribʳ              = *-distribʳ-+
  ; zeroˡ                 = *-zeroˡ
  }

------------------------------------------------------------------------
-- Packages

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

*-+-semiring : Semiring 0ℓ 0ℓ
*-+-semiring = record
  { isSemiring = *-+-isSemiring
  }

*-+-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
*-+-commutativeSemiring = record
  { isCommutativeSemiring = *-+-isCommutativeSemiring
  }

------------------------------------------------------------------------
-- Other properties of _*_ and _≡_

*-cancelʳ-≡ : ∀ i j {k} → i * suc k ≡ j * suc k → i ≡ j
*-cancelʳ-≡ zero    zero        eq = refl
*-cancelʳ-≡ (suc i) (suc j) {k} eq =
  cong suc (*-cancelʳ-≡ i j (+-cancelˡ-≡ (suc k) eq))

*-cancelˡ-≡ : ∀ {i j} k → suc k * i ≡ suc k * j → i ≡ j
*-cancelˡ-≡ {i} {j} k eq = *-cancelʳ-≡ i j
  (subst₂ _≡_ (*-comm (suc k) i) (*-comm (suc k) j) eq)

i*j≡0⇒i≡0∨j≡0 : ∀ i {j} → i * j ≡ 0 → i ≡ 0 ⊎ j ≡ 0
i*j≡0⇒i≡0∨j≡0 zero    {j}     eq = inj₁ refl
i*j≡0⇒i≡0∨j≡0 (suc i) {zero}  eq = inj₂ refl

i*j≡1⇒i≡1 : ∀ i j → i * j ≡ 1 → i ≡ 1
i*j≡1⇒i≡1 (suc zero)    j             _  = refl
i*j≡1⇒i≡1 (suc (suc i)) (suc zero)    ()
i*j≡1⇒i≡1 (suc (suc i)) zero          eq =
  contradiction (trans (sym $ *-zeroʳ i) eq) λ()

i*j≡1⇒j≡1 : ∀ i j → i * j ≡ 1 → j ≡ 1
i*j≡1⇒j≡1 i j eq = i*j≡1⇒i≡1 j i (trans (*-comm j i) eq)

------------------------------------------------------------------------
-- Other properties of _*_ and _≤_/_<_

*-cancelʳ-≤ : ∀ i j k → i * suc k ≤ j * suc k → i ≤ j
*-cancelʳ-≤ zero    _       _ _  = z≤n
*-cancelʳ-≤ (suc i) (suc j) k le =
  s≤s (*-cancelʳ-≤ i j k (+-cancelˡ-≤ (suc k) le))

*-mono-≤ : _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
*-mono-≤ z≤n       _   = z≤n
*-mono-≤ (s≤s m≤n) u≤v = +-mono-≤ u≤v (*-mono-≤ m≤n u≤v)

*-monoˡ-≤ : ∀ n → (_* n) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤ n m≤o = *-mono-≤ m≤o (≤-refl {n})

*-monoʳ-≤ : ∀ n → (n *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤ n m≤o = *-mono-≤ (≤-refl {n}) m≤o

*-mono-< : _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
*-mono-< (s≤s z≤n)       (s≤s u≤v) = s≤s z≤n
*-mono-< (s≤s (s≤s m≤n)) (s≤s u≤v) =
  +-mono-< (s≤s u≤v) (*-mono-< (s≤s m≤n) (s≤s u≤v))

*-monoˡ-< : ∀ n → (_* suc n) Preserves _<_ ⟶ _<_
*-monoˡ-< n (s≤s z≤n)       = s≤s z≤n
*-monoˡ-< n (s≤s (s≤s m≤o)) =
  +-mono-≤-< (≤-refl {suc n}) (*-monoˡ-< n (s≤s m≤o))

*-monoʳ-< : ∀ n → (suc n *_) Preserves _<_ ⟶ _<_
*-monoʳ-< zero    (s≤s m≤o) = +-mono-≤ (s≤s m≤o) z≤n
*-monoʳ-< (suc n) (s≤s m≤o) =
  +-mono-≤ (s≤s m≤o) (<⇒≤ (*-monoʳ-< n (s≤s m≤o)))

m≤m*n : ∀ m {n} → 0 < n → m ≤ m * n
m≤m*n m {n} 0<n = begin
  m     ≡⟨ sym (*-identityʳ m) ⟩
  m * 1 ≤⟨ *-monoʳ-≤ m 0<n ⟩
  m * n ∎

m<m*n :  ∀ {m n} → 0 < m → 1 < n → m < m * n
m<m*n {suc m-1} {suc (suc n-2)} (s≤s _) (s≤s (s≤s _)) = begin-strict
  m           <⟨ s≤s (s≤s (n≤m+n n-2 m-1)) ⟩
  n + m-1     ≤⟨ +-monoʳ-≤ n (m≤m*n m-1 (s≤s z≤n)) ⟩
  n + m-1 * n ≡⟨⟩
  m * n       ∎
  where m = suc m-1; n = suc (suc n-2)

------------------------------------------------------------------------
-- Properties of _^_
------------------------------------------------------------------------

^-identityʳ : RightIdentity 1 _^_
^-identityʳ zero    = refl
^-identityʳ (suc x) = cong suc (^-identityʳ x)

^-zeroˡ : LeftZero 1 _^_
^-zeroˡ zero    = refl
^-zeroˡ (suc e) = begin-equality
  1 ^ suc e   ≡⟨⟩
  1 * (1 ^ e) ≡⟨ *-identityˡ (1 ^ e) ⟩
  1 ^ e       ≡⟨ ^-zeroˡ e ⟩
  1           ∎

^-distribˡ-+-* : ∀ m n p → m ^ (n + p) ≡ m ^ n * m ^ p
^-distribˡ-+-* m zero    p = sym (+-identityʳ (m ^ p))
^-distribˡ-+-* m (suc n) p = begin-equality
  m * (m ^ (n + p))       ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
  m * ((m ^ n) * (m ^ p)) ≡⟨ sym (*-assoc m _ _) ⟩
  (m * (m ^ n)) * (m ^ p) ∎

^-semigroup-morphism : ∀ {n} → (n ^_) Is +-semigroup -Semigroup⟶ *-semigroup
^-semigroup-morphism = record
  { ⟦⟧-cong = cong (_ ^_)
  ; ∙-homo  = ^-distribˡ-+-* _
  }

^-monoid-morphism : ∀ {n} → (n ^_) Is +-0-monoid -Monoid⟶ *-1-monoid
^-monoid-morphism = record
  { sm-homo = ^-semigroup-morphism
  ; ε-homo  = refl
  }

^-*-assoc : ∀ m n p → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero    = begin-equality
  1           ≡⟨⟩
  m ^ 0       ≡⟨ cong (m ^_) (sym $ *-zeroʳ n) ⟩
  m ^ (n * 0) ∎
^-*-assoc m n (suc p) = begin-equality
  (m ^ n) * ((m ^ n) ^ p) ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n p) ⟩
  (m ^ n) * (m ^ (n * p)) ≡⟨ sym (^-distribˡ-+-* m n (n * p)) ⟩
  m ^ (n + n * p)         ≡⟨ cong (m ^_) (sym (+-*-suc n p)) ⟩
  m ^ (n * (suc p)) ∎

i^j≡0⇒i≡0 : ∀ i j → i ^ j ≡ 0 → i ≡ 0
i^j≡0⇒i≡0 i (suc j) eq = [ id , i^j≡0⇒i≡0 i j ]′ (i*j≡0⇒i≡0∨j≡0 i eq)

i^j≡1⇒j≡0∨i≡1 : ∀ i j → i ^ j ≡ 1 → j ≡ 0 ⊎ i ≡ 1
i^j≡1⇒j≡0∨i≡1 i zero    _  = inj₁ refl
i^j≡1⇒j≡0∨i≡1 i (suc j) eq = inj₂ (i*j≡1⇒i≡1 i (i ^ j) eq)

------------------------------------------------------------------------
-- Properties of _≤‴_
------------------------------------------------------------------------

≤‴⇒≤″ : ∀{m n} → m ≤‴ n → m ≤″ n
≤‴⇒≤″ {m = m} ≤‴-refl     = less-than-or-equal {k = 0} (+-identityʳ m)
≤‴⇒≤″ {m = m} (≤‴-step x) = less-than-or-equal (trans (+-suc m _) (_≤″_.proof ind)) where
  ind = ≤‴⇒≤″ x

m≤‴m+k : ∀{m n k} → m + k ≡ n → m ≤‴ n
m≤‴m+k {m} {k = zero} refl = subst (λ z → m ≤‴ z) (sym (+-identityʳ m)) (≤‴-refl {m})
m≤‴m+k {m} {k = suc k} proof
  = ≤‴-step (m≤‴m+k {k = k} (trans (sym (+-suc m _)) proof))

≤″⇒≤‴ : ∀{m n} → m ≤″ n → m ≤‴ n
≤″⇒≤‴ (less-than-or-equal {k} proof) = m≤‴m+k proof

------------------------------------------------------------------------
-- Properties of _⊔_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties

⊔-assoc : Associative _⊔_
⊔-assoc zero    _       _       = refl
⊔-assoc (suc m) zero    o       = refl
⊔-assoc (suc m) (suc n) zero    = refl
⊔-assoc (suc m) (suc n) (suc o) = cong suc $ ⊔-assoc m n o

⊔-identityˡ : LeftIdentity 0 _⊔_
⊔-identityˡ _ = refl

⊔-identityʳ : RightIdentity 0 _⊔_
⊔-identityʳ zero    = refl
⊔-identityʳ (suc n) = refl

⊔-identity : Identity 0 _⊔_
⊔-identity = ⊔-identityˡ , ⊔-identityʳ

⊔-comm : Commutative _⊔_
⊔-comm zero    n       = sym $ ⊔-identityʳ n
⊔-comm (suc m) zero    = refl
⊔-comm (suc m) (suc n) = cong suc (⊔-comm m n)

⊔-sel : Selective _⊔_
⊔-sel zero    _    = inj₂ refl
⊔-sel (suc m) zero = inj₁ refl
⊔-sel (suc m) (suc n) with ⊔-sel m n
... | inj₁ m⊔n≡m = inj₁ (cong suc m⊔n≡m)
... | inj₂ m⊔n≡n = inj₂ (cong suc m⊔n≡n)

⊔-idem : Idempotent _⊔_
⊔-idem = sel⇒idem ⊔-sel

------------------------------------------------------------------------
-- Structures

⊔-isMagma : IsMagma _⊔_
⊔-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _⊔_
  }

⊔-isSemigroup : IsSemigroup _⊔_
⊔-isSemigroup = record
  { isMagma = ⊔-isMagma
  ; assoc   = ⊔-assoc
  }

⊔-isBand : IsBand _⊔_
⊔-isBand = record
  { isSemigroup = ⊔-isSemigroup
  ; idem        = ⊔-idem
  }

⊔-isSemilattice : IsSemilattice _⊔_
⊔-isSemilattice = record
  { isBand = ⊔-isBand
  ; comm   = ⊔-comm
  }

⊔-0-isCommutativeMonoid : IsCommutativeMonoid _⊔_ 0
⊔-0-isCommutativeMonoid = record
  { isSemigroup = ⊔-isSemigroup
  ; identityˡ   = ⊔-identityˡ
  ; comm        = ⊔-comm
  }

------------------------------------------------------------------------
-- Packages

⊔-magma : Magma 0ℓ 0ℓ
⊔-magma = record
  { isMagma = ⊔-isMagma
  }

⊔-semigroup : Semigroup 0ℓ 0ℓ
⊔-semigroup = record
  { isSemigroup = ⊔-isSemigroup
  }

⊔-band : Band 0ℓ 0ℓ
⊔-band = record
  { isBand = ⊔-isBand
  }

⊔-semilattice : Semilattice 0ℓ 0ℓ
⊔-semilattice = record
  { isSemilattice = ⊔-isSemilattice
  }

⊔-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
⊔-0-commutativeMonoid = record
  { isCommutativeMonoid = ⊔-0-isCommutativeMonoid
  }

------------------------------------------------------------------------
-- Other properties of _⊔_ and _≡_

⊔-triangulate : ∀ x y z → x ⊔ y ⊔ z ≡ (x ⊔ y) ⊔ (y ⊔ z)
⊔-triangulate x y z = begin-equality
  x ⊔ y ⊔ z           ≡⟨ cong (λ v → x ⊔ v ⊔ z) (sym (⊔-idem y)) ⟩
  x ⊔ (y ⊔ y) ⊔ z     ≡⟨ ⊔-assoc x _ _ ⟩
  x ⊔ ((y ⊔ y) ⊔ z)   ≡⟨ cong (x ⊔_) (⊔-assoc y _ _) ⟩
  x ⊔ (y ⊔ (y ⊔ z))   ≡⟨ sym (⊔-assoc x _ _) ⟩
  (x ⊔ y) ⊔ (y ⊔ z)   ∎

------------------------------------------------------------------------
-- Other properties of _⊔_ and _≤_/_<_

m≤m⊔n : ∀ m n → m ≤ m ⊔ n
m≤m⊔n zero    _       = z≤n
m≤m⊔n (suc m) zero    = ≤-refl
m≤m⊔n (suc m) (suc n) = s≤s $ m≤m⊔n m n

n≤m⊔n : ∀ m n → n ≤ m ⊔ n
n≤m⊔n m n = subst (n ≤_) (⊔-comm n m) (m≤m⊔n n m)

m≤n⇒n⊔m≡n : ∀ {m n} → m ≤ n → n ⊔ m ≡ n
m≤n⇒n⊔m≡n z≤n       = ⊔-identityʳ _
m≤n⇒n⊔m≡n (s≤s m≤n) = cong suc (m≤n⇒n⊔m≡n m≤n)

m≤n⇒m⊔n≡n : ∀ {m n} → m ≤ n → m ⊔ n ≡ n
m≤n⇒m⊔n≡n {m} m≤n = trans (⊔-comm m _) (m≤n⇒n⊔m≡n m≤n)

n⊔m≡m⇒n≤m : ∀ {m n} → n ⊔ m ≡ m → n ≤ m
n⊔m≡m⇒n≤m n⊔m≡m = subst (_ ≤_) n⊔m≡m (m≤m⊔n _ _)

n⊔m≡n⇒m≤n : ∀ {m n} → n ⊔ m ≡ n → m ≤ n
n⊔m≡n⇒m≤n n⊔m≡n = subst (_ ≤_) n⊔m≡n (n≤m⊔n _ _)

m≤n⇒m≤n⊔o : ∀ {m n} o → m ≤ n → m ≤ n ⊔ o
m≤n⇒m≤n⊔o o m≤n = ≤-trans m≤n (m≤m⊔n _ o)

m≤n⇒m≤o⊔n : ∀ {m n} o → m ≤ n → m ≤ o ⊔ n
m≤n⇒m≤o⊔n n m≤n = ≤-trans m≤n (n≤m⊔n n _)

m⊔n≤o⇒m≤o : ∀ m n {o} → m ⊔ n ≤ o → m ≤ o
m⊔n≤o⇒m≤o m n m⊔n≤o = ≤-trans (m≤m⊔n m n) m⊔n≤o

m⊔n≤o⇒n≤o : ∀ m n {o} → m ⊔ n ≤ o → n ≤ o
m⊔n≤o⇒n≤o m n m⊔n≤o = ≤-trans (n≤m⊔n m n) m⊔n≤o

m<n⇒m<n⊔o : ∀ {m n} o → m < n → m < n ⊔ o
m<n⇒m<n⊔o = m≤n⇒m≤n⊔o

m<n⇒m<o⊔n : ∀ {m n} o → m < n → m < o ⊔ n
m<n⇒m<o⊔n = m≤n⇒m≤o⊔n

m⊔n<o⇒m<o : ∀ m n {o} → m ⊔ n < o → m < o
m⊔n<o⇒m<o m n m⊔n<o = <-transʳ (m≤m⊔n m n) m⊔n<o

m⊔n<o⇒n<o : ∀ m n {o} → m ⊔ n < o → n < o
m⊔n<o⇒n<o m n m⊔n<o = <-transʳ (n≤m⊔n m n) m⊔n<o

⊔-mono-≤ : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
⊔-mono-≤ {x} {y} {u} {v} x≤y u≤v with ⊔-sel x u
... | inj₁ x⊔u≡x rewrite x⊔u≡x = ≤-trans x≤y (m≤m⊔n y v)
... | inj₂ x⊔u≡u rewrite x⊔u≡u = ≤-trans u≤v (n≤m⊔n y v)

⊔-monoˡ-≤ : ∀ n → (_⊔ n) Preserves _≤_ ⟶ _≤_
⊔-monoˡ-≤ n m≤o = ⊔-mono-≤ m≤o (≤-refl {n})

⊔-monoʳ-≤ : ∀ n → (n ⊔_) Preserves _≤_ ⟶ _≤_
⊔-monoʳ-≤ n m≤o = ⊔-mono-≤ (≤-refl {n}) m≤o

⊔-mono-< : _⊔_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
⊔-mono-< = ⊔-mono-≤

------------------------------------------------------------------------
-- Other properties of _⊔_ and _+_

+-distribˡ-⊔ : _+_ DistributesOverˡ _⊔_
+-distribˡ-⊔ zero    y z = refl
+-distribˡ-⊔ (suc x) y z = cong suc (+-distribˡ-⊔ x y z)

+-distribʳ-⊔ : _+_ DistributesOverʳ _⊔_
+-distribʳ-⊔ = comm+distrˡ⇒distrʳ +-comm +-distribˡ-⊔

+-distrib-⊔ : _+_ DistributesOver _⊔_
+-distrib-⊔ = +-distribˡ-⊔ , +-distribʳ-⊔

m⊔n≤m+n : ∀ m n → m ⊔ n ≤ m + n
m⊔n≤m+n m n with ⊔-sel m n
... | inj₁ m⊔n≡m rewrite m⊔n≡m = m≤m+n m n
... | inj₂ m⊔n≡n rewrite m⊔n≡n = n≤m+n m n

------------------------------------------------------------------------
-- Properties of _⊓_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties

⊓-assoc : Associative _⊓_
⊓-assoc zero    _       _       = refl
⊓-assoc (suc m) zero    o       = refl
⊓-assoc (suc m) (suc n) zero    = refl
⊓-assoc (suc m) (suc n) (suc o) = cong suc $ ⊓-assoc m n o

⊓-zeroˡ : LeftZero 0 _⊓_
⊓-zeroˡ _ = refl

⊓-zeroʳ : RightZero 0 _⊓_
⊓-zeroʳ zero    = refl
⊓-zeroʳ (suc n) = refl

⊓-zero : Zero 0 _⊓_
⊓-zero = ⊓-zeroˡ , ⊓-zeroʳ

⊓-comm : Commutative _⊓_
⊓-comm zero    n       = sym $ ⊓-zeroʳ n
⊓-comm (suc m) zero    = refl
⊓-comm (suc m) (suc n) = cong suc (⊓-comm m n)

⊓-sel : Selective _⊓_
⊓-sel zero    _    = inj₁ refl
⊓-sel (suc m) zero = inj₂ refl
⊓-sel (suc m) (suc n) with ⊓-sel m n
... | inj₁ m⊓n≡m = inj₁ (cong suc m⊓n≡m)
... | inj₂ m⊓n≡n = inj₂ (cong suc m⊓n≡n)

⊓-idem : Idempotent _⊓_
⊓-idem = sel⇒idem ⊓-sel

⊓-distribʳ-⊔ : _⊓_ DistributesOverʳ _⊔_
⊓-distribʳ-⊔ (suc m) (suc n) (suc o) = cong suc $ ⊓-distribʳ-⊔ m n o
⊓-distribʳ-⊔ (suc m) (suc n) zero    = cong suc $ refl
⊓-distribʳ-⊔ (suc m) zero    o       = refl
⊓-distribʳ-⊔ zero    n       o       = begin-equality
  (n ⊔ o) ⊓ 0    ≡⟨ ⊓-comm (n ⊔ o) 0 ⟩
  0 ⊓ (n ⊔ o)    ≡⟨⟩
  0 ⊓ n ⊔ 0 ⊓ o  ≡⟨ ⊓-comm 0 n ⟨ cong₂ _⊔_ ⟩ ⊓-comm 0 o ⟩
  n ⊓ 0 ⊔ o ⊓ 0  ∎

⊓-distribˡ-⊔ : _⊓_ DistributesOverˡ _⊔_
⊓-distribˡ-⊔ = comm+distrʳ⇒distrˡ ⊓-comm ⊓-distribʳ-⊔

⊓-distrib-⊔ : _⊓_ DistributesOver _⊔_
⊓-distrib-⊔ = ⊓-distribˡ-⊔ , ⊓-distribʳ-⊔

⊔-abs-⊓ : _⊔_ Absorbs _⊓_
⊔-abs-⊓ zero    n       = refl
⊔-abs-⊓ (suc m) zero    = refl
⊔-abs-⊓ (suc m) (suc n) = cong suc $ ⊔-abs-⊓ m n

⊓-abs-⊔ : _⊓_ Absorbs _⊔_
⊓-abs-⊔ zero    n       = refl
⊓-abs-⊔ (suc m) (suc n) = cong suc $ ⊓-abs-⊔ m n
⊓-abs-⊔ (suc m) zero    = cong suc $ begin-equality
  m ⊓ m       ≡⟨ cong (m ⊓_) $ sym $ ⊔-identityʳ m ⟩
  m ⊓ (m ⊔ 0) ≡⟨ ⊓-abs-⊔ m zero ⟩
  m           ∎

⊓-⊔-absorptive : Absorptive _⊓_ _⊔_
⊓-⊔-absorptive = ⊓-abs-⊔ , ⊔-abs-⊓

------------------------------------------------------------------------
-- Structures

⊓-isMagma : IsMagma _⊓_
⊓-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _⊓_
  }

⊓-isSemigroup : IsSemigroup _⊓_
⊓-isSemigroup = record
  { isMagma = ⊓-isMagma
  ; assoc   = ⊓-assoc
  }

⊓-isBand : IsBand _⊓_
⊓-isBand = record
  { isSemigroup = ⊓-isSemigroup
  ; idem        = ⊓-idem
  }

⊓-isSemilattice : IsSemilattice _⊓_
⊓-isSemilattice = record
  { isBand = ⊓-isBand
  ; comm   = ⊓-comm
  }

⊔-⊓-isSemiringWithoutOne : IsSemiringWithoutOne _⊔_ _⊓_ 0
⊔-⊓-isSemiringWithoutOne = record
  { +-isCommutativeMonoid = ⊔-0-isCommutativeMonoid
  ; *-isSemigroup         = ⊓-isSemigroup
  ; distrib               = ⊓-distrib-⊔
  ; zero                  = ⊓-zero
  }

⊔-⊓-isCommutativeSemiringWithoutOne
  : IsCommutativeSemiringWithoutOne _⊔_ _⊓_ 0
⊔-⊓-isCommutativeSemiringWithoutOne = record
  { isSemiringWithoutOne = ⊔-⊓-isSemiringWithoutOne
  ; *-comm               = ⊓-comm
  }

⊓-⊔-isLattice : IsLattice _⊓_ _⊔_
⊓-⊔-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = ⊓-comm
  ; ∨-assoc       = ⊓-assoc
  ; ∨-cong        = cong₂ _⊓_
  ; ∧-comm        = ⊔-comm
  ; ∧-assoc       = ⊔-assoc
  ; ∧-cong        = cong₂ _⊔_
  ; absorptive    = ⊓-⊔-absorptive
  }

⊓-⊔-isDistributiveLattice : IsDistributiveLattice _⊓_ _⊔_
⊓-⊔-isDistributiveLattice = record
  { isLattice    = ⊓-⊔-isLattice
  ; ∨-∧-distribʳ = ⊓-distribʳ-⊔
  }

------------------------------------------------------------------------
-- Packages

⊓-magma : Magma 0ℓ 0ℓ
⊓-magma = record
  { isMagma = ⊓-isMagma
  }

⊓-semigroup : Semigroup 0ℓ 0ℓ
⊓-semigroup = record
  { isSemigroup = ⊔-isSemigroup
  }

⊓-band : Band 0ℓ 0ℓ
⊓-band = record
  { isBand = ⊓-isBand
  }

⊓-semilattice : Semilattice 0ℓ 0ℓ
⊓-semilattice = record
  { isSemilattice = ⊓-isSemilattice
  }

⊔-⊓-commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne 0ℓ 0ℓ
⊔-⊓-commutativeSemiringWithoutOne = record
  { isCommutativeSemiringWithoutOne =
      ⊔-⊓-isCommutativeSemiringWithoutOne
  }

⊓-⊔-lattice : Lattice 0ℓ 0ℓ
⊓-⊔-lattice = record
  { isLattice = ⊓-⊔-isLattice
  }

⊓-⊔-distributiveLattice : DistributiveLattice 0ℓ 0ℓ
⊓-⊔-distributiveLattice = record
  { isDistributiveLattice = ⊓-⊔-isDistributiveLattice
  }

------------------------------------------------------------------------
-- Other properties of _⊓_ and _≡_

⊓-triangulate : ∀ x y z → x ⊓ y ⊓ z ≡ (x ⊓ y) ⊓ (y ⊓ z)
⊓-triangulate x y z = begin-equality
  x ⊓ y ⊓ z           ≡⟨ sym (cong (λ v → x ⊓ v ⊓ z) (⊓-idem y)) ⟩
  x ⊓ (y ⊓ y) ⊓ z     ≡⟨ ⊓-assoc x _ _ ⟩
  x ⊓ ((y ⊓ y) ⊓ z)   ≡⟨ cong (x ⊓_) (⊓-assoc y _ _) ⟩
  x ⊓ (y ⊓ (y ⊓ z))   ≡⟨ sym (⊓-assoc x _ _) ⟩
  (x ⊓ y) ⊓ (y ⊓ z)   ∎

------------------------------------------------------------------------
-- Other properties of _⊓_ and _≤_/_<_

m⊓n≤m : ∀ m n → m ⊓ n ≤ m
m⊓n≤m zero    _       = z≤n
m⊓n≤m (suc m) zero    = z≤n
m⊓n≤m (suc m) (suc n) = s≤s $ m⊓n≤m m n

m⊓n≤n : ∀ m n → m ⊓ n ≤ n
m⊓n≤n m n = subst (_≤ n) (⊓-comm n m) (m⊓n≤m n m)

m≤n⇒m⊓n≡m : ∀ {m n} → m ≤ n → m ⊓ n ≡ m
m≤n⇒m⊓n≡m z≤n       = refl
m≤n⇒m⊓n≡m (s≤s m≤n) = cong suc (m≤n⇒m⊓n≡m m≤n)

m≤n⇒n⊓m≡m : ∀ {m n} → m ≤ n → n ⊓ m ≡ m
m≤n⇒n⊓m≡m {m} m≤n = trans (⊓-comm _ m) (m≤n⇒m⊓n≡m m≤n)

m⊓n≡m⇒m≤n : ∀ {m n} → m ⊓ n ≡ m → m ≤ n
m⊓n≡m⇒m≤n m⊓n≡m = subst (_≤ _) m⊓n≡m (m⊓n≤n _ _)

m⊓n≡n⇒n≤m : ∀ {m n} → m ⊓ n ≡ n → n ≤ m
m⊓n≡n⇒n≤m m⊓n≡n = subst (_≤ _) m⊓n≡n (m⊓n≤m _ _)

m≤n⇒m⊓o≤n : ∀ {m n} o → m ≤ n → m ⊓ o ≤ n
m≤n⇒m⊓o≤n o m≤n = ≤-trans (m⊓n≤m _ o) m≤n

m≤n⇒o⊓m≤n : ∀ {m n} o → m ≤ n → o ⊓ m ≤ n
m≤n⇒o⊓m≤n n m≤n = ≤-trans (m⊓n≤n n _) m≤n

m≤n⊓o⇒m≤n : ∀ {m} n o → m ≤ n ⊓ o → m ≤ n
m≤n⊓o⇒m≤n n o m≤n⊓o = ≤-trans m≤n⊓o (m⊓n≤m n o)

m≤n⊓o⇒m≤o : ∀ {m} n o → m ≤ n ⊓ o → m ≤ o
m≤n⊓o⇒m≤o n o m≤n⊓o = ≤-trans m≤n⊓o (m⊓n≤n n o)

m<n⇒m⊓o<n : ∀ {m n} o → m < n → m ⊓ o < n
m<n⇒m⊓o<n o m<n = <-transʳ (m⊓n≤m _ o) m<n

m<n⇒o⊓m<n : ∀ {m n} o → m < n → o ⊓ m < n
m<n⇒o⊓m<n o m<n = <-transʳ (m⊓n≤n o _) m<n

m<n⊓o⇒m<n : ∀ {m} n o → m < n ⊓ o → m < n
m<n⊓o⇒m<n = m≤n⊓o⇒m≤n

m<n⊓o⇒m<o : ∀ {m} n o → m < n ⊓ o → m < o
m<n⊓o⇒m<o = m≤n⊓o⇒m≤o

⊓-mono-≤ : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
⊓-mono-≤ {x} {y} {u} {v} x≤y u≤v with ⊓-sel y v
... | inj₁ y⊓v≡y rewrite y⊓v≡y = ≤-trans (m⊓n≤m x u) x≤y
... | inj₂ y⊓v≡v rewrite y⊓v≡v = ≤-trans (m⊓n≤n x u) u≤v

⊓-monoˡ-≤ : ∀ n → (_⊓ n) Preserves _≤_ ⟶ _≤_
⊓-monoˡ-≤ n m≤o = ⊓-mono-≤ m≤o (≤-refl {n})

⊓-monoʳ-≤ : ∀ n → (n ⊓_) Preserves _≤_ ⟶ _≤_
⊓-monoʳ-≤ n m≤o = ⊓-mono-≤ (≤-refl {n}) m≤o

⊓-mono-< : _⊓_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
⊓-mono-< = ⊓-mono-≤

m⊓n≤m⊔n : ∀ m n → m ⊓ n ≤ m ⊔ n
m⊓n≤m⊔n zero    n       = z≤n
m⊓n≤m⊔n (suc m) zero    = z≤n
m⊓n≤m⊔n (suc m) (suc n) = s≤s (m⊓n≤m⊔n m n)

------------------------------------------------------------------------
-- Other properties of _⊓_ and _+_

+-distribˡ-⊓ : _+_ DistributesOverˡ _⊓_
+-distribˡ-⊓ zero    y z = refl
+-distribˡ-⊓ (suc x) y z = cong suc (+-distribˡ-⊓ x y z)

+-distribʳ-⊓ : _+_ DistributesOverʳ _⊓_
+-distribʳ-⊓ = comm+distrˡ⇒distrʳ +-comm +-distribˡ-⊓

+-distrib-⊓ : _+_ DistributesOver _⊓_
+-distrib-⊓ = +-distribˡ-⊓ , +-distribʳ-⊓

m⊓n≤m+n : ∀ m n → m ⊓ n ≤ m + n
m⊓n≤m+n m n with ⊓-sel m n
... | inj₁ m⊓n≡m rewrite m⊓n≡m = m≤m+n m n
... | inj₂ m⊓n≡n rewrite m⊓n≡n = n≤m+n m n

------------------------------------------------------------------------
-- Properties of _∸_
------------------------------------------------------------------------

0∸n≡0 : LeftZero zero _∸_
0∸n≡0 zero    = refl
0∸n≡0 (suc _) = refl

n∸n≡0 : ∀ n → n ∸ n ≡ 0
n∸n≡0 zero    = refl
n∸n≡0 (suc n) = n∸n≡0 n

------------------------------------------------------------------------
-- Properties of _∸_ and _≤_/_<_

n∸m≤n : ∀ m n → n ∸ m ≤ n
n∸m≤n zero    n       = ≤-refl
n∸m≤n (suc m) zero    = ≤-refl
n∸m≤n (suc m) (suc n) = ≤-trans (n∸m≤n m n) (n≤1+n n)

m≮m∸n : ∀ m n → m ≮ m ∸ n
m≮m∸n m       zero    = n≮n m
m≮m∸n (suc m) (suc n) = m≮m∸n m n ∘ ≤-trans (n≤1+n (suc m))

∸-mono : _∸_ Preserves₂ _≤_ ⟶ _≥_ ⟶ _≤_
∸-mono z≤n         (s≤s n₁≥n₂)    = z≤n
∸-mono (s≤s m₁≤m₂) (s≤s n₁≥n₂)    = ∸-mono m₁≤m₂ n₁≥n₂
∸-mono m₁≤m₂       (z≤n {n = n₁}) = ≤-trans (n∸m≤n n₁ _) m₁≤m₂

∸-monoˡ-≤ : ∀ {m n} o → m ≤ n → m ∸ o ≤ n ∸ o
∸-monoˡ-≤ o m≤n = ∸-mono {u = o} m≤n ≤-refl

∸-monoʳ-≤ : ∀ {m n} o → m ≤ n → o ∸ m ≥ o ∸ n
∸-monoʳ-≤ _ m≤n = ∸-mono ≤-refl m≤n

m∸n≡0⇒m≤n : ∀ {m n} → m ∸ n ≡ 0 → m ≤ n
m∸n≡0⇒m≤n {zero}  {_}    _   = z≤n
m∸n≡0⇒m≤n {suc m} {suc n} eq = s≤s (m∸n≡0⇒m≤n eq)

m≤n⇒m∸n≡0 : ∀ {m n} → m ≤ n → m ∸ n ≡ 0
m≤n⇒m∸n≡0 {n = n} z≤n      = 0∸n≡0 n
m≤n⇒m∸n≡0 {_}    (s≤s m≤n) = m≤n⇒m∸n≡0 m≤n

m∸n≢0⇒n<m : ∀ {m n} → m ∸ n ≢ 0 → n < m
m∸n≢0⇒n<m {m} {n} m∸n≢0 with n <? m
... | yes n<m = n<m
... | no  n≮m = contradiction (m≤n⇒m∸n≡0 (≮⇒≥ n≮m)) m∸n≢0

---------------------------------------------------------------
-- Properties of _∸_ and _+_

+-∸-comm : ∀ {m} n {o} → o ≤ m → (m + n) ∸ o ≡ (m ∸ o) + n
+-∸-comm {zero}  _ {zero}  _         = refl
+-∸-comm {suc m} _ {zero}  _         = refl
+-∸-comm {suc m} n {suc o} (s≤s o≤m) = +-∸-comm n o≤m

∸-+-assoc : ∀ m n o → (m ∸ n) ∸ o ≡ m ∸ (n + o)
∸-+-assoc m       n       zero    = cong (m ∸_) (sym $ +-identityʳ n)
∸-+-assoc zero    zero    (suc o) = refl
∸-+-assoc zero    (suc n) (suc o) = refl
∸-+-assoc (suc m) zero    (suc o) = refl
∸-+-assoc (suc m) (suc n) (suc o) = ∸-+-assoc m n (suc o)

+-∸-assoc : ∀ m {n o} → o ≤ n → (m + n) ∸ o ≡ m + (n ∸ o)
+-∸-assoc m (z≤n {n = n})             = begin-equality m + n ∎
+-∸-assoc m (s≤s {m = o} {n = n} o≤n) = begin-equality
  (m + suc n) ∸ suc o  ≡⟨ cong (_∸ suc o) (+-suc m n) ⟩
  suc (m + n) ∸ suc o  ≡⟨⟩
  (m + n) ∸ o          ≡⟨ +-∸-assoc m o≤n ⟩
  m + (n ∸ o)          ∎

n≤m+n∸m : ∀ m n → n ≤ m + (n ∸ m)
n≤m+n∸m m       zero    = z≤n
n≤m+n∸m zero    (suc n) = ≤-refl
n≤m+n∸m (suc m) (suc n) = s≤s (n≤m+n∸m m n)

m+n∸n≡m : ∀ m n → (m + n) ∸ n ≡ m
m+n∸n≡m m n = begin-equality
  (m + n) ∸ n  ≡⟨ +-∸-assoc m (≤-refl {x = n}) ⟩
  m + (n ∸ n)  ≡⟨ cong (m +_) (n∸n≡0 n) ⟩
  m + 0        ≡⟨ +-identityʳ m ⟩
  m            ∎

m+n∸m≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
m+n∸m≡n {m} {n} m≤n = begin-equality
  m + (n ∸ m)  ≡⟨ sym $ +-∸-assoc m m≤n ⟩
  (m + n) ∸ m  ≡⟨ cong (_∸ m) (+-comm m n) ⟩
  (n + m) ∸ m  ≡⟨ m+n∸n≡m n m ⟩
  n            ∎

m∸n+n≡m : ∀ {m n} → n ≤ m → (m ∸ n) + n ≡ m
m∸n+n≡m {m} {n} n≤m = begin-equality
  (m ∸ n) + n ≡⟨ sym (+-∸-comm n n≤m) ⟩
  (m + n) ∸ n ≡⟨ m+n∸n≡m m n ⟩
  m           ∎

m∸[m∸n]≡n : ∀ {m n} → n ≤ m → m ∸ (m ∸ n) ≡ n
m∸[m∸n]≡n {m}     {_}     z≤n       = n∸n≡0 m
m∸[m∸n]≡n {suc m} {suc n} (s≤s n≤m) = begin-equality
  suc m ∸ (m ∸ n)   ≡⟨ +-∸-assoc 1 (n∸m≤n n m) ⟩
  suc (m ∸ (m ∸ n)) ≡⟨ cong suc (m∸[m∸n]≡n n≤m) ⟩
  suc n             ∎

[i+j]∸[i+k]≡j∸k : ∀ i j k → (i + j) ∸ (i + k) ≡ j ∸ k
[i+j]∸[i+k]≡j∸k zero    j k = refl
[i+j]∸[i+k]≡j∸k (suc i) j k = [i+j]∸[i+k]≡j∸k i j k

------------------------------------------------------------------------
-- Properties of _∸_ and _*_

*-distribʳ-∸ : _*_ DistributesOverʳ _∸_
*-distribʳ-∸ i       zero    zero    = refl
*-distribʳ-∸ zero    zero    (suc k) = sym (0∸n≡0 (k * zero))
*-distribʳ-∸ (suc i) zero    (suc k) = refl
*-distribʳ-∸ i       (suc j) zero    = refl
*-distribʳ-∸ i       (suc j) (suc k) = begin-equality
  (j ∸ k) * i             ≡⟨ *-distribʳ-∸ i j k ⟩
  j * i ∸ k * i           ≡⟨ sym $ [i+j]∸[i+k]≡j∸k i _ _ ⟩
  i + j * i ∸ (i + k * i) ∎

*-distribˡ-∸ : _*_ DistributesOverˡ _∸_
*-distribˡ-∸ = comm+distrʳ⇒distrˡ *-comm *-distribʳ-∸

*-distrib-∸ : _*_ DistributesOver _∸_
*-distrib-∸ = *-distribˡ-∸ , *-distribʳ-∸

------------------------------------------------------------------------
-- Properties of _∸_ and _⊓_ and _⊔_

m⊓n+n∸m≡n : ∀ m n → (m ⊓ n) + (n ∸ m) ≡ n
m⊓n+n∸m≡n zero    n       = refl
m⊓n+n∸m≡n (suc m) zero    = refl
m⊓n+n∸m≡n (suc m) (suc n) = cong suc $ m⊓n+n∸m≡n m n

[m∸n]⊓[n∸m]≡0 : ∀ m n → (m ∸ n) ⊓ (n ∸ m) ≡ 0
[m∸n]⊓[n∸m]≡0 zero zero       = refl
[m∸n]⊓[n∸m]≡0 zero (suc n)    = refl
[m∸n]⊓[n∸m]≡0 (suc m) zero    = refl
[m∸n]⊓[n∸m]≡0 (suc m) (suc n) = [m∸n]⊓[n∸m]≡0 m n

∸-distribˡ-⊓-⊔ : ∀ x y z → x ∸ (y ⊓ z) ≡ (x ∸ y) ⊔ (x ∸ z)
∸-distribˡ-⊓-⊔ x       zero    zero    = sym (⊔-idem x)
∸-distribˡ-⊓-⊔ zero    zero    (suc z) = refl
∸-distribˡ-⊓-⊔ zero    (suc y) zero    = refl
∸-distribˡ-⊓-⊔ zero    (suc y) (suc z) = refl
∸-distribˡ-⊓-⊔ (suc x) (suc y) zero    = sym (m≤n⇒m⊔n≡n (≤-step (n∸m≤n y x)))
∸-distribˡ-⊓-⊔ (suc x) zero    (suc z) = sym (m≤n⇒n⊔m≡n (≤-step (n∸m≤n z x)))
∸-distribˡ-⊓-⊔ (suc x) (suc y) (suc z) = ∸-distribˡ-⊓-⊔ x y z

∸-distribʳ-⊓ : _∸_ DistributesOverʳ _⊓_
∸-distribʳ-⊓ zero    y       z       = refl
∸-distribʳ-⊓ (suc x) zero    z       = refl
∸-distribʳ-⊓ (suc x) (suc y) zero    = sym (⊓-zeroʳ (y ∸ x))
∸-distribʳ-⊓ (suc x) (suc y) (suc z) = ∸-distribʳ-⊓ x y z

∸-distribˡ-⊔-⊓ : ∀ x y z → x ∸ (y ⊔ z) ≡ (x ∸ y) ⊓ (x ∸ z)
∸-distribˡ-⊔-⊓ x       zero    zero    = sym (⊓-idem x)
∸-distribˡ-⊔-⊓ zero    zero    z       = 0∸n≡0 z
∸-distribˡ-⊔-⊓ zero    (suc y) z       = 0∸n≡0 (suc y ⊔ z)
∸-distribˡ-⊔-⊓ (suc x) (suc y) zero    = sym (m≤n⇒m⊓n≡m (≤-step (n∸m≤n y x)))
∸-distribˡ-⊔-⊓ (suc x) zero    (suc z) = sym (m≤n⇒n⊓m≡m (≤-step (n∸m≤n z x)))
∸-distribˡ-⊔-⊓ (suc x) (suc y) (suc z) = ∸-distribˡ-⊔-⊓ x y z

∸-distribʳ-⊔ : _∸_ DistributesOverʳ _⊔_
∸-distribʳ-⊔ zero    y       z       = refl
∸-distribʳ-⊔ (suc x) zero    z       = refl
∸-distribʳ-⊔ (suc x) (suc y) zero    = sym (⊔-identityʳ (y ∸ x))
∸-distribʳ-⊔ (suc x) (suc y) (suc z) = ∸-distribʳ-⊔ x y z

------------------------------------------------------------------------
-- Properties of ∣_-_∣
------------------------------------------------------------------------

n≡m⇒∣n-m∣≡0 : ∀ {n m} → n ≡ m → ∣ n - m ∣ ≡ 0
n≡m⇒∣n-m∣≡0 {zero}  refl = refl
n≡m⇒∣n-m∣≡0 {suc n} refl = n≡m⇒∣n-m∣≡0 {n} refl

m≤n⇒∣n-m∣≡n∸m : ∀ {n m} → m ≤ n → ∣ n - m ∣ ≡ n ∸ m
m≤n⇒∣n-m∣≡n∸m {zero}  z≤n       = refl
m≤n⇒∣n-m∣≡n∸m {suc n} z≤n       = refl
m≤n⇒∣n-m∣≡n∸m         (s≤s m≤n) = m≤n⇒∣n-m∣≡n∸m m≤n

∣n-m∣≡0⇒n≡m : ∀ {n m} → ∣ n - m ∣ ≡ 0 → n ≡ m
∣n-m∣≡0⇒n≡m {zero}  {zero}  eq = refl
∣n-m∣≡0⇒n≡m {suc n} {suc m} eq = cong suc (∣n-m∣≡0⇒n≡m eq)

∣n-m∣≡n∸m⇒m≤n : ∀ {n m} → ∣ n - m ∣ ≡ n ∸ m → m ≤ n
∣n-m∣≡n∸m⇒m≤n {zero}  {zero}  eq = z≤n
∣n-m∣≡n∸m⇒m≤n {suc n} {zero}  eq = z≤n
∣n-m∣≡n∸m⇒m≤n {suc n} {suc m} eq = s≤s (∣n-m∣≡n∸m⇒m≤n eq)

∣n-n∣≡0 : ∀ n → ∣ n - n ∣ ≡ 0
∣n-n∣≡0 n = n≡m⇒∣n-m∣≡0 {n} refl

∣n-n+m∣≡m : ∀ n m → ∣ n - n + m ∣ ≡ m
∣n-n+m∣≡m zero    m = refl
∣n-n+m∣≡m (suc n) m = ∣n-n+m∣≡m n m

∣n+m-n+o∣≡∣m-o| : ∀ n m o → ∣ n + m - n + o ∣ ≡ ∣ m - o ∣
∣n+m-n+o∣≡∣m-o| zero    m o = refl
∣n+m-n+o∣≡∣m-o| (suc n) m o = ∣n+m-n+o∣≡∣m-o| n m o

n∸m≤∣n-m∣ : ∀ n m → n ∸ m ≤ ∣ n - m ∣
n∸m≤∣n-m∣ n m with ≤-total m n
... | inj₁ m≤n = subst (n ∸ m ≤_) (sym (m≤n⇒∣n-m∣≡n∸m m≤n)) ≤-refl
... | inj₂ n≤m = subst (_≤ ∣ n - m ∣) (sym (m≤n⇒m∸n≡0 n≤m)) z≤n

∣n-m∣≤n⊔m : ∀ n m → ∣ n - m ∣ ≤ n ⊔ m
∣n-m∣≤n⊔m zero    m       = ≤-refl
∣n-m∣≤n⊔m (suc n) zero    = ≤-refl
∣n-m∣≤n⊔m (suc n) (suc m) = ≤-step (∣n-m∣≤n⊔m n m)

∣-∣-comm : Commutative ∣_-_∣
∣-∣-comm zero    zero    = refl
∣-∣-comm zero    (suc m) = refl
∣-∣-comm (suc n) zero    = refl
∣-∣-comm (suc n) (suc m) = ∣-∣-comm n m

∣n-m∣≡[n∸m]∨[m∸n] : ∀ m n → (∣ n - m ∣ ≡ n ∸ m) ⊎ (∣ n - m ∣ ≡ m ∸ n)
∣n-m∣≡[n∸m]∨[m∸n] m n with ≤-total m n
... | inj₁ m≤n = inj₁ $ m≤n⇒∣n-m∣≡n∸m m≤n
... | inj₂ n≤m = inj₂ $ begin-equality
  ∣ n - m ∣ ≡⟨ ∣-∣-comm n m ⟩
  ∣ m - n ∣ ≡⟨ m≤n⇒∣n-m∣≡n∸m n≤m ⟩
  m ∸ n     ∎

private

  *-distribˡ-∣-∣-aux : ∀ a m n → m ≤ n → a * ∣ n - m ∣ ≡ ∣ a * n - a * m ∣
  *-distribˡ-∣-∣-aux a m n m≤n = begin-equality
    a * ∣ n - m ∣     ≡⟨ cong (a *_) (m≤n⇒∣n-m∣≡n∸m m≤n) ⟩
    a * (n ∸ m)       ≡⟨ *-distribˡ-∸ a n m ⟩
    a * n ∸ a * m     ≡⟨ sym $′ m≤n⇒∣n-m∣≡n∸m (*-monoʳ-≤ a m≤n) ⟩
    ∣ a * n - a * m ∣ ∎

*-distribˡ-∣-∣ : _*_ DistributesOverˡ ∣_-_∣
*-distribˡ-∣-∣ a m n with ≤-total m n
... | inj₁ m≤n = begin-equality
  a * ∣ m - n ∣     ≡⟨ cong (a *_) (∣-∣-comm m n) ⟩
  a * ∣ n - m ∣     ≡⟨ *-distribˡ-∣-∣-aux a m n m≤n ⟩
  ∣ a * n - a * m ∣ ≡⟨ ∣-∣-comm (a * n) (a * m) ⟩
  ∣ a * m - a * n ∣ ∎
... | inj₂ n≤m = *-distribˡ-∣-∣-aux a n m n≤m

*-distribʳ-∣-∣ : _*_ DistributesOverʳ ∣_-_∣
*-distribʳ-∣-∣ = comm+distrˡ⇒distrʳ *-comm *-distribˡ-∣-∣

*-distrib-∣-∣ : _*_ DistributesOver ∣_-_∣
*-distrib-∣-∣ = *-distribˡ-∣-∣ , *-distribʳ-∣-∣

------------------------------------------------------------------------
-- Properties of ⌊_/2⌋
------------------------------------------------------------------------

⌊n/2⌋-mono : ⌊_/2⌋ Preserves _≤_ ⟶ _≤_
⌊n/2⌋-mono z≤n             = z≤n
⌊n/2⌋-mono (s≤s z≤n)       = z≤n
⌊n/2⌋-mono (s≤s (s≤s m≤n)) = s≤s (⌊n/2⌋-mono m≤n)

⌈n/2⌉-mono : ⌈_/2⌉ Preserves _≤_ ⟶ _≤_
⌈n/2⌉-mono m≤n = ⌊n/2⌋-mono (s≤s m≤n)

------------------------------------------------------------------------
-- Properties of _≤′_ and _<′_
------------------------------------------------------------------------

≤′-trans : Transitive _≤′_
≤′-trans m≤n ≤′-refl       = m≤n
≤′-trans m≤n (≤′-step n≤o) = ≤′-step (≤′-trans m≤n n≤o)

z≤′n : ∀ {n} → zero ≤′ n
z≤′n {zero}  = ≤′-refl
z≤′n {suc n} = ≤′-step z≤′n

s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤′s ≤′-refl        = ≤′-refl
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

≤′⇒≤ : _≤′_ ⇒ _≤_
≤′⇒≤ ≤′-refl        = ≤-refl
≤′⇒≤ (≤′-step m≤′n) = ≤-step (≤′⇒≤ m≤′n)

≤⇒≤′ : _≤_ ⇒ _≤′_
≤⇒≤′ z≤n       = z≤′n
≤⇒≤′ (s≤s m≤n) = s≤′s (≤⇒≤′ m≤n)

≤′-step-injective : ∀ {m n} {p q : m ≤′ n} → ≤′-step p ≡ ≤′-step q → p ≡ q
≤′-step-injective refl = refl

infix 4 _≤′?_ _<′?_ _≥′?_ _>′?_

_≤′?_ : Decidable _≤′_
x ≤′? y = map′ ≤⇒≤′ ≤′⇒≤ (x ≤? y)

_<′?_ : Decidable _<′_
x <′? y = suc x ≤′? y

_≥′?_ : Decidable _≥′_
_≥′?_ = flip _≤′?_

_>′?_ : Decidable _>′_
_>′?_ = flip _<′?_

m≤′m+n : ∀ m n → m ≤′ m + n
m≤′m+n m n = ≤⇒≤′ (m≤m+n m n)

n≤′m+n : ∀ m n → n ≤′ m + n
n≤′m+n zero    n = ≤′-refl
n≤′m+n (suc m) n = ≤′-step (n≤′m+n m n)

⌈n/2⌉≤′n : ∀ n → ⌈ n /2⌉ ≤′ n
⌈n/2⌉≤′n zero          = ≤′-refl
⌈n/2⌉≤′n (suc zero)    = ≤′-refl
⌈n/2⌉≤′n (suc (suc n)) = s≤′s (≤′-step (⌈n/2⌉≤′n n))

⌊n/2⌋≤′n : ∀ n → ⌊ n /2⌋ ≤′ n
⌊n/2⌋≤′n zero    = ≤′-refl
⌊n/2⌋≤′n (suc n) = ≤′-step (⌈n/2⌉≤′n n)

------------------------------------------------------------------------
-- Properties of _≤″_ and _<″_
------------------------------------------------------------------------

m<ᵇn⇒1+m+[n-1+m]≡n : ∀ m n → T (m <ᵇ n) → suc m + (n ∸ suc m) ≡ n
m<ᵇn⇒1+m+[n-1+m]≡n m n lt = m+n∸m≡n (<ᵇ⇒< m n lt)

m<ᵇ1+m+n : ∀ m {n} → T (m <ᵇ suc (m + n))
m<ᵇ1+m+n m = <⇒<ᵇ (m≤m+n (suc m) _)

<ᵇ⇒<″ : ∀ {m n} → T (m <ᵇ n) → m <″ n
<ᵇ⇒<″ {m} {n} leq = less-than-or-equal (m+n∸m≡n (<ᵇ⇒< m n leq))

<″⇒<ᵇ : ∀ {m n} → m <″ n → T (m <ᵇ n)
<″⇒<ᵇ {m} (less-than-or-equal refl) = <⇒<ᵇ (m≤m+n (suc m) _)

-- equivalence to _≤_

≤″⇒≤ : _≤″_ ⇒ _≤_
≤″⇒≤ {zero}  (less-than-or-equal refl) = z≤n
≤″⇒≤ {suc m} (less-than-or-equal refl) =
  s≤s (≤″⇒≤ (less-than-or-equal refl))

≤⇒≤″ : _≤_ ⇒ _≤″_
≤⇒≤″ = less-than-or-equal ∘ m+n∸m≡n

-- NB: we use the builtin function `_<ᵇ_ : (m n : ℕ) → Bool` here so
-- that the function quickly decides whether to return `yes` or `no`.
-- It still takes a linear amount of time to generate the proof if it
-- is inspected. We expect the main benefit to be visible for compiled
-- code: the backend erases proofs.

infix 4 _<″?_ _≤″?_ _≥″?_ _>″?_

_<″?_ : Decidable _<″_
m <″? n = map′ <ᵇ⇒<″ <″⇒<ᵇ (T? (m <ᵇ n))

_≤″?_ : Decidable _≤″_
zero  ≤″? n = yes (less-than-or-equal refl)
suc m ≤″? n = m <″? n

_≥″?_ : Decidable _≥″_
_≥″?_ = flip _≤″?_

_>″?_ : Decidable _>″_
_>″?_ = flip _<″?_

≤″-irrelevant : Irrelevant _≤″_
≤″-irrelevant {m} (less-than-or-equal eq₁)
                  (less-than-or-equal eq₂)
  with +-cancelˡ-≡ m (trans eq₁ (sym eq₂))
... | refl = cong less-than-or-equal (≡-irrelevant eq₁ eq₂)

<″-irrelevant : Irrelevant _<″_
<″-irrelevant = ≤″-irrelevant

>″-irrelevant : Irrelevant _>″_
>″-irrelevant = ≤″-irrelevant

≥″-irrelevant : Irrelevant _≥″_
≥″-irrelevant = ≤″-irrelevant

------------------------------------------------------------------------
-- Other properties
------------------------------------------------------------------------

-- If there is an injection from a type to ℕ, then the type has
-- decidable equality.

eq? : ∀ {a} {A : Set a} → A ↣ ℕ → Decidable {A = A} _≡_
eq? inj = via-injection inj _≟_


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.14

_*-mono_ = *-mono-≤
{-# WARNING_ON_USAGE _*-mono_
"Warning: _*-mono_ was deprecated in v0.14.
Please use *-mono-≤ instead."
#-}
_+-mono_ = +-mono-≤
{-# WARNING_ON_USAGE _+-mono_
"Warning: _+-mono_ was deprecated in v0.14.
Please use +-mono-≤ instead."
#-}
+-right-identity = +-identityʳ
{-# WARNING_ON_USAGE +-right-identity
"Warning: +-right-identity was deprecated in v0.14.
Please use +-identityʳ instead."
#-}
*-right-zero     = *-zeroʳ
{-# WARNING_ON_USAGE *-right-zero
"Warning: *-right-zero was deprecated in v0.14.
Please use *-zeroʳ instead."
#-}
distribʳ-*-+     = *-distribʳ-+
{-# WARNING_ON_USAGE distribʳ-*-+
"Warning: distribʳ-*-+ was deprecated in v0.14.
Please use *-distribʳ-+ instead."
#-}
*-distrib-∸ʳ     = *-distribʳ-∸
{-# WARNING_ON_USAGE *-distrib-∸ʳ
"Warning: *-distrib-∸ʳ was deprecated in v0.14.
Please use *-distribʳ-∸ instead."
#-}
cancel-+-left    = +-cancelˡ-≡
{-# WARNING_ON_USAGE cancel-+-left
"Warning: cancel-+-left was deprecated in v0.14.
Please use +-cancelˡ-≡ instead."
#-}
cancel-+-left-≤  = +-cancelˡ-≤
{-# WARNING_ON_USAGE cancel-+-left-≤
"Warning: cancel-+-left-≤ was deprecated in v0.14.
Please use +-cancelˡ-≤ instead."
#-}
cancel-*-right   = *-cancelʳ-≡
{-# WARNING_ON_USAGE cancel-*-right
"Warning: cancel-*-right was deprecated in v0.14.
Please use *-cancelʳ-≡ instead."
#-}
cancel-*-right-≤ = *-cancelʳ-≤
{-# WARNING_ON_USAGE cancel-*-right-≤
"Warning: cancel-*-right-≤ was deprecated in v0.14.
Please use *-cancelʳ-≤ instead."
#-}
strictTotalOrder                      = <-strictTotalOrder
{-# WARNING_ON_USAGE strictTotalOrder
"Warning: strictTotalOrder was deprecated in v0.14.
Please use <-strictTotalOrder instead."
#-}
isCommutativeSemiring                 = *-+-isCommutativeSemiring
{-# WARNING_ON_USAGE isCommutativeSemiring
"Warning: isCommutativeSemiring was deprecated in v0.14.
Please use *-+-isCommutativeSemiring instead."
#-}
commutativeSemiring                   = *-+-commutativeSemiring
{-# WARNING_ON_USAGE commutativeSemiring
"Warning: commutativeSemiring was deprecated in v0.14.
Please use *-+-commutativeSemiring instead."
#-}
isDistributiveLattice                 = ⊓-⊔-isDistributiveLattice
{-# WARNING_ON_USAGE isDistributiveLattice
"Warning: isDistributiveLattice was deprecated in v0.14.
Please use ⊓-⊔-isDistributiveLattice instead."
#-}
distributiveLattice                   = ⊓-⊔-distributiveLattice
{-# WARNING_ON_USAGE distributiveLattice
"Warning: distributiveLattice was deprecated in v0.14.
Please use ⊓-⊔-distributiveLattice instead."
#-}
⊔-⊓-0-isSemiringWithoutOne            = ⊔-⊓-isSemiringWithoutOne
{-# WARNING_ON_USAGE ⊔-⊓-0-isSemiringWithoutOne
"Warning: ⊔-⊓-0-isSemiringWithoutOne was deprecated in v0.14.
Please use ⊔-⊓-isSemiringWithoutOne instead."
#-}
⊔-⊓-0-isCommutativeSemiringWithoutOne = ⊔-⊓-isCommutativeSemiringWithoutOne
{-# WARNING_ON_USAGE ⊔-⊓-0-isCommutativeSemiringWithoutOne
"Warning: ⊔-⊓-0-isCommutativeSemiringWithoutOne was deprecated in v0.14.
Please use ⊔-⊓-isCommutativeSemiringWithoutOne instead."
#-}
⊔-⊓-0-commutativeSemiringWithoutOne   = ⊔-⊓-commutativeSemiringWithoutOne
{-# WARNING_ON_USAGE ⊔-⊓-0-commutativeSemiringWithoutOne
"Warning: ⊔-⊓-0-commutativeSemiringWithoutOne was deprecated in v0.14.
Please use ⊔-⊓-commutativeSemiringWithoutOne instead."
#-}

-- Version 0.15

¬i+1+j≤i  = i+1+j≰i
{-# WARNING_ON_USAGE ¬i+1+j≤i
"Warning: ¬i+1+j≤i was deprecated in v0.15.
Please use i+1+j≰i instead."
#-}
≤-steps   = ≤-stepsˡ
{-# WARNING_ON_USAGE ≤-steps
"Warning: ≤-steps was deprecated in v0.15.
Please use ≤-stepsˡ instead."
#-}

-- Version 0.17

i∸k∸j+j∸k≡i+j∸k : ∀ i j k → i ∸ (k ∸ j) + (j ∸ k) ≡ i + j ∸ k
i∸k∸j+j∸k≡i+j∸k zero    j k    = cong (_+ (j ∸ k)) (0∸n≡0 (k ∸ j))
i∸k∸j+j∸k≡i+j∸k (suc i) j zero = cong (λ x → suc i ∸ x + j) (0∸n≡0 j)
i∸k∸j+j∸k≡i+j∸k (suc i) zero (suc k) = begin-equality
  i ∸ k + 0  ≡⟨ +-identityʳ _ ⟩
  i ∸ k      ≡⟨ cong (_∸ k) (sym (+-identityʳ _)) ⟩
  i + 0 ∸ k  ∎
i∸k∸j+j∸k≡i+j∸k (suc i) (suc j) (suc k) = begin-equality
  suc i ∸ (k ∸ j) + (j ∸ k) ≡⟨ i∸k∸j+j∸k≡i+j∸k (suc i) j k ⟩
  suc i + j ∸ k             ≡⟨ cong (_∸ k) (sym (+-suc i j)) ⟩
  i + suc j ∸ k             ∎
{-# WARNING_ON_USAGE i∸k∸j+j∸k≡i+j∸k
"Warning: i∸k∸j+j∸k≡i+j∸k was deprecated in v0.17."
#-}
im≡jm+n⇒[i∸j]m≡n : ∀ i j m n → i * m ≡ j * m + n → (i ∸ j) * m ≡ n
im≡jm+n⇒[i∸j]m≡n i j m n eq = begin-equality
  (i ∸ j) * m            ≡⟨ *-distribʳ-∸ m i j ⟩
  (i * m) ∸ (j * m)      ≡⟨ cong (_∸ j * m) eq ⟩
  (j * m + n) ∸ (j * m)  ≡⟨ cong (_∸ j * m) (+-comm (j * m) n) ⟩
  (n + j * m) ∸ (j * m)  ≡⟨ m+n∸n≡m n (j * m) ⟩
  n                      ∎
{-# WARNING_ON_USAGE im≡jm+n⇒[i∸j]m≡n
"Warning: im≡jm+n⇒[i∸j]m≡n was deprecated in v0.17."
#-}
≤+≢⇒< = ≤∧≢⇒<
{-# WARNING_ON_USAGE ≤+≢⇒<
"Warning: ≤+≢⇒< was deprecated in v0.17.
Please use ≤∧≢⇒< instead."
#-}

-- Version 1.0

≤-irrelevance = ≤-irrelevant
{-# WARNING_ON_USAGE ≤-irrelevance
"Warning: ≤-irrelevance was deprecated in v1.0.
Please use ≤-irrelevant instead."
#-}
<-irrelevance = <-irrelevant
{-# WARNING_ON_USAGE <-irrelevance
"Warning: <-irrelevance was deprecated in v1.0.
Please use <-irrelevant instead."
#-}
