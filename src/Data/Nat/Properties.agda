------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties about natural number operations
------------------------------------------------------------------------

-- See README.Data.Nat for some examples showing how this module can be
-- used.

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Properties where

open import Axiom.UniquenessOfIdentityProofs
open import Algebra.Bundles
open import Algebra.Morphism
open import Algebra.Consequences.Propositional
open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp
import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥)
open import Data.Nat.Base
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base as Sum
open import Data.Unit using (tt)
open import Function.Base
open import Function.Injection using (_↣_)
open import Function.Metric.Nat
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.Consequences using (flip-Connex)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable using (True; via-injection; map′)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Reflects using (fromEquivalence)

open import Algebra.Definitions {A = ℕ} _≡_
  hiding (LeftCancellative; RightCancellative; Cancellative)
open import Algebra.Definitions
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

0≢1+n : ∀ {n} → 0 ≢ suc n
0≢1+n ()

1+n≢0 : ∀ {n} → suc n ≢ 0
1+n≢0 ()

1+n≢n : ∀ {n} → suc n ≢ n
1+n≢n {suc n} = 1+n≢n ∘ suc-injective

------------------------------------------------------------------------
-- Properties of _<ᵇ_
------------------------------------------------------------------------

<ᵇ⇒< : ∀ m n → T (m <ᵇ n) → m < n
<ᵇ⇒< zero    (suc n) m<n = s≤s z≤n
<ᵇ⇒< (suc m) (suc n) m<n = s≤s (<ᵇ⇒< m n m<n)

<⇒<ᵇ : ∀ {m n} → m < n → T (m <ᵇ n)
<⇒<ᵇ (s≤s z≤n)       = tt
<⇒<ᵇ (s≤s (s≤s m<n)) = <⇒<ᵇ (s≤s m<n)

<ᵇ-reflects-< : ∀ m n → Reflects (m < n) (m <ᵇ n)
<ᵇ-reflects-< m n = fromEquivalence (<ᵇ⇒< m n) <⇒<ᵇ

------------------------------------------------------------------------
-- Properties of _≤ᵇ_
------------------------------------------------------------------------

≤ᵇ⇒≤ : ∀ m n → T (m ≤ᵇ n) → m ≤ n
≤ᵇ⇒≤ zero    n m≤n = z≤n
≤ᵇ⇒≤ (suc m) n m≤n = <ᵇ⇒< m n m≤n

≤⇒≤ᵇ : ∀ {m n} → m ≤ n → T (m ≤ᵇ n)
≤⇒≤ᵇ z≤n         = tt
≤⇒≤ᵇ m≤n@(s≤s _) = <⇒<ᵇ m≤n

≤ᵇ-reflects-≤ : ∀ m n → Reflects (m ≤ n) (m ≤ᵇ n)
≤ᵇ-reflects-≤ m n = fromEquivalence (≤ᵇ⇒≤ m n) ≤⇒≤ᵇ

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------

open import Data.Nat.Properties.Core public

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
m ≤? n = map′ (≤ᵇ⇒≤ m n) ≤⇒≤ᵇ (T? (m ≤ᵇ n))

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

≤-isTotalPreorder : IsTotalPreorder _≡_ _≤_
≤-isTotalPreorder = record
  { isPreorder = ≤-isPreorder
  ; total      = ≤-total
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
-- Bundles

≤-preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder = record
  { isPreorder = ≤-isPreorder
  }

≤-totalPreorder : TotalPreorder 0ℓ 0ℓ 0ℓ
≤-totalPreorder = record
  { isTotalPreorder = ≤-isTotalPreorder
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

>⇒≢ : _>_ ⇒ _≢_
>⇒≢ = ≢-sym ∘ <⇒≢

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

≤∧≮⇒≡ : ∀ {m n} → m ≤ n → m ≮ n → m ≡ n
≤∧≮⇒≡ m≤n m≮n = ≤-antisym m≤n (≮⇒≥ m≮n)

≤-<-connex : Connex _≤_ _<_
≤-<-connex m n with m ≤? n
... | yes m≤n = inj₁ m≤n
... | no ¬m≤n = inj₂ (≰⇒> ¬m≤n)

≥->-connex : Connex _≥_ _>_
≥->-connex = flip ≤-<-connex

<-≤-connex : Connex _<_ _≤_
<-≤-connex = flip-Connex ≤-<-connex

>-≥-connex : Connex _>_ _≥_
>-≥-connex = flip-Connex ≥->-connex

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
m <? n = suc m ≤? n

_>?_ : Decidable _>_
_>?_ = flip _<?_

<-irrelevant : Irrelevant _<_
<-irrelevant = ≤-irrelevant

<-resp₂-≡ : _<_ Respects₂ _≡_
<-resp₂-≡ = subst (_ <_) , subst (_< _)

------------------------------------------------------------------------
-- Bundles

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

0<1+n : ∀ {n} → 0 < suc n
0<1+n = s≤s z≤n

n<1+n : ∀ n → n < suc n
n<1+n n = ≤-refl

n<1⇒n≡0 : ∀ {n} → n < 1 → n ≡ 0
n<1⇒n≡0 (s≤s n≤0) = n≤0⇒n≡0 n≤0

n≢0⇒n>0 : ∀ {n} → n ≢ 0 → n > 0
n≢0⇒n>0 {zero}  0≢0 =  contradiction refl 0≢0
n≢0⇒n>0 {suc n} _   =  0<1+n

m<n⇒0<n : ∀ {m n} → m < n → 0 < n
m<n⇒0<n = ≤-trans 0<1+n

m<n⇒n≢0 : ∀ {m n} → m < n → n ≢ 0
m<n⇒n≢0 (s≤s m≤n) ()

m<n⇒m≤1+n : ∀ {m n} → m < n → m ≤ suc n
m<n⇒m≤1+n = ≤-step ∘ <⇒≤

∀[m≤n⇒m≢o]⇒n<o : ∀ n o → (∀ {m} → m ≤ n → m ≢ o) → n < o
∀[m≤n⇒m≢o]⇒n<o _       zero    m≤n⇒n≢0 = contradiction refl (m≤n⇒n≢0 z≤n)
∀[m≤n⇒m≢o]⇒n<o zero    (suc o) _       = 0<1+n
∀[m≤n⇒m≢o]⇒n<o (suc n) (suc o) m≤n⇒n≢o = s≤s (∀[m≤n⇒m≢o]⇒n<o n o rec)
  where
  rec : ∀ {m} → m ≤ n → m ≢ o
  rec m≤n refl = m≤n⇒n≢o (s≤s m≤n) refl

∀[m<n⇒m≢o]⇒n≤o : ∀ n o → (∀ {m} → m < n → m ≢ o) → n ≤ o
∀[m<n⇒m≢o]⇒n≤o zero    n       _       = z≤n
∀[m<n⇒m≢o]⇒n≤o (suc n) zero    m<n⇒m≢0 = contradiction refl (m<n⇒m≢0 0<1+n)
∀[m<n⇒m≢o]⇒n≤o (suc n) (suc o) m<n⇒m≢o = s≤s (∀[m<n⇒m≢o]⇒n≤o n o rec)
  where
  rec : ∀ {m} → m < n → m ≢ o
  rec x<m refl = m<n⇒m≢o (s≤s x<m) refl

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
    as Reasoning
    public
    hiding (begin-irrefl; step-≈; step-≈˘)

  infix 1 begin-irrefl_
  begin-irrefl_ = Reasoning.begin-irrefl <-irrefl

open ≤-Reasoning

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

+-isCommutativeSemigroup : IsCommutativeSemigroup _+_
+-isCommutativeSemigroup = record
  { isSemigroup = +-isSemigroup
  ; comm        = +-comm
  }

+-0-isMonoid : IsMonoid _+_ 0
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm     = +-comm
  }

------------------------------------------------------------------------
-- Raw bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  }

+-0-rawMonoid : RawMonoid 0ℓ 0ℓ
+-0-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε   = 0
  }

------------------------------------------------------------------------
-- Bundles

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
+-commutativeSemigroup = record
  { isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

∸-magma : Magma 0ℓ 0ℓ
∸-magma = magma _∸_


------------------------------------------------------------------------
-- Other properties of _+_ and _≡_

m≢1+m+n : ∀ m {n} → m ≢ suc (m + n)
m≢1+m+n (suc m) eq = m≢1+m+n m (cong pred eq)

m≢1+n+m : ∀ m {n} → m ≢ suc (n + m)
m≢1+n+m m m≡1+n+m = m≢1+m+n m (trans m≡1+n+m (cong suc (+-comm _ m)))

m+1+n≢m : ∀ m {n} → m + suc n ≢ m
m+1+n≢m (suc m) = (m+1+n≢m m) ∘ suc-injective

m+1+n≢0 : ∀ m {n} → m + suc n ≢ 0
m+1+n≢0 m {n} rewrite +-suc m n = λ()

m+n≡0⇒m≡0 : ∀ m {n} → m + n ≡ 0 → m ≡ 0
m+n≡0⇒m≡0 zero eq = refl

m+n≡0⇒n≡0 : ∀ m {n} → m + n ≡ 0 → n ≡ 0
m+n≡0⇒n≡0 m {n} m+n≡0 = m+n≡0⇒m≡0 n (trans (+-comm n m) (m+n≡0))

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
+-cancelˡ-< m {n} {o} = +-cancelˡ-≤ m ∘ subst (_≤ m + o) (sym (+-suc m n))

+-cancelʳ-< : RightCancellative _<_ _+_
+-cancelʳ-< n o n+m<o+m = +-cancelʳ-≤ (suc n) o n+m<o+m

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

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m n = subst (m ≤_) (+-comm m n) (m≤m+n m n)

m≤n⇒m<n∨m≡n :  ∀ {m n} → m ≤ n → m < n ⊎ m ≡ n
m≤n⇒m<n∨m≡n {0}     {0}     _          =  inj₂ refl
m≤n⇒m<n∨m≡n {0}     {suc n} _          =  inj₁ 0<1+n
m≤n⇒m<n∨m≡n {suc m} {suc n} (s≤s m≤n)  with m≤n⇒m<n∨m≡n m≤n
... | inj₂ m≡n = inj₂ (cong suc m≡n)
... | inj₁ m<n = inj₁ (s≤s m<n)

m+n≤o⇒m≤o : ∀ m {n o} → m + n ≤ o → m ≤ o
m+n≤o⇒m≤o zero    m+n≤o       = z≤n
m+n≤o⇒m≤o (suc m) (s≤s m+n≤o) = s≤s (m+n≤o⇒m≤o m m+n≤o)

m+n≤o⇒n≤o : ∀ m {n o} → m + n ≤ o → n ≤ o
m+n≤o⇒n≤o zero    n≤o   = n≤o
m+n≤o⇒n≤o (suc m) m+n<o = m+n≤o⇒n≤o m (<⇒≤ m+n<o)

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {_} {m} z≤n       o≤p = ≤-trans o≤p (m≤n+m _ m)
+-mono-≤ {_} {_} (s≤s m≤n) o≤p = s≤s (+-mono-≤ m≤n o≤p)

+-monoˡ-≤ : ∀ n → (_+ n) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ n m≤o = +-mono-≤ m≤o (≤-refl {n})

+-monoʳ-≤ : ∀ n → (n +_) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ n m≤o = +-mono-≤ (≤-refl {n}) m≤o

+-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {_} {suc n} (s≤s z≤n)       o≤p = s≤s (≤-stepsˡ n o≤p)
+-mono-<-≤ {_} {_}     (s≤s (s≤s m<n)) o≤p = s≤s (+-mono-<-≤ (s≤s m<n) o≤p)

+-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {_} {n} z≤n       o<p = ≤-trans o<p (m≤n+m _ n)
+-mono-≤-< {_} {_} (s≤s m≤n) o<p = s≤s (+-mono-≤-< m≤n o<p)

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< m≤n = +-mono-≤-< (<⇒≤ m≤n)

+-monoˡ-< : ∀ n → (_+ n) Preserves _<_ ⟶ _<_
+-monoˡ-< n = +-monoˡ-≤ n

+-monoʳ-< : ∀ n → (n +_) Preserves _<_ ⟶ _<_
+-monoʳ-< zero    m≤o = m≤o
+-monoʳ-< (suc n) m≤o = s≤s (+-monoʳ-< n m≤o)

m+1+n≰m : ∀ m {n} → m + suc n ≰ m
m+1+n≰m (suc m) le = m+1+n≰m m (≤-pred le)

m<m+n : ∀ m {n} → n > 0 → m < m + n
m<m+n zero    n>0 = n>0
m<m+n (suc m) n>0 = s≤s (m<m+n m n>0)

m<n+m : ∀ m {n} → n > 0 → m < n + m
m<n+m m {n} n>0 rewrite +-comm n m = m<m+n m n>0

m+n≮n : ∀ m n → m + n ≮ n
m+n≮n zero    n                   = n≮n n
m+n≮n (suc m) (suc n) (s≤s m+n<n) = m+n≮n m (suc n) (≤-step m+n<n)

m+n≮m : ∀ m n → m + n ≮ m
m+n≮m m n = subst (_≮ m) (+-comm n m) (m+n≮n n m)

------------------------------------------------------------------------
-- Properties of _*_
------------------------------------------------------------------------

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc zero    n = refl
*-suc (suc m) n = begin-equality
  suc m * suc n         ≡⟨⟩
  suc n + m * suc n     ≡⟨ cong (suc n +_) (*-suc m n) ⟩
  suc n + (m + m * n)   ≡⟨⟩
  suc (n + (m + m * n)) ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
  suc (n + m + m * n)   ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m) ⟩
  suc (m + n + m * n)   ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
  suc (m + (n + m * n)) ≡⟨⟩
  suc m + suc m * n     ∎

------------------------------------------------------------------------
-- Algebraic properties of _*_

*-identityˡ : LeftIdentity 1 _*_
*-identityˡ n = +-identityʳ n

*-identityʳ : RightIdentity 1 _*_
*-identityʳ zero    = refl
*-identityʳ (suc n) = cong suc (*-identityʳ n)

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
  n + n * m  ≡⟨ sym (*-suc n m) ⟩
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

*-isCommutativeSemigroup : IsCommutativeSemigroup _*_
*-isCommutativeSemigroup = record
  { isSemigroup = *-isSemigroup
  ; comm        = *-comm
  }

*-1-isMonoid : IsMonoid _*_ 1
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = *-comm
  }

+-*-isSemiring : IsSemiring _+_ _*_ 0 1
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-0-isCommutativeMonoid
    ; *-isMonoid            = *-1-isMonoid
    ; distrib               = *-distrib-+
    }
  ; zero = *-zero
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ 0 1
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm     = *-comm
  }

------------------------------------------------------------------------
-- Bundles

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  }

*-1-rawMonoid : RawMonoid 0ℓ 0ℓ
*-1-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  ; ε   = 1
  }

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
*-commutativeSemigroup = record
  { isCommutativeSemigroup = *-isCommutativeSemigroup
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

+-*-semiring : Semiring 0ℓ 0ℓ
+-*-semiring = record
  { isSemiring = +-*-isSemiring
  }

+-*-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
+-*-commutativeSemiring = record
  { isCommutativeSemiring = +-*-isCommutativeSemiring
  }

------------------------------------------------------------------------
-- Other properties of _*_ and _≡_

*-cancelʳ-≡ : ∀ m n {o} → m * suc o ≡ n * suc o → m ≡ n
*-cancelʳ-≡ zero    zero        eq = refl
*-cancelʳ-≡ (suc m) (suc n) {o} eq =
  cong suc (*-cancelʳ-≡ m n (+-cancelˡ-≡ (suc o) eq))

*-cancelˡ-≡ : ∀ {m n} o → suc o * m ≡ suc o * n → m ≡ n
*-cancelˡ-≡ {m} {n} o eq = *-cancelʳ-≡ m n
  (subst₂ _≡_ (*-comm (suc o) m) (*-comm (suc o) n) eq)

m*n≡0⇒m≡0∨n≡0 : ∀ m {n} → m * n ≡ 0 → m ≡ 0 ⊎ n ≡ 0
m*n≡0⇒m≡0∨n≡0 zero    {n}     eq = inj₁ refl
m*n≡0⇒m≡0∨n≡0 (suc m) {zero}  eq = inj₂ refl

m*n≡1⇒m≡1 : ∀ m n → m * n ≡ 1 → m ≡ 1
m*n≡1⇒m≡1 (suc zero)    n             _  = refl
m*n≡1⇒m≡1 (suc (suc m)) (suc zero)    ()
m*n≡1⇒m≡1 (suc (suc m)) zero          eq =
  contradiction (trans (sym $ *-zeroʳ m) eq) λ()

m*n≡1⇒n≡1 : ∀ m n → m * n ≡ 1 → n ≡ 1
m*n≡1⇒n≡1 m n eq = m*n≡1⇒m≡1 n m (trans (*-comm n m) eq)

[m*n]*[o*p]≡[m*o]*[n*p] : ∀ m n o p → (m * n) * (o * p) ≡ (m * o) * (n * p)
[m*n]*[o*p]≡[m*o]*[n*p] m n o p = begin-equality
  (m * n) * (o * p) ≡⟨  *-assoc m n (o * p) ⟩
  m * (n * (o * p)) ≡⟨  cong (m *_) (x∙yz≈y∙xz n o p) ⟩
  m * (o * (n * p)) ≡˘⟨ *-assoc m o (n * p) ⟩
  (m * o) * (n * p) ∎
  where open CommSemigroupProperties *-commutativeSemigroup

------------------------------------------------------------------------
-- Other properties of _*_ and _≤_/_<_

*-cancelʳ-≤ : ∀ m n o → m * suc o ≤ n * suc o → m ≤ n
*-cancelʳ-≤ zero    _       _ _  = z≤n
*-cancelʳ-≤ (suc m) (suc n) o le =
  s≤s (*-cancelʳ-≤ m n o (+-cancelˡ-≤ (suc o) le))

*-cancelˡ-≤ : ∀ {m n} o → suc o * m ≤ suc o * n → m ≤ n
*-cancelˡ-≤ {m} {n} o rewrite *-comm (suc o) m | *-comm (suc o) n = *-cancelʳ-≤ m n o

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

m≤n*m : ∀ m {n} → 0 < n → m ≤ n * m
m≤n*m m {n} 0<n = begin
  m     ≤⟨ m≤m*n m 0<n ⟩
  m * n ≡⟨ *-comm m n ⟩
  n * m ∎

m<m*n :  ∀ {m n} → 0 < m → 1 < n → m < m * n
m<m*n {m@(suc m-1)} {n@(suc (suc n-2))} (s≤s _) (s≤s (s≤s _)) = begin-strict
  m           <⟨ s≤s (s≤s (m≤n+m m-1 n-2)) ⟩
  n + m-1     ≤⟨ +-monoʳ-≤ n (m≤m*n m-1 0<1+n) ⟩
  n + m-1 * n ≡⟨⟩
  m * n       ∎

*-cancelʳ-< : RightCancellative _<_ _*_
*-cancelʳ-< {zero}  zero    (suc o) _     = 0<1+n
*-cancelʳ-< {suc m} zero    (suc o) _     = 0<1+n
*-cancelʳ-< {m}     (suc n) (suc o) nm<om =
  s≤s (*-cancelʳ-< n o (+-cancelˡ-< m nm<om))

-- Redo in terms of `comm+cancelʳ⇒cancelˡ` when generalised
*-cancelˡ-< : LeftCancellative _<_ _*_
*-cancelˡ-< x {y} {z} rewrite *-comm x y | *-comm x z = *-cancelʳ-< y z

*-cancel-< : Cancellative _<_ _*_
*-cancel-< = *-cancelˡ-< , *-cancelʳ-<

------------------------------------------------------------------------
-- Properties of _^_
------------------------------------------------------------------------

^-identityʳ : RightIdentity 1 _^_
^-identityʳ zero    = refl
^-identityʳ (suc n) = cong suc (^-identityʳ n)

^-zeroˡ : LeftZero 1 _^_
^-zeroˡ zero    = refl
^-zeroˡ (suc n) = begin-equality
  1 ^ suc n   ≡⟨⟩
  1 * (1 ^ n) ≡⟨ *-identityˡ (1 ^ n) ⟩
  1 ^ n       ≡⟨ ^-zeroˡ n ⟩
  1           ∎

^-distribˡ-+-* : ∀ m n o → m ^ (n + o) ≡ m ^ n * m ^ o
^-distribˡ-+-* m zero    o = sym (+-identityʳ (m ^ o))
^-distribˡ-+-* m (suc n) o = begin-equality
  m * (m ^ (n + o))       ≡⟨ cong (m *_) (^-distribˡ-+-* m n o) ⟩
  m * ((m ^ n) * (m ^ o)) ≡⟨ sym (*-assoc m _ _) ⟩
  (m * (m ^ n)) * (m ^ o) ∎

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

^-*-assoc : ∀ m n o → (m ^ n) ^ o ≡ m ^ (n * o)
^-*-assoc m n zero    = cong (m ^_) (sym $ *-zeroʳ n)
^-*-assoc m n (suc o) = begin-equality
  (m ^ n) * ((m ^ n) ^ o) ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n o) ⟩
  (m ^ n) * (m ^ (n * o)) ≡⟨ sym (^-distribˡ-+-* m n (n * o)) ⟩
  m ^ (n + n * o)         ≡⟨ cong (m ^_) (sym (*-suc n o)) ⟩
  m ^ (n * (suc o)) ∎

m^n≡0⇒m≡0 : ∀ m n → m ^ n ≡ 0 → m ≡ 0
m^n≡0⇒m≡0 m (suc n) eq = [ id , m^n≡0⇒m≡0 m n ]′ (m*n≡0⇒m≡0∨n≡0 m eq)

m^n≡1⇒n≡0∨m≡1 : ∀ m n → m ^ n ≡ 1 → n ≡ 0 ⊎ m ≡ 1
m^n≡1⇒n≡0∨m≡1 m zero    _  = inj₁ refl
m^n≡1⇒n≡0∨m≡1 m (suc n) eq = inj₂ (m*n≡1⇒m≡1 m (m ^ n) eq)

------------------------------------------------------------------------
-- Properties of _⊓_ and _⊔_
------------------------------------------------------------------------
-- Basic specification in terms of _≤_

m≤n⇒m⊔n≡n : ∀ {m n} → m ≤ n → m ⊔ n ≡ n
m≤n⇒m⊔n≡n {zero}  _         = refl
m≤n⇒m⊔n≡n {suc m} (s≤s m≤n) = cong suc (m≤n⇒m⊔n≡n m≤n)

m≥n⇒m⊔n≡m : ∀ {m n} → m ≥ n → m ⊔ n ≡ m
m≥n⇒m⊔n≡m {zero}  {zero}  z≤n       = refl
m≥n⇒m⊔n≡m {suc m} {zero}  z≤n       = refl
m≥n⇒m⊔n≡m {suc m} {suc n} (s≤s m≥n) = cong suc (m≥n⇒m⊔n≡m m≥n)

m≤n⇒m⊓n≡m : ∀ {m n} → m ≤ n → m ⊓ n ≡ m
m≤n⇒m⊓n≡m {zero}  z≤n       = refl
m≤n⇒m⊓n≡m {suc m} (s≤s m≤n) = cong suc (m≤n⇒m⊓n≡m m≤n)

m≥n⇒m⊓n≡n : ∀ {m n} → m ≥ n → m ⊓ n ≡ n
m≥n⇒m⊓n≡n {zero}  {zero}  z≤n       = refl
m≥n⇒m⊓n≡n {suc m} {zero}  z≤n       = refl
m≥n⇒m⊓n≡n {suc m} {suc n} (s≤s m≤n) = cong suc (m≥n⇒m⊓n≡n m≤n)

⊓-operator : MinOperator ≤-totalPreorder
⊓-operator = record
  { x≤y⇒x⊓y≈x = m≤n⇒m⊓n≡m
  ; x≥y⇒x⊓y≈y = m≥n⇒m⊓n≡n
  }

⊔-operator : MaxOperator ≤-totalPreorder
⊔-operator = record
  { x≤y⇒x⊔y≈y = m≤n⇒m⊔n≡n
  ; x≥y⇒x⊔y≈x = m≥n⇒m⊔n≡m
  }

------------------------------------------------------------------------
-- Derived properties of _⊓_ and _⊔_

private
  module ⊓-⊔-properties = MinMaxOp ⊓-operator ⊔-operator

open ⊓-⊔-properties public
  using
  ( ⊓-idem                    -- : Idempotent _⊓_
  ; ⊓-sel                     -- : Selective _⊓_
  ; ⊓-assoc                   -- : Associative _⊓_
  ; ⊓-comm                    -- : Commutative _⊓_

  ; ⊔-idem                    -- : Idempotent _⊔_
  ; ⊔-sel                     -- : Selective _⊔_
  ; ⊔-assoc                   -- : Associative _⊔_
  ; ⊔-comm                    -- : Commutative _⊔_

  ; ⊓-distribˡ-⊔              -- : _⊓_ DistributesOverˡ _⊔_
  ; ⊓-distribʳ-⊔              -- : _⊓_ DistributesOverʳ _⊔_
  ; ⊓-distrib-⊔               -- : _⊓_ DistributesOver  _⊔_
  ; ⊔-distribˡ-⊓              -- : _⊔_ DistributesOverˡ _⊓_
  ; ⊔-distribʳ-⊓              -- : _⊔_ DistributesOverʳ _⊓_
  ; ⊔-distrib-⊓               -- : _⊔_ DistributesOver  _⊓_
  ; ⊓-absorbs-⊔               -- : _⊓_ Absorbs _⊔_
  ; ⊔-absorbs-⊓               -- : _⊔_ Absorbs _⊓_
  ; ⊔-⊓-absorptive            -- : Absorptive _⊔_ _⊓_
  ; ⊓-⊔-absorptive            -- : Absorptive _⊓_ _⊔_

  ; ⊓-isMagma                 -- : IsMagma _⊓_
  ; ⊓-isSemigroup             -- : IsSemigroup _⊓_
  ; ⊓-isCommutativeSemigroup  -- : IsCommutativeSemigroup _⊓_
  ; ⊓-isBand                  -- : IsBand _⊓_
  ; ⊓-isSemilattice           -- : IsSemilattice _⊓_
  ; ⊓-isSelectiveMagma        -- : IsSelectiveMagma _⊓_

  ; ⊔-isMagma                 -- : IsMagma _⊔_
  ; ⊔-isSemigroup             -- : IsSemigroup _⊔_
  ; ⊔-isCommutativeSemigroup  -- : IsCommutativeSemigroup _⊔_
  ; ⊔-isBand                  -- : IsBand _⊔_
  ; ⊔-isSemilattice           -- : IsSemilattice _⊔_
  ; ⊔-isSelectiveMagma        -- : IsSelectiveMagma _⊔_

  ; ⊔-⊓-isLattice             -- : IsLattice _⊔_ _⊓_
  ; ⊓-⊔-isLattice             -- : IsLattice _⊓_ _⊔_
  ; ⊔-⊓-isDistributiveLattice -- : IsDistributiveLattice _⊔_ _⊓_
  ; ⊓-⊔-isDistributiveLattice -- : IsDistributiveLattice _⊓_ _⊔_

  ; ⊓-magma                   -- : Magma _ _
  ; ⊓-semigroup               -- : Semigroup _ _
  ; ⊓-band                    -- : Band _ _
  ; ⊓-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊓-semilattice             -- : Semilattice _ _
  ; ⊓-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊔-magma                   -- : Magma _ _
  ; ⊔-semigroup               -- : Semigroup _ _
  ; ⊔-band                    -- : Band _ _
  ; ⊔-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊔-semilattice             -- : Semilattice _ _
  ; ⊔-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊔-⊓-lattice               -- : Lattice _ _
  ; ⊓-⊔-lattice               -- : Lattice _ _
  ; ⊔-⊓-distributiveLattice   -- : DistributiveLattice _ _
  ; ⊓-⊔-distributiveLattice   -- : DistributiveLattice _ _

  ; ⊓-glb                     -- : ∀ {m n o} → m ≥ o → n ≥ o → m ⊓ n ≥ o
  ; ⊓-triangulate             -- : ∀ m n o → m ⊓ n ⊓ o ≡ (m ⊓ n) ⊓ (n ⊓ o)
  ; ⊓-mono-≤                  -- : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ; ⊓-monoˡ-≤                 -- : ∀ n → (_⊓ n) Preserves _≤_ ⟶ _≤_
  ; ⊓-monoʳ-≤                 -- : ∀ n → (n ⊓_) Preserves _≤_ ⟶ _≤_

  ; ⊔-lub                     -- : ∀ {m n o} → m ≤ o → n ≤ o → m ⊔ n ≤ o
  ; ⊔-triangulate             -- : ∀ m n o → m ⊔ n ⊔ o ≡ (m ⊔ n) ⊔ (n ⊔ o)
  ; ⊔-mono-≤                  -- : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ; ⊔-monoˡ-≤                 -- : ∀ n → (_⊔ n) Preserves _≤_ ⟶ _≤_
  ; ⊔-monoʳ-≤                 -- : ∀ n → (n ⊔_) Preserves _≤_ ⟶ _≤_
  )
  renaming
  ( x⊓y≈y⇒y≤x to m⊓n≡n⇒n≤m    -- : ∀ {m n} → m ⊓ n ≡ n → n ≤ m
  ; x⊓y≈x⇒x≤y to m⊓n≡m⇒m≤n    -- : ∀ {m n} → m ⊓ n ≡ m → m ≤ n
  ; x⊓y≤x     to m⊓n≤m        -- : ∀ m n → m ⊓ n ≤ m
  ; x⊓y≤y     to m⊓n≤n        -- : ∀ m n → m ⊓ n ≤ n
  ; x≤y⇒x⊓z≤y to m≤n⇒m⊓o≤n    -- : ∀ {m n} o → m ≤ n → m ⊓ o ≤ n
  ; x≤y⇒z⊓x≤y to m≤n⇒o⊓m≤n    -- : ∀ {m n} o → m ≤ n → o ⊓ m ≤ n
  ; x≤y⊓z⇒x≤y to m≤n⊓o⇒m≤n    -- : ∀ {m} n o → m ≤ n ⊓ o → m ≤ n
  ; x≤y⊓z⇒x≤z to m≤n⊓o⇒m≤o    -- : ∀ {m} n o → m ≤ n ⊓ o → m ≤ o

  ; x⊔y≈y⇒x≤y to m⊔n≡n⇒m≤n    -- : ∀ {m n} → m ⊔ n ≡ n → m ≤ n
  ; x⊔y≈x⇒y≤x to m⊔n≡m⇒n≤m    -- : ∀ {m n} → m ⊔ n ≡ m → n ≤ m
  ; x≤x⊔y     to m≤m⊔n        -- : ∀ m n → m ≤ m ⊔ n
  ; x≤y⊔x     to m≤n⊔m        -- : ∀ m n → m ≤ n ⊔ m
  ; x≤y⇒x≤y⊔z to m≤n⇒m≤n⊔o    -- : ∀ {m n} o → m ≤ n → m ≤ n ⊔ o
  ; x≤y⇒x≤z⊔y to m≤n⇒m≤o⊔n    -- : ∀ {m n} o → m ≤ n → m ≤ o ⊔ n
  ; x⊔y≤z⇒x≤z to m⊔n≤o⇒m≤o    -- : ∀ m n {o} → m ⊔ n ≤ o → m ≤ o
  ; x⊔y≤z⇒y≤z to m⊔n≤o⇒n≤o    -- : ∀ m n {o} → m ⊔ n ≤ o → n ≤ o

  ; x⊓y≤x⊔y   to m⊓n≤m⊔n      -- : ∀ m n → m ⊓ n ≤ m ⊔ n
  )

------------------------------------------------------------------------
-- Automatically derived properties of _⊓_ and _⊔_

⊔-identityˡ : LeftIdentity 0 _⊔_
⊔-identityˡ _ = refl

⊔-identityʳ : RightIdentity 0 _⊔_
⊔-identityʳ zero    = refl
⊔-identityʳ (suc n) = refl

⊔-identity : Identity 0 _⊔_
⊔-identity = ⊔-identityˡ , ⊔-identityʳ

------------------------------------------------------------------------
-- Structures

⊔-0-isMonoid : IsMonoid _⊔_ 0
⊔-0-isMonoid = record
  { isSemigroup = ⊔-isSemigroup
  ; identity    = ⊔-identity
  }

⊔-0-isCommutativeMonoid : IsCommutativeMonoid _⊔_ 0
⊔-0-isCommutativeMonoid = record
  { isMonoid = ⊔-0-isMonoid
  ; comm     = ⊔-comm
  }

------------------------------------------------------------------------
-- Bundles

⊔-0-monoid : Monoid 0ℓ 0ℓ
⊔-0-monoid = record
  { isMonoid = ⊔-0-isMonoid
  }

⊔-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
⊔-0-commutativeMonoid = record
  { isCommutativeMonoid = ⊔-0-isCommutativeMonoid
  }

------------------------------------------------------------------------
-- Other properties of _⊔_ and _≤_/_<_

mono-≤-distrib-⊔ : ∀ {f} → f Preserves _≤_ ⟶ _≤_ →
                   ∀ m n → f (m ⊔ n) ≡ f m ⊔ f n
mono-≤-distrib-⊔ {f} = ⊓-⊔-properties.mono-≤-distrib-⊔ (cong f)

mono-≤-distrib-⊓ : ∀ {f} → f Preserves _≤_ ⟶ _≤_ →
                   ∀ m n → f (m ⊓ n) ≡ f m ⊓ f n
mono-≤-distrib-⊓ {f} = ⊓-⊔-properties.mono-≤-distrib-⊓ (cong f)

antimono-≤-distrib-⊓ : ∀ {f} → f Preserves _≤_ ⟶ _≥_ →
                       ∀ m n → f (m ⊓ n) ≡ f m ⊔ f n
antimono-≤-distrib-⊓ {f} = ⊓-⊔-properties.antimono-≤-distrib-⊓ (cong f)

antimono-≤-distrib-⊔ : ∀ {f} → f Preserves _≤_ ⟶ _≥_ →
                       ∀ m n → f (m ⊔ n) ≡ f m ⊓ f n
antimono-≤-distrib-⊔ {f} = ⊓-⊔-properties.antimono-≤-distrib-⊔ (cong f)

m<n⇒m<n⊔o : ∀ {m n} o → m < n → m < n ⊔ o
m<n⇒m<n⊔o = m≤n⇒m≤n⊔o

m<n⇒m<o⊔n : ∀ {m n} o → m < n → m < o ⊔ n
m<n⇒m<o⊔n = m≤n⇒m≤o⊔n

m⊔n<o⇒m<o : ∀ m n {o} → m ⊔ n < o → m < o
m⊔n<o⇒m<o m n m⊔n<o = <-transʳ (m≤m⊔n m n) m⊔n<o

m⊔n<o⇒n<o : ∀ m n {o} → m ⊔ n < o → n < o
m⊔n<o⇒n<o m n m⊔n<o = <-transʳ (m≤n⊔m m n) m⊔n<o

⊔-mono-< : _⊔_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
⊔-mono-< = ⊔-mono-≤

⊔-pres-<m : ∀ {m n o} → n < m → o < m → n ⊔ o < m
⊔-pres-<m {m} n<m o<m = subst (_ <_) (⊔-idem m) (⊔-mono-< n<m o<m)

------------------------------------------------------------------------
-- Other properties of _⊔_ and _+_

+-distribˡ-⊔ : _+_ DistributesOverˡ _⊔_
+-distribˡ-⊔ zero    n o = refl
+-distribˡ-⊔ (suc m) n o = cong suc (+-distribˡ-⊔ m n o)

+-distribʳ-⊔ : _+_ DistributesOverʳ _⊔_
+-distribʳ-⊔ = comm+distrˡ⇒distrʳ +-comm +-distribˡ-⊔

+-distrib-⊔ : _+_ DistributesOver _⊔_
+-distrib-⊔ = +-distribˡ-⊔ , +-distribʳ-⊔

m⊔n≤m+n : ∀ m n → m ⊔ n ≤ m + n
m⊔n≤m+n m n with ⊔-sel m n
... | inj₁ m⊔n≡m rewrite m⊔n≡m = m≤m+n m n
... | inj₂ m⊔n≡n rewrite m⊔n≡n = m≤n+m n m

------------------------------------------------------------------------
-- Other properties of _⊔_ and _*_

*-distribˡ-⊔ : _*_ DistributesOverˡ _⊔_
*-distribˡ-⊔ m zero o = sym (cong (_⊔ m * o) (*-zeroʳ m))
*-distribˡ-⊔ m (suc n) zero = begin-equality
  m * (suc n ⊔ zero)         ≡⟨⟩
  m * suc n                  ≡˘⟨ ⊔-identityʳ (m * suc n) ⟩
  m * suc n ⊔ zero           ≡˘⟨ cong (m * suc n ⊔_) (*-zeroʳ m) ⟩
  m * suc n ⊔ m * zero       ∎
*-distribˡ-⊔ m (suc n) (suc o) = begin-equality
  m * (suc n ⊔ suc o)        ≡⟨⟩
  m * suc (n ⊔ o)            ≡⟨ *-suc m (n ⊔ o) ⟩
  m + m * (n ⊔ o)            ≡⟨ cong (m +_) (*-distribˡ-⊔ m n o) ⟩
  m + (m * n ⊔ m * o)        ≡⟨ +-distribˡ-⊔ m (m * n) (m * o) ⟩
  (m + m * n) ⊔ (m + m * o)  ≡˘⟨ cong₂ _⊔_ (*-suc m n) (*-suc m o) ⟩
  (m * suc n) ⊔ (m * suc o)  ∎

*-distribʳ-⊔ : _*_ DistributesOverʳ _⊔_
*-distribʳ-⊔ = comm+distrˡ⇒distrʳ *-comm *-distribˡ-⊔

*-distrib-⊔ : _*_ DistributesOver _⊔_
*-distrib-⊔ = *-distribˡ-⊔ , *-distribʳ-⊔

------------------------------------------------------------------------
-- Properties of _⊓_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties

⊓-zeroˡ : LeftZero 0 _⊓_
⊓-zeroˡ _ = refl

⊓-zeroʳ : RightZero 0 _⊓_
⊓-zeroʳ zero    = refl
⊓-zeroʳ (suc n) = refl

⊓-zero : Zero 0 _⊓_
⊓-zero = ⊓-zeroˡ , ⊓-zeroʳ

------------------------------------------------------------------------
-- Structures

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

------------------------------------------------------------------------
-- Bundles

⊔-⊓-commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne 0ℓ 0ℓ
⊔-⊓-commutativeSemiringWithoutOne = record
  { isCommutativeSemiringWithoutOne =
      ⊔-⊓-isCommutativeSemiringWithoutOne
  }

------------------------------------------------------------------------
-- Other properties of _⊓_ and _≤_/_<_

m<n⇒m⊓o<n : ∀ {m n} o → m < n → m ⊓ o < n
m<n⇒m⊓o<n o m<n = <-transʳ (m⊓n≤m _ o) m<n

m<n⇒o⊓m<n : ∀ {m n} o → m < n → o ⊓ m < n
m<n⇒o⊓m<n o m<n = <-transʳ (m⊓n≤n o _) m<n

m<n⊓o⇒m<n : ∀ {m} n o → m < n ⊓ o → m < n
m<n⊓o⇒m<n = m≤n⊓o⇒m≤n

m<n⊓o⇒m<o : ∀ {m} n o → m < n ⊓ o → m < o
m<n⊓o⇒m<o = m≤n⊓o⇒m≤o

⊓-mono-< : _⊓_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
⊓-mono-< = ⊓-mono-≤

⊓-pres-m< : ∀ {m n o} → m < n → m < o → m < n ⊓ o
⊓-pres-m< {m} m<n m<o = subst (_< _) (⊓-idem m) (⊓-mono-< m<n m<o)

------------------------------------------------------------------------
-- Other properties of _⊓_ and _+_

+-distribˡ-⊓ : _+_ DistributesOverˡ _⊓_
+-distribˡ-⊓ zero    n o = refl
+-distribˡ-⊓ (suc m) n o = cong suc (+-distribˡ-⊓ m n o)

+-distribʳ-⊓ : _+_ DistributesOverʳ _⊓_
+-distribʳ-⊓ = comm+distrˡ⇒distrʳ +-comm +-distribˡ-⊓

+-distrib-⊓ : _+_ DistributesOver _⊓_
+-distrib-⊓ = +-distribˡ-⊓ , +-distribʳ-⊓

m⊓n≤m+n : ∀ m n → m ⊓ n ≤ m + n
m⊓n≤m+n m n with ⊓-sel m n
... | inj₁ m⊓n≡m rewrite m⊓n≡m = m≤m+n m n
... | inj₂ m⊓n≡n rewrite m⊓n≡n = m≤n+m n m

------------------------------------------------------------------------
-- Other properties of _⊓_ and _*_

*-distribˡ-⊓ : _*_ DistributesOverˡ _⊓_
*-distribˡ-⊓ m 0 o = begin-equality
  m * (0 ⊓ o)               ≡⟨⟩
  m * 0                     ≡⟨ *-zeroʳ m ⟩
  0                         ≡⟨⟩
  0 ⊓ (m * o)               ≡˘⟨ cong (_⊓ (m * o)) (*-zeroʳ m) ⟩
  (m * 0) ⊓ (m * o)         ∎
*-distribˡ-⊓ m (suc n) 0 = begin-equality
  m * (suc n ⊓ 0)           ≡⟨⟩
  m * 0                     ≡⟨ *-zeroʳ m ⟩
  0                         ≡˘⟨ ⊓-zeroʳ (m * suc n) ⟩
  (m * suc n) ⊓ 0           ≡˘⟨ cong (m * suc n ⊓_) (*-zeroʳ m) ⟩
  (m * suc n) ⊓ (m * 0)     ∎
*-distribˡ-⊓ m (suc n) (suc o) = begin-equality
  m * (suc n ⊓ suc o)       ≡⟨⟩
  m * suc (n ⊓ o)           ≡⟨ *-suc m (n ⊓ o) ⟩
  m + m * (n ⊓ o)           ≡⟨ cong (m +_) (*-distribˡ-⊓ m n o) ⟩
  m + (m * n) ⊓ (m * o)     ≡⟨ +-distribˡ-⊓ m (m * n) (m * o) ⟩
  (m + m * n) ⊓ (m + m * o) ≡˘⟨ cong₂ _⊓_ (*-suc m n) (*-suc m o) ⟩
  (m * suc n) ⊓ (m * suc o) ∎

*-distribʳ-⊓ : _*_ DistributesOverʳ _⊓_
*-distribʳ-⊓ = comm+distrˡ⇒distrʳ *-comm *-distribˡ-⊓

*-distrib-⊓ : _*_ DistributesOver _⊓_
*-distrib-⊓ = *-distribˡ-⊓ , *-distribʳ-⊓

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
-- Properties of _∸_ and pred

pred[m∸n]≡m∸[1+n] : ∀ m n → pred (m ∸ n) ≡ m ∸ suc n
pred[m∸n]≡m∸[1+n] zero    zero    = refl
pred[m∸n]≡m∸[1+n] (suc m) zero    = refl
pred[m∸n]≡m∸[1+n] zero (suc n)    = refl
pred[m∸n]≡m∸[1+n] (suc m) (suc n) = pred[m∸n]≡m∸[1+n] m n

------------------------------------------------------------------------
-- Properties of _∸_ and _≤_/_<_

m∸n≤m : ∀ m n → m ∸ n ≤ m
m∸n≤m n       zero    = ≤-refl
m∸n≤m zero    (suc n) = ≤-refl
m∸n≤m (suc m) (suc n) = ≤-trans (m∸n≤m m n) (n≤1+n m)

m≮m∸n : ∀ m n → m ≮ m ∸ n
m≮m∸n m       zero    = n≮n m
m≮m∸n (suc m) (suc n) = m≮m∸n m n ∘ ≤-trans (n≤1+n (suc m))

1+m≢m∸n : ∀ {m} n → suc m ≢ m ∸ n
1+m≢m∸n {m} n eq = m≮m∸n m n (≤-reflexive eq)

∸-mono : _∸_ Preserves₂ _≤_ ⟶ _≥_ ⟶ _≤_
∸-mono z≤n         (s≤s n₁≥n₂)    = z≤n
∸-mono (s≤s m₁≤m₂) (s≤s n₁≥n₂)    = ∸-mono m₁≤m₂ n₁≥n₂
∸-mono m₁≤m₂       (z≤n {n = n₁}) = ≤-trans (m∸n≤m _ n₁) m₁≤m₂

∸-monoˡ-≤ : ∀ {m n} o → m ≤ n → m ∸ o ≤ n ∸ o
∸-monoˡ-≤ o m≤n = ∸-mono {u = o} m≤n ≤-refl

∸-monoʳ-≤ : ∀ {m n} o → m ≤ n → o ∸ m ≥ o ∸ n
∸-monoʳ-≤ _ m≤n = ∸-mono ≤-refl m≤n

∸-monoʳ-< : ∀ {m n o} → o < n → n ≤ m → m ∸ n < m ∸ o
∸-monoʳ-< {n = suc n} {zero}  (s≤s o<n) (s≤s n<m) = s≤s (m∸n≤m _ n)
∸-monoʳ-< {n = suc n} {suc o} (s≤s o<n) (s≤s n<m) = ∸-monoʳ-< o<n n<m

∸-cancelʳ-≤ : ∀ {m n o} → m ≤ o → o ∸ n ≤ o ∸ m → m ≤ n
∸-cancelʳ-≤ {_}     {_}     z≤n       _       = z≤n
∸-cancelʳ-≤ {suc m} {zero}  (s≤s _)   o<o∸m   = contradiction o<o∸m (m≮m∸n _ m)
∸-cancelʳ-≤ {suc m} {suc n} (s≤s m≤o) o∸n<o∸m = s≤s (∸-cancelʳ-≤ m≤o o∸n<o∸m)

∸-cancelʳ-< : ∀ {m n o} → o ∸ m < o ∸ n → n < m
∸-cancelʳ-< {zero}  {n}     {o}     o<o∸n   = contradiction o<o∸n (m≮m∸n o n)
∸-cancelʳ-< {suc m} {zero}  {_}     o∸n<o∸m = 0<1+n
∸-cancelʳ-< {suc m} {suc n} {suc o} o∸n<o∸m = s≤s (∸-cancelʳ-< o∸n<o∸m)

∸-cancelˡ-≡ :  ∀ {m n o} → n ≤ m → o ≤ m → m ∸ n ≡ m ∸ o → n ≡ o
∸-cancelˡ-≡ {_}         z≤n       z≤n       _  = refl
∸-cancelˡ-≡ {o = suc o} z≤n       (s≤s _)   eq = contradiction eq (1+m≢m∸n o)
∸-cancelˡ-≡ {n = suc n} (s≤s _)   z≤n       eq = contradiction (sym eq) (1+m≢m∸n n)
∸-cancelˡ-≡ {_}         (s≤s n≤m) (s≤s o≤m) eq = cong suc (∸-cancelˡ-≡ n≤m o≤m eq)

∸-cancelʳ-≡ :  ∀ {m n o} → o ≤ m → o ≤ n → m ∸ o ≡ n ∸ o → m ≡ n
∸-cancelʳ-≡  z≤n       z≤n      eq = eq
∸-cancelʳ-≡ (s≤s o≤m) (s≤s o≤n) eq = cong suc (∸-cancelʳ-≡ o≤m o≤n eq)

m∸n≡0⇒m≤n : ∀ {m n} → m ∸ n ≡ 0 → m ≤ n
m∸n≡0⇒m≤n {zero}  {_}    _   = z≤n
m∸n≡0⇒m≤n {suc m} {suc n} eq = s≤s (m∸n≡0⇒m≤n eq)

m≤n⇒m∸n≡0 : ∀ {m n} → m ≤ n → m ∸ n ≡ 0
m≤n⇒m∸n≡0 {n = n} z≤n      = 0∸n≡0 n
m≤n⇒m∸n≡0 {_}    (s≤s m≤n) = m≤n⇒m∸n≡0 m≤n

m<n⇒0<n∸m : ∀ {m n} → m < n → 0 < n ∸ m
m<n⇒0<n∸m {zero}  {suc n} _         = 0<1+n
m<n⇒0<n∸m {suc m} {suc n} (s≤s m<n) = m<n⇒0<n∸m m<n

m∸n≢0⇒n<m : ∀ {m n} → m ∸ n ≢ 0 → n < m
m∸n≢0⇒n<m {m} {n} m∸n≢0 with n <? m
... | yes n<m = n<m
... | no  n≮m = contradiction (m≤n⇒m∸n≡0 (≮⇒≥ n≮m)) m∸n≢0

m>n⇒m∸n≢0 : ∀ {m n} → m > n → m ∸ n ≢ 0
m>n⇒m∸n≢0 {n = suc n} (s≤s m>n) = m>n⇒m∸n≢0 m>n

---------------------------------------------------------------
-- Properties of _∸_ and _+_

+-∸-comm : ∀ {m} n {o} → o ≤ m → (m + n) ∸ o ≡ (m ∸ o) + n
+-∸-comm {zero}  _ {zero}  _         = refl
+-∸-comm {suc m} _ {zero}  _         = refl
+-∸-comm {suc m} n {suc o} (s≤s o≤m) = +-∸-comm n o≤m

∸-+-assoc : ∀ m n o → (m ∸ n) ∸ o ≡ m ∸ (n + o)
∸-+-assoc zero zero o = refl
∸-+-assoc zero (suc n) o = 0∸n≡0 o
∸-+-assoc (suc m) zero o = refl
∸-+-assoc (suc m) (suc n) o = ∸-+-assoc m n o

+-∸-assoc : ∀ m {n o} → o ≤ n → (m + n) ∸ o ≡ m + (n ∸ o)
+-∸-assoc m (z≤n {n = n})             = begin-equality m + n ∎
+-∸-assoc m (s≤s {m = o} {n = n} o≤n) = begin-equality
  (m + suc n) ∸ suc o  ≡⟨ cong (_∸ suc o) (+-suc m n) ⟩
  suc (m + n) ∸ suc o  ≡⟨⟩
  (m + n) ∸ o          ≡⟨ +-∸-assoc m o≤n ⟩
  m + (n ∸ o)          ∎

m≤n+m∸n : ∀ m n → m ≤ n + (m ∸ n)
m≤n+m∸n zero    n       = z≤n
m≤n+m∸n (suc m) zero    = ≤-refl
m≤n+m∸n (suc m) (suc n) = s≤s (m≤n+m∸n m n)

m+n∸n≡m : ∀ m n → m + n ∸ n ≡ m
m+n∸n≡m m n = begin-equality
  (m + n) ∸ n  ≡⟨ +-∸-assoc m (≤-refl {x = n}) ⟩
  m + (n ∸ n)  ≡⟨ cong (m +_) (n∸n≡0 n) ⟩
  m + 0        ≡⟨ +-identityʳ m ⟩
  m            ∎

m+n∸m≡n : ∀ m n → m + n ∸ m ≡ n
m+n∸m≡n m n = trans (cong (_∸ m) (+-comm m n)) (m+n∸n≡m n m)

m+[n∸m]≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
m+[n∸m]≡n {m} {n} m≤n = begin-equality
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
  suc m ∸ (m ∸ n)   ≡⟨ +-∸-assoc 1 (m∸n≤m m n) ⟩
  suc (m ∸ (m ∸ n)) ≡⟨ cong suc (m∸[m∸n]≡n n≤m) ⟩
  suc n             ∎

[m+n]∸[m+o]≡n∸o : ∀ m n o → (m + n) ∸ (m + o) ≡ n ∸ o
[m+n]∸[m+o]≡n∸o zero    n o = refl
[m+n]∸[m+o]≡n∸o (suc m) n o = [m+n]∸[m+o]≡n∸o m n o

------------------------------------------------------------------------
-- Properties of _∸_ and _*_

*-distribʳ-∸ : _*_ DistributesOverʳ _∸_
*-distribʳ-∸ m       zero    zero    = refl
*-distribʳ-∸ zero    zero    (suc o) = sym (0∸n≡0 (o * zero))
*-distribʳ-∸ (suc m) zero    (suc o) = refl
*-distribʳ-∸ m       (suc n) zero    = refl
*-distribʳ-∸ m       (suc n) (suc o) = begin-equality
  (n ∸ o) * m             ≡⟨ *-distribʳ-∸ m n o ⟩
  n * m ∸ o * m           ≡⟨ sym $ [m+n]∸[m+o]≡n∸o m _ _ ⟩
  m + n * m ∸ (m + o * m) ∎

*-distribˡ-∸ : _*_ DistributesOverˡ _∸_
*-distribˡ-∸ = comm+distrʳ⇒distrˡ *-comm *-distribʳ-∸

*-distrib-∸ : _*_ DistributesOver _∸_
*-distrib-∸ = *-distribˡ-∸ , *-distribʳ-∸

even≢odd :  ∀ m n → 2 * m ≢ suc (2 * n)
even≢odd (suc m) zero    eq = contradiction (suc-injective eq) (m+1+n≢0 m)
even≢odd (suc m) (suc n) eq = even≢odd m n (suc-injective (begin-equality
  suc (2 * m)         ≡⟨ sym (+-suc m _) ⟩
  m + suc (m + 0)     ≡⟨ suc-injective eq ⟩
  suc n + suc (n + 0) ≡⟨ cong suc (+-suc n _) ⟩
  suc (suc (2 * n))   ∎))

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

∸-distribˡ-⊓-⊔ : ∀ m n o → m ∸ (n ⊓ o) ≡ (m ∸ n) ⊔ (m ∸ o)
∸-distribˡ-⊓-⊔ m n o = antimono-≤-distrib-⊓ (∸-monoʳ-≤ m) n o

∸-distribʳ-⊓ : _∸_ DistributesOverʳ _⊓_
∸-distribʳ-⊓ m n o = mono-≤-distrib-⊓ (∸-monoˡ-≤ m) n o

∸-distribˡ-⊔-⊓ : ∀ m n o → m ∸ (n ⊔ o) ≡ (m ∸ n) ⊓ (m ∸ o)
∸-distribˡ-⊔-⊓ m n o = antimono-≤-distrib-⊔ (∸-monoʳ-≤ m) n o

∸-distribʳ-⊔ : _∸_ DistributesOverʳ _⊔_
∸-distribʳ-⊔ m n o = mono-≤-distrib-⊔ (∸-monoˡ-≤ m) n o

------------------------------------------------------------------------
-- Properties of pred
------------------------------------------------------------------------

pred-mono : pred Preserves _≤_ ⟶ _≤_
pred-mono m≤n = ∸-mono m≤n (≤-refl {1})

pred[n]≤n : ∀ {n} → pred n ≤ n
pred[n]≤n {zero}  = z≤n
pred[n]≤n {suc n} = n≤1+n n

≤pred⇒≤ : ∀ {m n} → m ≤ pred n → m ≤ n
≤pred⇒≤ {m} {zero}  le = le
≤pred⇒≤ {m} {suc n} le = ≤-step le

≤⇒pred≤ : ∀ {m n} → m ≤ n → pred m ≤ n
≤⇒pred≤ {zero}  le = le
≤⇒pred≤ {suc m} le = ≤-trans (n≤1+n m) le

<⇒≤pred : ∀ {m n} → m < n → m ≤ pred n
<⇒≤pred (s≤s le) = le

suc[pred[n]]≡n : ∀ {n} → n ≢ 0 → suc (pred n) ≡ n
suc[pred[n]]≡n {zero}  n≢0 = contradiction refl n≢0
suc[pred[n]]≡n {suc n} n≢0 = refl

------------------------------------------------------------------------
-- Properties of ∣_-_∣
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Basic

m≡n⇒∣m-n∣≡0 : ∀ {m n} → m ≡ n → ∣ m - n ∣ ≡ 0
m≡n⇒∣m-n∣≡0 {zero}  refl = refl
m≡n⇒∣m-n∣≡0 {suc m} refl = m≡n⇒∣m-n∣≡0 {m} refl

∣m-n∣≡0⇒m≡n : ∀ {m n} → ∣ m - n ∣ ≡ 0 → m ≡ n
∣m-n∣≡0⇒m≡n {zero}  {zero}  eq = refl
∣m-n∣≡0⇒m≡n {suc m} {suc n} eq = cong suc (∣m-n∣≡0⇒m≡n eq)

m≤n⇒∣n-m∣≡n∸m : ∀ {m n} → m ≤ n → ∣ n - m ∣ ≡ n ∸ m
m≤n⇒∣n-m∣≡n∸m {_} {zero}  z≤n       = refl
m≤n⇒∣n-m∣≡n∸m {_} {suc m} z≤n       = refl
m≤n⇒∣n-m∣≡n∸m {_} {_}     (s≤s m≤n) = m≤n⇒∣n-m∣≡n∸m m≤n

∣m-n∣≡m∸n⇒n≤m : ∀ {m n} → ∣ m - n ∣ ≡ m ∸ n → n ≤ m
∣m-n∣≡m∸n⇒n≤m {zero}  {zero}  eq = z≤n
∣m-n∣≡m∸n⇒n≤m {suc m} {zero}  eq = z≤n
∣m-n∣≡m∸n⇒n≤m {suc m} {suc n} eq = s≤s (∣m-n∣≡m∸n⇒n≤m eq)

∣n-n∣≡0 : ∀ n → ∣ n - n ∣ ≡ 0
∣n-n∣≡0 n = m≡n⇒∣m-n∣≡0 {n} refl

∣m-m+n∣≡n : ∀ m n → ∣ m - m + n ∣ ≡ n
∣m-m+n∣≡n zero    n = refl
∣m-m+n∣≡n (suc m) n = ∣m-m+n∣≡n m n

∣m+n-m+o∣≡∣n-o∣ : ∀ m n o → ∣ m + n - m + o ∣ ≡ ∣ n - o ∣
∣m+n-m+o∣≡∣n-o∣ zero    n o = refl
∣m+n-m+o∣≡∣n-o∣ (suc m) n o = ∣m+n-m+o∣≡∣n-o∣ m n o

m∸n≤∣m-n∣ : ∀ m n → m ∸ n ≤ ∣ m - n ∣
m∸n≤∣m-n∣ m n with ≤-total m n
... | inj₁ m≤n = subst (_≤ ∣ m - n ∣) (sym (m≤n⇒m∸n≡0 m≤n)) z≤n
... | inj₂ n≤m = subst (m ∸ n ≤_) (sym (m≤n⇒∣n-m∣≡n∸m n≤m)) ≤-refl

∣m-n∣≤m⊔n : ∀ m n → ∣ m - n ∣ ≤ m ⊔ n
∣m-n∣≤m⊔n zero    m       = ≤-refl
∣m-n∣≤m⊔n (suc m) zero    = ≤-refl
∣m-n∣≤m⊔n (suc m) (suc n) = ≤-step (∣m-n∣≤m⊔n m n)

∣-∣-identityˡ : LeftIdentity 0 ∣_-_∣
∣-∣-identityˡ x = refl

∣-∣-identityʳ : RightIdentity 0 ∣_-_∣
∣-∣-identityʳ zero    = refl
∣-∣-identityʳ (suc x) = refl

∣-∣-identity : Identity 0 ∣_-_∣
∣-∣-identity = ∣-∣-identityˡ , ∣-∣-identityʳ

∣-∣-comm : Commutative ∣_-_∣
∣-∣-comm zero    zero    = refl
∣-∣-comm zero    (suc n) = refl
∣-∣-comm (suc m) zero    = refl
∣-∣-comm (suc m) (suc n) = ∣-∣-comm m n

∣m-n∣≡[m∸n]∨[n∸m] : ∀ m n → (∣ m - n ∣ ≡ m ∸ n) ⊎ (∣ m - n ∣ ≡ n ∸ m)
∣m-n∣≡[m∸n]∨[n∸m] m n with ≤-total m n
... | inj₂ n≤m = inj₁ $ m≤n⇒∣n-m∣≡n∸m n≤m
... | inj₁ m≤n = inj₂ $ begin-equality
  ∣ m - n ∣ ≡⟨ ∣-∣-comm m n ⟩
  ∣ n - m ∣ ≡⟨ m≤n⇒∣n-m∣≡n∸m m≤n ⟩
  n ∸ m     ∎

private

  *-distribˡ-∣-∣-aux : ∀ a m n → m ≤ n → a * ∣ n - m ∣ ≡ ∣ a * n - a * m ∣
  *-distribˡ-∣-∣-aux a m n m≤n = begin-equality
    a * ∣ n - m ∣     ≡⟨ cong (a *_) (m≤n⇒∣n-m∣≡n∸m m≤n) ⟩
    a * (n ∸ m)       ≡⟨ *-distribˡ-∸ a n m ⟩
    a * n ∸ a * m     ≡⟨ sym $′ m≤n⇒∣n-m∣≡n∸m (*-monoʳ-≤ a m≤n) ⟩
    ∣ a * n - a * m ∣ ∎

*-distribˡ-∣-∣ : _*_ DistributesOverˡ ∣_-_∣
*-distribˡ-∣-∣ a m n with ≤-total m n
... | inj₂ n≤m = *-distribˡ-∣-∣-aux a n m n≤m
... | inj₁ m≤n = begin-equality
  a * ∣ m - n ∣     ≡⟨ cong (a *_) (∣-∣-comm m n) ⟩
  a * ∣ n - m ∣     ≡⟨ *-distribˡ-∣-∣-aux a m n m≤n ⟩
  ∣ a * n - a * m ∣ ≡⟨ ∣-∣-comm (a * n) (a * m) ⟩
  ∣ a * m - a * n ∣ ∎

*-distribʳ-∣-∣ : _*_ DistributesOverʳ ∣_-_∣
*-distribʳ-∣-∣ = comm+distrˡ⇒distrʳ *-comm *-distribˡ-∣-∣

*-distrib-∣-∣ : _*_ DistributesOver ∣_-_∣
*-distrib-∣-∣ = *-distribˡ-∣-∣ , *-distribʳ-∣-∣

m≤n+∣n-m∣ : ∀ m n → m ≤ n + ∣ n - m ∣
m≤n+∣n-m∣ zero    n       = z≤n
m≤n+∣n-m∣ (suc m) zero    = ≤-refl
m≤n+∣n-m∣ (suc m) (suc n) = s≤s (m≤n+∣n-m∣ m n)

m≤n+∣m-n∣ : ∀ m n → m ≤ n + ∣ m - n ∣
m≤n+∣m-n∣ m n = subst (m ≤_) (cong (n +_) (∣-∣-comm n m)) (m≤n+∣n-m∣ m n)

m≤∣m-n∣+n : ∀ m n → m ≤ ∣ m - n ∣ + n
m≤∣m-n∣+n m n = subst (m ≤_) (+-comm n _) (m≤n+∣m-n∣ m n)

∣-∣-triangle : TriangleInequality ∣_-_∣
∣-∣-triangle zero    y       z       = m≤n+∣n-m∣ z y
∣-∣-triangle x       zero    z       = begin
  ∣ x - z ∣     ≤⟨ ∣m-n∣≤m⊔n x z ⟩
  x ⊔ z         ≤⟨ m⊔n≤m+n x z ⟩
  x + z         ≡⟨ cong₂ _+_ (sym (∣-∣-identityʳ x)) refl ⟩
  ∣ x - 0 ∣ + z ∎
  where open ≤-Reasoning
∣-∣-triangle x       y       zero    = begin
  ∣ x - 0 ∣             ≡⟨ ∣-∣-identityʳ x ⟩
  x                     ≤⟨ m≤∣m-n∣+n x y ⟩
  ∣ x - y ∣ + y         ≡⟨ cong₂ _+_ refl (sym (∣-∣-identityʳ y)) ⟩
  ∣ x - y ∣ + ∣ y - 0 ∣ ∎
  where open ≤-Reasoning
∣-∣-triangle (suc x) (suc y) (suc z) = ∣-∣-triangle x y z

------------------------------------------------------------------------
-- Metric structures

∣-∣-isProtoMetric : IsProtoMetric _≡_ ∣_-_∣
∣-∣-isProtoMetric = record
  { isPartialOrder  = ≤-isPartialOrder
  ; ≈-isEquivalence = isEquivalence
  ; cong            = cong₂ ∣_-_∣
  ; nonNegative     = z≤n
  }

∣-∣-isPreMetric : IsPreMetric _≡_ ∣_-_∣
∣-∣-isPreMetric = record
  { isProtoMetric = ∣-∣-isProtoMetric
  ; ≈⇒0           = m≡n⇒∣m-n∣≡0
  }

∣-∣-isQuasiSemiMetric : IsQuasiSemiMetric _≡_ ∣_-_∣
∣-∣-isQuasiSemiMetric = record
  { isPreMetric = ∣-∣-isPreMetric
  ; 0⇒≈         = ∣m-n∣≡0⇒m≡n
  }

∣-∣-isSemiMetric : IsSemiMetric _≡_ ∣_-_∣
∣-∣-isSemiMetric = record
  { isQuasiSemiMetric = ∣-∣-isQuasiSemiMetric
  ; sym               = ∣-∣-comm
  }

∣-∣-isMetric : IsMetric _≡_ ∣_-_∣
∣-∣-isMetric = record
  { isSemiMetric = ∣-∣-isSemiMetric
  ; triangle     = ∣-∣-triangle
  }

------------------------------------------------------------------------
-- Metric bundles

∣-∣-quasiSemiMetric : QuasiSemiMetric 0ℓ 0ℓ
∣-∣-quasiSemiMetric = record
  { isQuasiSemiMetric = ∣-∣-isQuasiSemiMetric
  }

∣-∣-semiMetric : SemiMetric 0ℓ 0ℓ
∣-∣-semiMetric = record
  { isSemiMetric = ∣-∣-isSemiMetric
  }

∣-∣-preMetric : PreMetric 0ℓ 0ℓ
∣-∣-preMetric = record
  { isPreMetric = ∣-∣-isPreMetric
  }

∣-∣-metric : Metric 0ℓ 0ℓ
∣-∣-metric = record
  { isMetric = ∣-∣-isMetric
  }

------------------------------------------------------------------------
-- Properties of ⌊_/2⌋ and ⌈_/2⌉
------------------------------------------------------------------------

⌊n/2⌋-mono : ⌊_/2⌋ Preserves _≤_ ⟶ _≤_
⌊n/2⌋-mono z≤n             = z≤n
⌊n/2⌋-mono (s≤s z≤n)       = z≤n
⌊n/2⌋-mono (s≤s (s≤s m≤n)) = s≤s (⌊n/2⌋-mono m≤n)

⌈n/2⌉-mono : ⌈_/2⌉ Preserves _≤_ ⟶ _≤_
⌈n/2⌉-mono m≤n = ⌊n/2⌋-mono (s≤s m≤n)

⌊n/2⌋≤⌈n/2⌉ : ∀ n → ⌊ n /2⌋ ≤ ⌈ n /2⌉
⌊n/2⌋≤⌈n/2⌉ zero          = z≤n
⌊n/2⌋≤⌈n/2⌉ (suc zero)    = z≤n
⌊n/2⌋≤⌈n/2⌉ (suc (suc n)) = s≤s (⌊n/2⌋≤⌈n/2⌉ n)

⌊n/2⌋+⌈n/2⌉≡n : ∀ n → ⌊ n /2⌋ + ⌈ n /2⌉ ≡ n
⌊n/2⌋+⌈n/2⌉≡n zero    = refl
⌊n/2⌋+⌈n/2⌉≡n (suc n) = begin-equality
  ⌊ suc n /2⌋ + suc ⌊ n /2⌋   ≡⟨ +-comm ⌊ suc n /2⌋ (suc ⌊ n /2⌋) ⟩
  suc ⌊ n /2⌋ + ⌊ suc n /2⌋   ≡⟨⟩
  suc (⌊ n /2⌋ + ⌊ suc n /2⌋) ≡⟨ cong suc (⌊n/2⌋+⌈n/2⌉≡n n) ⟩
  suc n                       ∎

⌊n/2⌋≤n : ∀ n → ⌊ n /2⌋ ≤ n
⌊n/2⌋≤n zero          = z≤n
⌊n/2⌋≤n (suc zero)    = z≤n
⌊n/2⌋≤n (suc (suc n)) = s≤s (≤-step (⌊n/2⌋≤n n))

⌊n/2⌋<n : ∀ n → ⌊ suc n /2⌋ < suc n
⌊n/2⌋<n zero    = s≤s z≤n
⌊n/2⌋<n (suc n) = s≤s (s≤s (⌊n/2⌋≤n n))

⌈n/2⌉≤n : ∀ n → ⌈ n /2⌉ ≤ n
⌈n/2⌉≤n zero = z≤n
⌈n/2⌉≤n (suc n) = s≤s (⌊n/2⌋≤n n)

⌈n/2⌉<n : ∀ n → ⌈ suc (suc n) /2⌉ < suc (suc n)
⌈n/2⌉<n n = s≤s (⌊n/2⌋<n n)

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
m ≤′? n = map′ ≤⇒≤′ ≤′⇒≤ (m ≤? n)

_<′?_ : Decidable _<′_
m <′? n = suc m ≤′? n

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
m<ᵇn⇒1+m+[n-1+m]≡n m n lt = m+[n∸m]≡n (<ᵇ⇒< m n lt)

m<ᵇ1+m+n : ∀ m {n} → T (m <ᵇ suc (m + n))
m<ᵇ1+m+n m = <⇒<ᵇ (m≤m+n (suc m) _)

<ᵇ⇒<″ : ∀ {m n} → T (m <ᵇ n) → m <″ n
<ᵇ⇒<″ {m} {n} leq = less-than-or-equal (m+[n∸m]≡n (<ᵇ⇒< m n leq))

<″⇒<ᵇ : ∀ {m n} → m <″ n → T (m <ᵇ n)
<″⇒<ᵇ {m} (less-than-or-equal refl) = <⇒<ᵇ (m≤m+n (suc m) _)

-- equivalence to _≤_

≤″⇒≤ : _≤″_ ⇒ _≤_
≤″⇒≤ {zero}  (less-than-or-equal refl) = z≤n
≤″⇒≤ {suc m} (less-than-or-equal refl) =
  s≤s (≤″⇒≤ (less-than-or-equal refl))

≤⇒≤″ : _≤_ ⇒ _≤″_
≤⇒≤″ = less-than-or-equal ∘ m+[n∸m]≡n

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

0≤‴n : ∀{n} → 0 ≤‴ n
0≤‴n {n} = m≤‴m+k refl

<ᵇ⇒<‴ : ∀ {m n} → T (m <ᵇ n) → m <‴ n
<ᵇ⇒<‴ {m} {n} leq = ≤″⇒≤‴ (<ᵇ⇒<″ leq)

<‴⇒<ᵇ : ∀ {m n} → m <‴ n → T (m <ᵇ n)
<‴⇒<ᵇ leq = <″⇒<ᵇ (≤‴⇒≤″ leq)

infix 4 _<‴?_ _≤‴?_ _≥‴?_ _>‴?_

_<‴?_ : Decidable _<‴_
m <‴? n = map′ <ᵇ⇒<‴ <‴⇒<ᵇ (T? (m <ᵇ n))

_≤‴?_ : Decidable _≤‴_
zero ≤‴? n = yes 0≤‴n
suc m ≤‴? n = m <‴? n

_≥‴?_ : Decidable _≥‴_
_≥‴?_ = flip _≤‴?_

_>‴?_ : Decidable _>‴_
_>‴?_ = flip _<‴?_

≤⇒≤‴ : _≤_ ⇒ _≤‴_
≤⇒≤‴ = ≤″⇒≤‴ ∘ ≤⇒≤″

≤‴⇒≤ : _≤‴_ ⇒ _≤_
≤‴⇒≤ = ≤″⇒≤ ∘ ≤‴⇒≤″

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
isCommutativeSemiring                 = +-*-isCommutativeSemiring
{-# WARNING_ON_USAGE isCommutativeSemiring
"Warning: isCommutativeSemiring was deprecated in v0.14.
Please use *-+-isCommutativeSemiring instead."
#-}
commutativeSemiring                   = +-*-commutativeSemiring
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

¬i+1+j≤i  = m+1+n≰m
{-# WARNING_ON_USAGE ¬i+1+j≤i
"Warning: ¬i+1+j≤i was deprecated in v0.15.
Please use m+1+n≰m instead."
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

-- Version 1.1

i+1+j≢i = m+1+n≢m
{-# WARNING_ON_USAGE i+1+j≢i
"Warning: i+1+j≢i was deprecated in v1.1.
Please use m+1+n≢m instead."
#-}
i+j≡0⇒i≡0 = m+n≡0⇒m≡0
{-# WARNING_ON_USAGE i+j≡0⇒i≡0
"Warning: i+j≡0⇒i≡0 was deprecated in v1.1.
Please use m+n≡0⇒m≡0 instead."
#-}
i+j≡0⇒j≡0 = m+n≡0⇒n≡0
{-# WARNING_ON_USAGE i+j≡0⇒j≡0
"Warning: i+j≡0⇒j≡0 was deprecated in v1.1.
Please use m+n≡0⇒n≡0 instead."
#-}
i+1+j≰i = m+1+n≰m
{-# WARNING_ON_USAGE i+1+j≰i
"Warning: i+1+j≰i was deprecated in v1.1.
Please use m+1+n≰m instead."
#-}
i*j≡0⇒i≡0∨j≡0 = m*n≡0⇒m≡0∨n≡0
{-# WARNING_ON_USAGE i*j≡0⇒i≡0∨j≡0
"Warning: i*j≡0⇒i≡0∨j≡0 was deprecated in v1.1.
Please use m*n≡0⇒m≡0∨n≡0 instead."
#-}
i*j≡1⇒i≡1 = m*n≡1⇒m≡1
{-# WARNING_ON_USAGE i*j≡1⇒i≡1
"Warning: i*j≡1⇒i≡1 was deprecated in v1.1.
Please use m*n≡1⇒m≡1 instead."
#-}
i*j≡1⇒j≡1 = m*n≡1⇒n≡1
{-# WARNING_ON_USAGE i*j≡1⇒j≡1
"Warning: i*j≡1⇒j≡1 was deprecated in v1.1.
Please use m*n≡1⇒n≡1 instead."
#-}
i^j≡0⇒i≡0 = m^n≡0⇒m≡0
{-# WARNING_ON_USAGE i^j≡0⇒i≡0
"Warning: i^j≡0⇒i≡0 was deprecated in v1.1.
Please use m^n≡0⇒m≡0 instead."
#-}
i^j≡1⇒j≡0∨i≡1 = m^n≡1⇒n≡0∨m≡1
{-# WARNING_ON_USAGE i^j≡1⇒j≡0∨i≡1
"Warning: i^j≡1⇒j≡0∨i≡1 was deprecated in v1.1.
Please use m^n≡1⇒n≡0∨m≡1 instead."
#-}
[i+j]∸[i+k]≡j∸k = [m+n]∸[m+o]≡n∸o
{-# WARNING_ON_USAGE [i+j]∸[i+k]≡j∸k
"Warning: [i+j]∸[i+k]≡j∸k was deprecated in v1.1.
Please use [m+n]∸[m+o]≡n∸o instead."
#-}
m≢0⇒suc[pred[m]]≡m = suc[pred[n]]≡n
{-# WARNING_ON_USAGE m≢0⇒suc[pred[m]]≡m
"Warning: m≢0⇒suc[pred[m]]≡m was deprecated in v1.1.
Please use suc[pred[n]]≡n instead."
#-}
n≡m⇒∣n-m∣≡0 = m≡n⇒∣m-n∣≡0
{-# WARNING_ON_USAGE n≡m⇒∣n-m∣≡0
"Warning: n≡m⇒∣n-m∣≡0 was deprecated in v1.1.
Please use m≡n⇒∣m-n∣≡0 instead."
#-}
∣n-m∣≡0⇒n≡m = ∣m-n∣≡0⇒m≡n
{-# WARNING_ON_USAGE ∣n-m∣≡0⇒n≡m
"Warning: ∣n-m∣≡0⇒n≡m was deprecated in v1.1.
Please use ∣m-n∣≡0⇒m≡n instead."
#-}
∣n-m∣≡n∸m⇒m≤n = ∣m-n∣≡m∸n⇒n≤m
{-# WARNING_ON_USAGE ∣n-m∣≡n∸m⇒m≤n
"Warning: ∣n-m∣≡n∸m⇒m≤n was deprecated in v1.1.
Please use ∣m-n∣≡m∸n⇒n≤m instead."
#-}
∣n-n+m∣≡m = ∣m-m+n∣≡n
{-# WARNING_ON_USAGE ∣n-n+m∣≡m
"Warning: ∣n-n+m∣≡m was deprecated in v1.1.
Please use ∣m-m+n∣≡n instead."
#-}
∣n+m-n+o∣≡∣m-o| = ∣m+n-m+o∣≡∣n-o∣
{-# WARNING_ON_USAGE ∣n+m-n+o∣≡∣m-o|
"Warning: ∣n+m-n+o∣≡∣m-o| was deprecated in v1.1.
Please use ∣m+n-m+o∣≡∣n-o∣ instead."
#-}
∣m+n-m+o∣≡∣n-o| = ∣m+n-m+o∣≡∣n-o∣
{-# WARNING_ON_USAGE ∣m+n-m+o∣≡∣n-o|
"Warning: ∣m+n-m+o∣≡∣n-o| was deprecated in v1.6.
Please use ∣m+n-m+o∣≡∣n-o∣ instead. Note the final is a \\| rather than a |"
#-}
n∸m≤∣n-m∣ = m∸n≤∣m-n∣
{-# WARNING_ON_USAGE n∸m≤∣n-m∣
"Warning: n∸m≤∣n-m∣ was deprecated in v1.1.
Please use m∸n≤∣m-n∣ instead."
#-}
∣n-m∣≤n⊔m = ∣m-n∣≤m⊔n
{-# WARNING_ON_USAGE ∣n-m∣≤n⊔m
"Warning: ∣n-m∣≤n⊔m was deprecated in v1.1.
Please use ∣m-n∣≤m⊔n instead."
#-}
n≤m+n : ∀ m n → n ≤ m + n
n≤m+n m n = subst (n ≤_) (+-comm n m) (m≤m+n n m)
{-# WARNING_ON_USAGE n≤m+n
"Warning: n≤m+n was deprecated in v1.1.
Please use m≤n+m instead (note, you will need to switch the argument order)."
#-}
n≤m+n∸m : ∀ m n → n ≤ m + (n ∸ m)
n≤m+n∸m m       zero    = z≤n
n≤m+n∸m zero    (suc n) = ≤-refl
n≤m+n∸m (suc m) (suc n) = s≤s (n≤m+n∸m m n)
{-# WARNING_ON_USAGE n≤m+n∸m
"Warning: n≤m+n∸m was deprecated in v1.1.
Please use m≤n+m∸n instead (note, you will need to switch the argument order)."
#-}
∣n-m∣≡[n∸m]∨[m∸n] : ∀ m n → (∣ n - m ∣ ≡ n ∸ m) ⊎ (∣ n - m ∣ ≡ m ∸ n)
∣n-m∣≡[n∸m]∨[m∸n] m n with ≤-total m n
... | inj₁ m≤n = inj₁ $ m≤n⇒∣n-m∣≡n∸m m≤n
... | inj₂ n≤m = inj₂ $ begin-equality
  ∣ n - m ∣ ≡⟨ ∣-∣-comm n m ⟩
  ∣ m - n ∣ ≡⟨ m≤n⇒∣n-m∣≡n∸m n≤m ⟩
  m ∸ n     ∎
{-# WARNING_ON_USAGE ∣n-m∣≡[n∸m]∨[m∸n]
"Warning: ∣n-m∣≡[n∸m]∨[m∸n] was deprecated in v1.1.
Please use ∣m-n∣≡[m∸n]∨[n∸m] instead (note, you will need to switch the argument order)."
#-}

-- Version 1.2

+-*-suc = *-suc
{-# WARNING_ON_USAGE +-*-suc
"Warning: +-*-suc was deprecated in v1.2.
Please use *-suc instead."
#-}

n∸m≤n : ∀ m n → n ∸ m ≤ n
n∸m≤n m n = m∸n≤m n m
{-# WARNING_ON_USAGE n∸m≤n
"Warning: n∸m≤n was deprecated in v1.2.
Please use m∸n≤m instead (note, you will need to switch the argument order)."
#-}

-- Version 1.3

∀[m≤n⇒m≢o]⇒o<n : ∀ n o → (∀ {m} → m ≤ n → m ≢ o) → n < o
∀[m≤n⇒m≢o]⇒o<n = ∀[m≤n⇒m≢o]⇒n<o
{-# WARNING_ON_USAGE ∀[m≤n⇒m≢o]⇒o<n
"Warning: ∀[m≤n⇒m≢o]⇒o<n was deprecated in v1.3.
Please use ∀[m≤n⇒m≢o]⇒n<o instead."
#-}
∀[m<n⇒m≢o]⇒o≤n : ∀ n o → (∀ {m} → m < n → m ≢ o) → n ≤ o
∀[m<n⇒m≢o]⇒o≤n = ∀[m<n⇒m≢o]⇒n≤o
{-# WARNING_ON_USAGE ∀[m<n⇒m≢o]⇒o≤n
"Warning: ∀[m<n⇒m≢o]⇒o≤n was deprecated in v1.3.
Please use ∀[m<n⇒m≢o]⇒n≤o instead."
#-}

-- Version 1.4

*-+-isSemiring = +-*-isSemiring
{-# WARNING_ON_USAGE *-+-isSemiring
"Warning: *-+-isSemiring was deprecated in v1.4.
Please use +-*-isSemiring instead."
#-}
*-+-isCommutativeSemiring = +-*-isCommutativeSemiring
{-# WARNING_ON_USAGE *-+-isCommutativeSemiring
"Warning: *-+-isCommutativeSemiring was deprecated in v1.4.
Please use +-*-isCommutativeSemiring instead."
#-}
*-+-semiring = +-*-semiring
{-# WARNING_ON_USAGE *-+-semiring
"Warning: *-+-semiring was deprecated in v1.4.
Please use +-*-semiring instead."
#-}
*-+-commutativeSemiring = +-*-commutativeSemiring
{-# WARNING_ON_USAGE *-+-commutativeSemiring
"Warning: *-+-commutativeSemiring was deprecated in v1.4.
Please use +-*-commutativeSemiring instead."
#-}

-- Version 1.6

m≤n⇒n⊔m≡n = m≥n⇒m⊔n≡m
{-# WARNING_ON_USAGE m≤n⇒n⊔m≡n
"Warning: m≤n⇒n⊔m≡n was deprecated in v1.6. Please use m≥n⇒m⊔n≡m instead."
#-}
m≤n⇒n⊓m≡m = m≥n⇒m⊓n≡n
{-# WARNING_ON_USAGE m≤n⇒n⊓m≡m
"Warning: m≤n⇒n⊓m≡m was deprecated in v1.6. Please use m≥n⇒m⊓n≡n instead."
#-}
n⊔m≡m⇒n≤m = m⊔n≡n⇒m≤n
{-# WARNING_ON_USAGE n⊔m≡m⇒n≤m
"Warning: n⊔m≡m⇒n≤m was deprecated in v1.6. Please use m⊔n≡n⇒m≤n instead."
#-}
n⊔m≡n⇒m≤n = m⊔n≡m⇒n≤m
{-# WARNING_ON_USAGE n⊔m≡n⇒m≤n
"Warning: n⊔m≡n⇒m≤n was deprecated in v1.6. Please use m⊔n≡m⇒n≤m instead."
#-}
n≤m⊔n = m≤n⊔m
{-# WARNING_ON_USAGE n≤m⊔n
"Warning: n≤m⊔n was deprecated in v1.6. Please use m≤n⊔m instead."
#-}
⊔-least = ⊔-lub
{-# WARNING_ON_USAGE ⊔-least
"Warning: ⊔-least was deprecated in v1.6. Please use ⊔-lub instead."
#-}
⊓-greatest = ⊓-glb
{-# WARNING_ON_USAGE ⊓-greatest
"Warning: ⊓-greatest was deprecated in v1.6. Please use ⊓-glb instead."
#-}
⊔-pres-≤m = ⊔-lub
{-# WARNING_ON_USAGE ⊔-pres-≤m
"Warning: ⊔-pres-≤m was deprecated in v1.6. Please use ⊔-lub instead."
#-}
⊓-pres-m≤ = ⊓-glb
{-# WARNING_ON_USAGE ⊓-pres-m≤
"Warning: ⊓-pres-m≤ was deprecated in v1.6. Please use ⊓-glb instead."
#-}
⊔-abs-⊓ = ⊔-absorbs-⊓
{-# WARNING_ON_USAGE ⊔-abs-⊓
"Warning: ⊔-abs-⊓ was deprecated in v1.6. Please use ⊔-absorbs-⊓ instead."
#-}
⊓-abs-⊔ = ⊓-absorbs-⊔
{-# WARNING_ON_USAGE ⊓-abs-⊔
"Warning: ⊓-abs-⊔ was deprecated in v1.6. Please use ⊓-absorbs-⊔ instead."
#-}
