------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties about natural number operations
------------------------------------------------------------------------

-- See README.Data.Nat for some examples showing how this module can be
-- used.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Properties where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Algebra.Bundles
  using (Magma; Semigroup; CommutativeSemigroup; CommutativeMonoid; Monoid
        ; Semiring; CommutativeSemiring; CommutativeSemiringWithoutOne)
open import Algebra.Definitions.RawMagma using (_,_)
open import Algebra.Morphism
open import Algebra.Consequences.Propositional
  using (comm∧cancelˡ⇒cancelʳ; comm∧distrʳ⇒distrˡ; comm∧distrˡ⇒distrʳ
        ; comm⇒sym[distribˡ])
open import Algebra.Construct.NaturalChoice.Base
  using (MinOperator; MaxOperator)
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp
import Algebra.Lattice.Construct.NaturalChoice.MinMaxOp as LatticeMinMaxOp
import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Bool.Properties using (T?)
open import Data.Nat.Base
open import Data.Product.Base using (∃; _×_; _,_)
open import Data.Sum.Base as Sum using (inj₁; inj₂; _⊎_; [_,_]′)
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_; flip; _$_; id; _∘′_; _$′_)
open import Function.Bundles using (_↣_)
open import Function.Metric.Nat
  using (TriangleInequality; IsProtoMetric; IsPreMetric; IsQuasiSemiMetric
        ; IsSemiMetric; IsMetric; PreMetric; QuasiSemiMetric
        ; SemiMetric; Metric)
open import Level using (0ℓ)
open import Relation.Unary as U using (Pred)
open import Relation.Binary.Core
  using (_⇒_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary
open import Relation.Binary.Consequences using (flip-Connex; wlog)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable
  using (True; via-injection; map′; recompute)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (fromEquivalence)

open import Algebra.Definitions {A = ℕ} _≡_
  hiding (LeftCancellative; RightCancellative; Cancellative)
open import Algebra.Definitions
  using (LeftCancellative; RightCancellative; Cancellative)
open import Algebra.Structures {A = ℕ} _≡_


private
  variable
    m n o k : ℕ


------------------------------------------------------------------------
-- Properties of NonZero
------------------------------------------------------------------------

nonZero? : U.Decidable NonZero
nonZero? zero    = no NonZero.nonZero
nonZero? (suc n) = yes _

------------------------------------------------------------------------
-- Properties of NonTrivial
------------------------------------------------------------------------

nonTrivial? : U.Decidable NonTrivial
nonTrivial? 0      = no λ()
nonTrivial? 1      = no λ()
nonTrivial? (2+ n) = yes _

------------------------------------------------------------------------
-- Properties of _≡_
------------------------------------------------------------------------

suc-injective : suc m ≡ suc n → m ≡ n
suc-injective = cong pred

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
_≟_ : DecidableEquality ℕ
m ≟ n = map′ (≡ᵇ⇒≡ m n) (≡⇒≡ᵇ m n) (T? (m ≡ᵇ n))

≡-irrelevant : Irrelevant {A = ℕ} _≡_
≡-irrelevant = Decidable⇒UIP.≡-irrelevant _≟_

≟-diag : (eq : m ≡ n) → (m ≟ n) ≡ yes eq
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

0≢1+n : 0 ≢ suc n
0≢1+n ()

1+n≢0 : suc n ≢ 0
1+n≢0 ()

1+n≢n : suc n ≢ n
1+n≢n {suc n} = 1+n≢n ∘ suc-injective

------------------------------------------------------------------------
-- Properties of _<ᵇ_
------------------------------------------------------------------------

<ᵇ⇒< : ∀ m n → T (m <ᵇ n) → m < n
<ᵇ⇒< zero    (suc n) m<n = z<s
<ᵇ⇒< (suc m) (suc n) m<n = s<s (<ᵇ⇒< m n m<n)

<⇒<ᵇ : m < n → T (m <ᵇ n)
<⇒<ᵇ z<s               = tt
<⇒<ᵇ (s<s m<n@(s≤s _)) = <⇒<ᵇ m<n

<ᵇ-reflects-< : ∀ m n → Reflects (m < n) (m <ᵇ n)
<ᵇ-reflects-< m n = fromEquivalence (<ᵇ⇒< m n) <⇒<ᵇ

------------------------------------------------------------------------
-- Properties of _≤ᵇ_
------------------------------------------------------------------------

≤ᵇ⇒≤ : ∀ m n → T (m ≤ᵇ n) → m ≤ n
≤ᵇ⇒≤ zero    n m≤n = z≤n
≤ᵇ⇒≤ (suc m) n m≤n = <ᵇ⇒< m n m≤n

≤⇒≤ᵇ : m ≤ n → T (m ≤ᵇ n)
≤⇒≤ᵇ z≤n         = tt
≤⇒≤ᵇ m≤n@(s≤s _) = <⇒<ᵇ m≤n

≤ᵇ-reflects-≤ : ∀ m n → Reflects (m ≤ n) (m ≤ᵇ n)
≤ᵇ-reflects-≤ m n = fromEquivalence (≤ᵇ⇒≤ m n) ≤⇒≤ᵇ

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------

≰⇒≥ : _≰_ ⇒ _≥_
≰⇒≥ {m} {zero} m≰n = z≤n
≰⇒≥ {zero} {suc n} m≰n = contradiction z≤n m≰n
≰⇒≥ {suc m} {suc n} m≰n = s≤s (≰⇒≥ (m≰n ∘ s≤s))

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

≤-total : Total _≤_
≤-total m n with m ≤? n
... | true because m≤n = inj₁ (invert m≤n)
... | false because m≰n = inj₂ (≰⇒≥ (invert m≰n))

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

s≤s-injective : {p q : m ≤ n} → s≤s p ≡ s≤s q → p ≡ q
s≤s-injective refl = refl

suc[m]≤n⇒m≤pred[n] : suc m ≤ n → m ≤ pred n
suc[m]≤n⇒m≤pred[n] {n = suc _} = s≤s⁻¹

m≤pred[n]⇒suc[m]≤n : .{{NonZero n}} → m ≤ pred n → suc m ≤ n
m≤pred[n]⇒suc[m]≤n {n = suc _} = s≤s

≤-pred : suc m ≤ suc n → m ≤ n
≤-pred = suc[m]≤n⇒m≤pred[n]

m≤n⇒m≤1+n : m ≤ n → m ≤ 1 + n
m≤n⇒m≤1+n z≤n       = z≤n
m≤n⇒m≤1+n (s≤s m≤n) = s≤s (m≤n⇒m≤1+n m≤n)

n≤1+n : ∀ n → n ≤ 1 + n
n≤1+n _ = m≤n⇒m≤1+n ≤-refl

1+n≰n : 1 + n ≰ n
1+n≰n (s≤s 1+n≤n) = 1+n≰n 1+n≤n

n≤0⇒n≡0 : n ≤ 0 → n ≡ 0
n≤0⇒n≡0 z≤n = refl

n≤1⇒n≡0∨n≡1 : n ≤ 1 → n ≡ 0 ⊎ n ≡ 1
n≤1⇒n≡0∨n≡1 z≤n       = inj₁ refl
n≤1⇒n≡0∨n≡1 (s≤s z≤n) = inj₂ refl

------------------------------------------------------------------------
-- Properties of _<_
------------------------------------------------------------------------

-- Relationships between the various relations

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ z<s               = z≤n
<⇒≤ (s<s m<n@(s≤s _)) = s≤s (<⇒≤ m<n)

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
≰⇒> {suc m} {zero}  _   = z<s
≰⇒> {suc m} {suc n} m≰n = s<s (≰⇒> (m≰n ∘ s≤s))

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ {_}     {zero}  _       = z≤n
≮⇒≥ {zero}  {suc j} 1≮j+1   = contradiction z<s 1≮j+1
≮⇒≥ {suc i} {suc j} i+1≮j+1 = s≤s (≮⇒≥ (i+1≮j+1 ∘ s<s))

≤∧≢⇒< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤∧≢⇒< {_} {zero}  z≤n       m≢n     = contradiction refl m≢n
≤∧≢⇒< {_} {suc n} z≤n       m≢n     = z<s
≤∧≢⇒< {_} {suc n} (s≤s m≤n) 1+m≢1+n =
  s<s (≤∧≢⇒< m≤n (1+m≢1+n ∘ cong suc))

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
<-irrefl refl (s<s n<n) = <-irrefl refl n<n

<-asym : Asymmetric _<_
<-asym (s<s n<m) (s<s m<n) = <-asym n<m m<n

<-trans : Transitive _<_
<-trans (s≤s i≤j) (s≤s j<k) = s≤s (≤-trans i≤j (≤-trans (n≤1+n _) j<k))

≤-<-trans : LeftTrans _≤_ _<_
≤-<-trans m≤n (s<s n≤o) = s≤s (≤-trans m≤n n≤o)

<-≤-trans : RightTrans _<_ _≤_
<-≤-trans (s<s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

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
<-isStrictTotalOrder = isStrictTotalOrderᶜ record
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

s<s-injective : {p q : m < n} → s<s p ≡ s<s q → p ≡ q
s<s-injective refl = refl

<-pred : suc m < suc n → m < n
<-pred = s<s⁻¹

m<n⇒m<1+n : m < n → m < 1 + n
m<n⇒m<1+n z<s               = z<s
m<n⇒m<1+n (s<s m<n@(s≤s _)) = s<s (m<n⇒m<1+n m<n)

n≮0 : n ≮ 0
n≮0 ()

n≮n : ∀ n → n ≮ n -- implicit?
n≮n n = <-irrefl (refl {x = n})

0<1+n : 0 < suc n
0<1+n = z<s

n<1+n : ∀ n → n < suc n
n<1+n n = ≤-refl

n<1⇒n≡0 : n < 1 → n ≡ 0
n<1⇒n≡0 (s≤s n≤0) = n≤0⇒n≡0 n≤0

n>0⇒n≢0 : n > 0 → n ≢ 0
n>0⇒n≢0 {suc n} _ ()

n≢0⇒n>0 : n ≢ 0 → n > 0
n≢0⇒n>0 {zero}  0≢0 =  contradiction refl 0≢0
n≢0⇒n>0 {suc n} _   =  0<1+n

m<n⇒0<n : m < n → 0 < n
m<n⇒0<n = ≤-trans 0<1+n

m<n⇒n≢0 : m < n → n ≢ 0
m<n⇒n≢0 (s≤s m≤n) ()

m<n⇒m≤1+n : m < n → m ≤ suc n
m<n⇒m≤1+n = m≤n⇒m≤1+n ∘ <⇒≤

m<1+n⇒m<n∨m≡n :  ∀ {m n} → m < suc n → m < n ⊎ m ≡ n
m<1+n⇒m<n∨m≡n {0}     {0}     _           = inj₂ refl
m<1+n⇒m<n∨m≡n {0}     {suc n} _           = inj₁ 0<1+n
m<1+n⇒m<n∨m≡n {suc m} {suc n} (s<s m<1+n) = Sum.map s<s (cong suc) (m<1+n⇒m<n∨m≡n m<1+n)

m≤n⇒m<n∨m≡n : m ≤ n → m < n ⊎ m ≡ n
m≤n⇒m<n∨m≡n m≤n = m<1+n⇒m<n∨m≡n (s≤s m≤n)

m<1+n⇒m≤n : m < suc n → m ≤ n
m<1+n⇒m≤n (s≤s m≤n) = m≤n

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
  rec o<n refl = m<n⇒m≢o (s<s o<n) refl

------------------------------------------------------------------------
-- A module for reasoning about the _≤_ and _<_ relations
------------------------------------------------------------------------

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-asym
    <-trans
    (resp₂ _<_)
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)

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
+-cancelˡ-≡ zero    _ _ eq = eq
+-cancelˡ-≡ (suc m) _ _ eq = +-cancelˡ-≡ m _ _ (cong pred eq)

+-cancelʳ-≡ : RightCancellative _≡_ _+_
+-cancelʳ-≡ = comm∧cancelˡ⇒cancelʳ +-comm +-cancelˡ-≡

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

m+1+n≢n : ∀ m {n} → m + suc n ≢ n
m+1+n≢n m {n} rewrite +-suc m n = ≢-sym (m≢1+n+m n)

m+1+n≢0 : ∀ m {n} → m + suc n ≢ 0
m+1+n≢0 m {n} rewrite +-suc m n = λ()

m+n≡0⇒m≡0 : ∀ m {n} → m + n ≡ 0 → m ≡ 0
m+n≡0⇒m≡0 zero eq = refl

m+n≡0⇒n≡0 : ∀ m {n} → m + n ≡ 0 → n ≡ 0
m+n≡0⇒n≡0 m {n} m+n≡0 = m+n≡0⇒m≡0 n (trans (+-comm n m) (m+n≡0))

------------------------------------------------------------------------
-- Properties of _+_ and _≤_/_<_

+-cancelˡ-≤ : LeftCancellative _≤_ _+_
+-cancelˡ-≤ zero    _ _ le       = le
+-cancelˡ-≤ (suc m) _ _ (s≤s le) = +-cancelˡ-≤ m _ _ le

+-cancelʳ-≤ : RightCancellative _≤_ _+_
+-cancelʳ-≤ m n o le =
  +-cancelˡ-≤ m _ _ (subst₂ _≤_ (+-comm n m) (+-comm o m) le)

+-cancel-≤ : Cancellative _≤_ _+_
+-cancel-≤ = +-cancelˡ-≤ , +-cancelʳ-≤

+-cancelˡ-< : LeftCancellative _<_ _+_
+-cancelˡ-< m n o = +-cancelˡ-≤ m (suc n) o ∘ subst (_≤ m + o) (sym (+-suc m n))

+-cancelʳ-< : RightCancellative _<_ _+_
+-cancelʳ-< m n o n+m<o+m = +-cancelʳ-≤ m (suc n) o n+m<o+m

+-cancel-< : Cancellative _<_ _+_
+-cancel-< = +-cancelˡ-< , +-cancelʳ-<

m≤n⇒m≤o+n : ∀ o → m ≤ n → m ≤ o + n
m≤n⇒m≤o+n zero    m≤n = m≤n
m≤n⇒m≤o+n (suc o) m≤n = m≤n⇒m≤1+n (m≤n⇒m≤o+n o m≤n)

m≤n⇒m≤n+o : ∀ o → m ≤ n → m ≤ n + o
m≤n⇒m≤n+o {m} o m≤n = subst (m ≤_) (+-comm o _) (m≤n⇒m≤o+n o m≤n)

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero    n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)

m≤n+m : ∀ m n → m ≤ n + m
m≤n+m m n = subst (m ≤_) (+-comm m n) (m≤m+n m n)

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
+-mono-<-≤ {_} {suc n} z<s               o≤p = s≤s (m≤n⇒m≤o+n n o≤p)
+-mono-<-≤ {_} {_}     (s<s m<n@(s≤s _)) o≤p = s≤s (+-mono-<-≤ m<n o≤p)

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
m+1+n≰m (suc m) m+1+n≤m = m+1+n≰m m (s≤s⁻¹ m+1+n≤m)

m<m+n : ∀ m {n} → n > 0 → m < m + n
m<m+n zero    n>0 = n>0
m<m+n (suc m) n>0 = s<s (m<m+n m n>0)

m<n+m : ∀ m {n} → n > 0 → m < n + m
m<n+m m {n} n>0 rewrite +-comm n m = m<m+n m n>0

m+n≮n : ∀ m n → m + n ≮ n
m+n≮n zero    n                = n≮n n
m+n≮n (suc m) n@(suc _) sm+n<n = m+n≮n m n (m<n⇒m<1+n (s<s⁻¹ sm+n<n))

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
*-distribˡ-+ = comm∧distrʳ⇒distrˡ *-comm *-distribʳ-+

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
    ; *-cong                = cong₂ _*_
    ; *-assoc               = *-assoc
    ; *-identity            = *-identity
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

*-cancelʳ-≡ : ∀ m n o .{{_ : NonZero o}} → m * o ≡ n * o → m ≡ n
*-cancelʳ-≡ zero    zero    (suc o) eq = refl
*-cancelʳ-≡ (suc m) (suc n) (suc o) eq =
  cong suc (*-cancelʳ-≡ m n (suc o) (+-cancelˡ-≡ (suc o) (m * suc o) (n * suc o) eq))

*-cancelˡ-≡ : ∀ m n o .{{_ : NonZero o}} → o * m ≡ o * n → m ≡ n
*-cancelˡ-≡ m n o rewrite *-comm o m | *-comm o n = *-cancelʳ-≡ m n o

m*n≡0⇒m≡0∨n≡0 : ∀ m {n} → m * n ≡ 0 → m ≡ 0 ⊎ n ≡ 0
m*n≡0⇒m≡0∨n≡0 zero    {n}     eq = inj₁ refl
m*n≡0⇒m≡0∨n≡0 (suc m) {zero}  eq = inj₂ refl

m*n≢0 : ∀ m n .{{_ : NonZero m}} .{{_ : NonZero n}} → NonZero (m * n)
m*n≢0 (suc m) (suc n) = _

m*n≢0⇒m≢0 : ∀ m {n} → .{{NonZero (m * n)}} → NonZero m
m*n≢0⇒m≢0 (suc _) = _

m*n≢0⇒n≢0 : ∀ m {n} → .{{NonZero (m * n)}} → NonZero n
m*n≢0⇒n≢0 m {n} rewrite *-comm m n = m*n≢0⇒m≢0 n {m}

m*n≡0⇒m≡0 : ∀ m n .{{_ : NonZero n}} → m * n ≡ 0 → m ≡ 0
m*n≡0⇒m≡0 zero (suc _) eq = refl

m*n≡1⇒m≡1 : ∀ m n → m * n ≡ 1 → m ≡ 1
m*n≡1⇒m≡1 (suc zero)    n          _  = refl
m*n≡1⇒m≡1 (suc (suc m)) (suc zero) ()
m*n≡1⇒m≡1 (suc (suc m)) zero       eq =
  contradiction (trans (sym $ *-zeroʳ m) eq) λ()

m*n≡1⇒n≡1 : ∀ m n → m * n ≡ 1 → n ≡ 1
m*n≡1⇒n≡1 m n eq = m*n≡1⇒m≡1 n m (trans (*-comm n m) eq)

[m*n]*[o*p]≡[m*o]*[n*p] : ∀ m n o p → (m * n) * (o * p) ≡ (m * o) * (n * p)
[m*n]*[o*p]≡[m*o]*[n*p] m n o p = begin-equality
  (m * n) * (o * p) ≡⟨  *-assoc m n (o * p) ⟩
  m * (n * (o * p)) ≡⟨  cong (m *_) (x∙yz≈y∙xz n o p) ⟩
  m * (o * (n * p)) ≡⟨ *-assoc m o (n * p) ⟨
  (m * o) * (n * p) ∎
  where open CommSemigroupProperties *-commutativeSemigroup

m≢0∧n>1⇒m*n>1 : ∀ m n .{{_ : NonZero m}} .{{_ : NonTrivial n}} → NonTrivial (m * n)
m≢0∧n>1⇒m*n>1 (suc m) (2+ n) = _

n≢0∧m>1⇒m*n>1 : ∀ m n .{{_ : NonZero n}} .{{_ : NonTrivial m}} → NonTrivial (m * n)
n≢0∧m>1⇒m*n>1 m n rewrite *-comm m n = m≢0∧n>1⇒m*n>1 n m

------------------------------------------------------------------------
-- Other properties of _*_ and _≤_/_<_

*-cancelʳ-≤ : ∀ m n o .{{_ : NonZero o}} → m * o ≤ n * o → m ≤ n
*-cancelʳ-≤ zero    _       _         _  = z≤n
*-cancelʳ-≤ (suc m) (suc n) o@(suc _) le =
  s≤s (*-cancelʳ-≤ m n o (+-cancelˡ-≤ _ _ _ le))

*-cancelˡ-≤ : ∀ o .{{_ : NonZero o}} → o * m ≤ o * n → m ≤ n
*-cancelˡ-≤ {m} {n} o rewrite *-comm o m | *-comm o n = *-cancelʳ-≤ m n o

*-mono-≤ : _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
*-mono-≤ z≤n       _   = z≤n
*-mono-≤ (s≤s m≤n) u≤v = +-mono-≤ u≤v (*-mono-≤ m≤n u≤v)

*-monoˡ-≤ : ∀ n → (_* n) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤ n m≤o = *-mono-≤ m≤o (≤-refl {n})

*-monoʳ-≤ : ∀ n → (n *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤ n m≤o = *-mono-≤ (≤-refl {n}) m≤o

*-mono-< : _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
*-mono-< z<s               u<v@(s≤s _) = 0<1+n
*-mono-< (s<s m<n@(s≤s _)) u<v@(s≤s _) = +-mono-< u<v (*-mono-< m<n u<v)

*-monoˡ-< : ∀ n .{{_ : NonZero n}} → (_* n) Preserves _<_ ⟶ _<_
*-monoˡ-< n@(suc _) z<s               = 0<1+n
*-monoˡ-< n@(suc _) (s<s m<o@(s≤s _)) = +-mono-≤-< ≤-refl (*-monoˡ-< n m<o)

*-monoʳ-< : ∀ n .{{_ : NonZero n}} → (n *_) Preserves _<_ ⟶ _<_
*-monoʳ-< (suc zero)      m<o@(s≤s _) = +-mono-≤ m<o z≤n
*-monoʳ-< (suc n@(suc _)) m<o@(s≤s _) = +-mono-≤ m<o (<⇒≤ (*-monoʳ-< n m<o))

m≤m*n : ∀ m n .{{_ : NonZero n}} → m ≤ m * n
m≤m*n m n@(suc _) = begin
  m     ≡⟨ sym (*-identityʳ m) ⟩
  m * 1 ≤⟨ *-monoʳ-≤ m 0<1+n ⟩
  m * n ∎

m≤n*m : ∀ m n .{{_ : NonZero n}} → m ≤ n * m
m≤n*m m n@(suc _) = begin
  m     ≤⟨ m≤m*n m n ⟩
  m * n ≡⟨ *-comm m n ⟩
  n * m ∎

m≤n⇒m≤o*n : ∀ o .{{_ : NonZero o}} → m ≤ n → m ≤ o * n
m≤n⇒m≤o*n o m≤n = ≤-trans m≤n (m≤n*m _ o)

m≤n⇒m≤n*o : ∀ o .{{_ : NonZero o}} → m ≤ n → m ≤ n * o
m≤n⇒m≤n*o o m≤n = ≤-trans m≤n (m≤m*n _ o)

m<m*n : ∀ m n .{{_ : NonZero m}} → 1 < n → m < m * n
m<m*n m@(suc m-1) n@(suc (suc n-2)) (s≤s (s≤s _)) = begin-strict
  m           <⟨ s≤s (s≤s (m≤n+m m-1 n-2)) ⟩
  n + m-1     ≤⟨ +-monoʳ-≤ n (m≤m*n m-1 n) ⟩
  n + m-1 * n ≡⟨⟩
  m * n       ∎

m<n⇒m<n*o : ∀ o .{{_ : NonZero o}} → m < n → m < n * o
m<n⇒m<n*o = m≤n⇒m≤n*o

m<n⇒m<o*n : ∀ {m n} o .{{_ : NonZero o}} → m < n → m < o * n
m<n⇒m<o*n = m≤n⇒m≤o*n

*-cancelʳ-< : RightCancellative _<_ _*_
*-cancelʳ-< zero    zero    (suc o) _     = 0<1+n
*-cancelʳ-< (suc m) zero    (suc o) _     = 0<1+n
*-cancelʳ-< m       (suc n) (suc o) nm<om =
  s≤s (*-cancelʳ-< m n o (+-cancelˡ-< m _ _ nm<om))

*-cancelˡ-< : LeftCancellative _<_ _*_
*-cancelˡ-< x y z rewrite *-comm x y | *-comm x z = *-cancelʳ-< x y z

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

m^n≢0 : ∀ m n .{{_ : NonZero m}} → NonZero (m ^ n)
m^n≢0 m n = ≢-nonZero (≢-nonZero⁻¹ m ∘′ m^n≡0⇒m≡0 m n)

m^n>0 : ∀ m .{{_ : NonZero m}} n → m ^ n > 0
m^n>0 m n = >-nonZero⁻¹ (m ^ n) {{m^n≢0 m n}}

^-monoˡ-≤ : ∀ n → (_^ n) Preserves _≤_ ⟶ _≤_
^-monoˡ-≤ zero m≤o = s≤s z≤n
^-monoˡ-≤ (suc n) m≤o = *-mono-≤ m≤o (^-monoˡ-≤ n m≤o)

^-monoʳ-≤ : ∀ m .{{_ : NonZero m}} → (m ^_) Preserves _≤_ ⟶ _≤_
^-monoʳ-≤ m {_} {o} z≤n = n≢0⇒n>0 (≢-nonZero⁻¹ (m ^ o) {{m^n≢0 m o}})
^-monoʳ-≤ m (s≤s n≤o) = *-monoʳ-≤ m (^-monoʳ-≤ m n≤o)

^-monoˡ-< : ∀ n .{{_ : NonZero n}} → (_^ n) Preserves _<_ ⟶ _<_
^-monoˡ-< (suc zero)      m<o = *-monoˡ-< 1 m<o
^-monoˡ-< (suc n@(suc _)) m<o = *-mono-< m<o (^-monoˡ-< n m<o)

^-monoʳ-< : ∀ m → 1 < m → (m ^_) Preserves _<_ ⟶ _<_
^-monoʳ-< m@(suc _) 1<m {zero}  {suc o} z<s       = *-mono-≤ 1<m (m^n>0 m o)
^-monoʳ-< m@(suc _) 1<m {suc n} {suc o} (s<s n<o) = *-monoʳ-< m (^-monoʳ-< m 1<m n<o)

------------------------------------------------------------------------
-- Properties of _⊓_ and _⊔_
------------------------------------------------------------------------
-- Basic specification in terms of _≤_

m≤n⇒m⊔n≡n : m ≤ n → m ⊔ n ≡ n
m≤n⇒m⊔n≡n {zero}  _         = refl
m≤n⇒m⊔n≡n {suc m} (s≤s m≤n) = cong suc (m≤n⇒m⊔n≡n m≤n)

m≥n⇒m⊔n≡m : m ≥ n → m ⊔ n ≡ m
m≥n⇒m⊔n≡m {zero}  {zero}  z≤n       = refl
m≥n⇒m⊔n≡m {suc m} {zero}  z≤n       = refl
m≥n⇒m⊔n≡m {suc m} {suc n} (s≤s m≥n) = cong suc (m≥n⇒m⊔n≡m m≥n)

m≤n⇒m⊓n≡m : m ≤ n → m ⊓ n ≡ m
m≤n⇒m⊓n≡m {zero}  z≤n       = refl
m≤n⇒m⊓n≡m {suc m} (s≤s m≤n) = cong suc (m≤n⇒m⊓n≡m m≤n)

m≥n⇒m⊓n≡n : m ≥ n → m ⊓ n ≡ n
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
-- Equality to their counterparts defined in terms of primitive operations

⊔≡⊔′ : ∀ m n → m ⊔ n ≡ m ⊔′ n
⊔≡⊔′ m n with m <ᵇ n in eq
... | false = m≥n⇒m⊔n≡m (≮⇒≥ (λ m<n → subst T eq (<⇒<ᵇ m<n)))
... | true  = m≤n⇒m⊔n≡n (<⇒≤ (<ᵇ⇒< m n (subst T (sym eq) _)))

⊓≡⊓′ : ∀ m n → m ⊓ n ≡ m ⊓′ n
⊓≡⊓′ m n with m <ᵇ n in eq
... | false = m≥n⇒m⊓n≡n (≮⇒≥ (λ m<n → subst T eq (<⇒<ᵇ m<n)))
... | true  = m≤n⇒m⊓n≡m (<⇒≤ (<ᵇ⇒< m n (subst T (sym eq) _)))

------------------------------------------------------------------------
-- Derived properties of _⊓_ and _⊔_

private
  module ⊓-⊔-properties        = MinMaxOp        ⊓-operator ⊔-operator
  module ⊓-⊔-latticeProperties = LatticeMinMaxOp ⊓-operator ⊔-operator

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
  ; ⊓-isSelectiveMagma        -- : IsSelectiveMagma _⊓_

  ; ⊔-isMagma                 -- : IsMagma _⊔_
  ; ⊔-isSemigroup             -- : IsSemigroup _⊔_
  ; ⊔-isCommutativeSemigroup  -- : IsCommutativeSemigroup _⊔_
  ; ⊔-isBand                  -- : IsBand _⊔_
  ; ⊔-isSelectiveMagma        -- : IsSelectiveMagma _⊔_

  ; ⊓-magma                   -- : Magma _ _
  ; ⊓-semigroup               -- : Semigroup _ _
  ; ⊓-band                    -- : Band _ _
  ; ⊓-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊓-selectiveMagma          -- : SelectiveMagma _ _

  ; ⊔-magma                   -- : Magma _ _
  ; ⊔-semigroup               -- : Semigroup _ _
  ; ⊔-band                    -- : Band _ _
  ; ⊔-commutativeSemigroup    -- : CommutativeSemigroup _ _
  ; ⊔-selectiveMagma          -- : SelectiveMagma _ _

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

open ⊓-⊔-latticeProperties public
  using
  ( ⊓-isSemilattice           -- : IsSemilattice _⊓_
  ; ⊔-isSemilattice           -- : IsSemilattice _⊔_
  ; ⊔-⊓-isLattice             -- : IsLattice _⊔_ _⊓_
  ; ⊓-⊔-isLattice             -- : IsLattice _⊓_ _⊔_
  ; ⊔-⊓-isDistributiveLattice -- : IsDistributiveLattice _⊔_ _⊓_
  ; ⊓-⊔-isDistributiveLattice -- : IsDistributiveLattice _⊓_ _⊔_

  ; ⊓-semilattice             -- : Semilattice _ _
  ; ⊔-semilattice             -- : Semilattice _ _
  ; ⊔-⊓-lattice               -- : Lattice _ _
  ; ⊓-⊔-lattice               -- : Lattice _ _
  ; ⊔-⊓-distributiveLattice   -- : DistributiveLattice _ _
  ; ⊓-⊔-distributiveLattice   -- : DistributiveLattice _ _
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

m<n⇒m<n⊔o : ∀ o → m < n → m < n ⊔ o
m<n⇒m<n⊔o = m≤n⇒m≤n⊔o

m<n⇒m<o⊔n : ∀ o → m < n → m < o ⊔ n
m<n⇒m<o⊔n = m≤n⇒m≤o⊔n

m⊔n<o⇒m<o : ∀ m n {o} → m ⊔ n < o → m < o
m⊔n<o⇒m<o m n m⊔n<o = ≤-<-trans (m≤m⊔n m n) m⊔n<o

m⊔n<o⇒n<o : ∀ m n {o} → m ⊔ n < o → n < o
m⊔n<o⇒n<o m n m⊔n<o = ≤-<-trans (m≤n⊔m m n) m⊔n<o

⊔-mono-< : _⊔_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
⊔-mono-< = ⊔-mono-≤

⊔-pres-<m : n < m → o < m → n ⊔ o < m
⊔-pres-<m {m = m} n<m o<m = subst (_ <_) (⊔-idem m) (⊔-mono-< n<m o<m)

------------------------------------------------------------------------
-- Other properties of _⊔_ and _+_

+-distribˡ-⊔ : _+_ DistributesOverˡ _⊔_
+-distribˡ-⊔ zero    n o = refl
+-distribˡ-⊔ (suc m) n o = cong suc (+-distribˡ-⊔ m n o)

+-distribʳ-⊔ : _+_ DistributesOverʳ _⊔_
+-distribʳ-⊔ = comm∧distrˡ⇒distrʳ +-comm +-distribˡ-⊔

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
  m * suc n                  ≡⟨ ⊔-identityʳ (m * suc n) ⟨
  m * suc n ⊔ zero           ≡⟨ cong (m * suc n ⊔_) (*-zeroʳ m) ⟨
  m * suc n ⊔ m * zero       ∎
*-distribˡ-⊔ m (suc n) (suc o) = begin-equality
  m * (suc n ⊔ suc o)        ≡⟨⟩
  m * suc (n ⊔ o)            ≡⟨ *-suc m (n ⊔ o) ⟩
  m + m * (n ⊔ o)            ≡⟨ cong (m +_) (*-distribˡ-⊔ m n o) ⟩
  m + (m * n ⊔ m * o)        ≡⟨ +-distribˡ-⊔ m (m * n) (m * o) ⟩
  (m + m * n) ⊔ (m + m * o)  ≡⟨ cong₂ _⊔_ (*-suc m n) (*-suc m o) ⟨
  (m * suc n) ⊔ (m * suc o)  ∎

*-distribʳ-⊔ : _*_ DistributesOverʳ _⊔_
*-distribʳ-⊔ = comm∧distrˡ⇒distrʳ *-comm *-distribˡ-⊔

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
  ; *-cong                = cong₂ _⊓_
  ; *-assoc               = ⊓-assoc
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

m<n⇒m⊓o<n : ∀ o → m < n → m ⊓ o < n
m<n⇒m⊓o<n o m<n = ≤-<-trans (m⊓n≤m _ o) m<n

m<n⇒o⊓m<n : ∀ o → m < n → o ⊓ m < n
m<n⇒o⊓m<n o m<n = ≤-<-trans (m⊓n≤n o _) m<n

m<n⊓o⇒m<n : ∀ n o → m < n ⊓ o → m < n
m<n⊓o⇒m<n = m≤n⊓o⇒m≤n

m<n⊓o⇒m<o : ∀ n o → m < n ⊓ o → m < o
m<n⊓o⇒m<o = m≤n⊓o⇒m≤o

⊓-mono-< : _⊓_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
⊓-mono-< = ⊓-mono-≤

⊓-pres-m< : m < n → m < o → m < n ⊓ o
⊓-pres-m< {m} m<n m<o = subst (_< _) (⊓-idem m) (⊓-mono-< m<n m<o)

------------------------------------------------------------------------
-- Other properties of _⊓_ and _+_

+-distribˡ-⊓ : _+_ DistributesOverˡ _⊓_
+-distribˡ-⊓ zero    n o = refl
+-distribˡ-⊓ (suc m) n o = cong suc (+-distribˡ-⊓ m n o)

+-distribʳ-⊓ : _+_ DistributesOverʳ _⊓_
+-distribʳ-⊓ = comm∧distrˡ⇒distrʳ +-comm +-distribˡ-⊓

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
  0 ⊓ (m * o)               ≡⟨ cong (_⊓ (m * o)) (*-zeroʳ m) ⟨
  (m * 0) ⊓ (m * o)         ∎
*-distribˡ-⊓ m (suc n) 0 = begin-equality
  m * (suc n ⊓ 0)           ≡⟨⟩
  m * 0                     ≡⟨ *-zeroʳ m ⟩
  0                         ≡⟨ ⊓-zeroʳ (m * suc n) ⟨
  (m * suc n) ⊓ 0           ≡⟨ cong (m * suc n ⊓_) (*-zeroʳ m) ⟨
  (m * suc n) ⊓ (m * 0)     ∎
*-distribˡ-⊓ m (suc n) (suc o) = begin-equality
  m * (suc n ⊓ suc o)       ≡⟨⟩
  m * suc (n ⊓ o)           ≡⟨ *-suc m (n ⊓ o) ⟩
  m + m * (n ⊓ o)           ≡⟨ cong (m +_) (*-distribˡ-⊓ m n o) ⟩
  m + (m * n) ⊓ (m * o)     ≡⟨ +-distribˡ-⊓ m (m * n) (m * o) ⟩
  (m + m * n) ⊓ (m + m * o) ≡⟨ cong₂ _⊓_ (*-suc m n) (*-suc m o) ⟨
  (m * suc n) ⊓ (m * suc o) ∎

*-distribʳ-⊓ : _*_ DistributesOverʳ _⊓_
*-distribʳ-⊓ = comm∧distrˡ⇒distrʳ *-comm *-distribˡ-⊓

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

∸-monoˡ-≤ : ∀ o → m ≤ n → m ∸ o ≤ n ∸ o
∸-monoˡ-≤ o m≤n = ∸-mono {u = o} m≤n ≤-refl

∸-monoʳ-≤ : ∀ o → m ≤ n → o ∸ m ≥ o ∸ n
∸-monoʳ-≤ _ m≤n = ∸-mono ≤-refl m≤n

∸-monoˡ-< : ∀ {m n o} → m < o → n ≤ m → m ∸ n < o ∸ n
∸-monoˡ-< {m}     {zero}  {o}     m<o       n≤m       = m<o
∸-monoˡ-< {suc m} {suc n} {suc o} (s≤s m<o) (s≤s n≤m) = ∸-monoˡ-< m<o n≤m

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

∸-cancelˡ-≡ :  n ≤ m → o ≤ m → m ∸ n ≡ m ∸ o → n ≡ o
∸-cancelˡ-≡ {_}         z≤n       z≤n       _  = refl
∸-cancelˡ-≡ {o = suc o} z≤n       (s≤s _)   eq = contradiction eq (1+m≢m∸n o)
∸-cancelˡ-≡ {n = suc n} (s≤s _)   z≤n       eq = contradiction (sym eq) (1+m≢m∸n n)
∸-cancelˡ-≡ {_}         (s≤s n≤m) (s≤s o≤m) eq = cong suc (∸-cancelˡ-≡ n≤m o≤m eq)

∸-cancelʳ-≡ :  o ≤ m → o ≤ n → m ∸ o ≡ n ∸ o → m ≡ n
∸-cancelʳ-≡  z≤n       z≤n      eq = eq
∸-cancelʳ-≡ (s≤s o≤m) (s≤s o≤n) eq = cong suc (∸-cancelʳ-≡ o≤m o≤n eq)

m∸n≡0⇒m≤n : m ∸ n ≡ 0 → m ≤ n
m∸n≡0⇒m≤n {zero}  {_}    _   = z≤n
m∸n≡0⇒m≤n {suc m} {suc n} eq = s≤s (m∸n≡0⇒m≤n eq)

m≤n⇒m∸n≡0 : m ≤ n → m ∸ n ≡ 0
m≤n⇒m∸n≡0 {n = n} z≤n      = 0∸n≡0 n
m≤n⇒m∸n≡0 {_}    (s≤s m≤n) = m≤n⇒m∸n≡0 m≤n

m<n⇒0<n∸m : m < n → 0 < n ∸ m
m<n⇒0<n∸m {zero}  {suc n} _         = 0<1+n
m<n⇒0<n∸m {suc m} {suc n} (s≤s m<n) = m<n⇒0<n∸m m<n

m∸n≢0⇒n<m : m ∸ n ≢ 0 → n < m
m∸n≢0⇒n<m {m} {n} m∸n≢0 with n <? m
... | yes n<m = n<m
... | no  n≮m = contradiction (m≤n⇒m∸n≡0 (≮⇒≥ n≮m)) m∸n≢0

m>n⇒m∸n≢0 : m > n → m ∸ n ≢ 0
m>n⇒m∸n≢0 {n = suc n} (s≤s m>n) = m>n⇒m∸n≢0 m>n

m≤n⇒n∸m≤n : m ≤ n → n ∸ m ≤ n
m≤n⇒n∸m≤n z≤n       = ≤-refl
m≤n⇒n∸m≤n (s≤s m≤n) = m≤n⇒m≤1+n (m≤n⇒n∸m≤n m≤n)

------------------------------------------------------------------------
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

m≤n+o⇒m∸n≤o : ∀ m n {o} → m ≤ n + o → m ∸ n ≤ o
m≤n+o⇒m∸n≤o      m  zero    le = le
m≤n+o⇒m∸n≤o zero    (suc n)  _ = z≤n
m≤n+o⇒m∸n≤o (suc m) (suc n) le = m≤n+o⇒m∸n≤o m n (s≤s⁻¹ le)

m<n+o⇒m∸n<o : ∀ m n {o} → .{{NonZero o}} → m < n + o → m ∸ n < o
m<n+o⇒m∸n<o      m  zero                lt = lt
m<n+o⇒m∸n<o zero    (suc n) {o@(suc _)} lt = z<s
m<n+o⇒m∸n<o (suc m) (suc n)             lt = m<n+o⇒m∸n<o m n  (s<s⁻¹ lt)

m+n≤o⇒m≤o∸n : ∀ m {n o} → m + n ≤ o → m ≤ o ∸ n
m+n≤o⇒m≤o∸n zero    le       = z≤n
m+n≤o⇒m≤o∸n (suc m) (s≤s le)
  rewrite +-∸-assoc 1 (m+n≤o⇒n≤o m le) = s≤s (m+n≤o⇒m≤o∸n m le)

m≤o∸n⇒m+n≤o : ∀ m {n o} (n≤o : n ≤ o) → m ≤ o ∸ n → m + n ≤ o
m≤o∸n⇒m+n≤o m         z≤n       le rewrite +-identityʳ m = le
m≤o∸n⇒m+n≤o m {suc n} (s≤s n≤o) le rewrite +-suc m n = s≤s (m≤o∸n⇒m+n≤o m n≤o le)

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

m+[n∸m]≡n : m ≤ n → m + (n ∸ m) ≡ n
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
*-distribˡ-∸ = comm∧distrʳ⇒distrˡ *-comm *-distribʳ-∸

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

pred[n]≤n : pred n ≤ n
pred[n]≤n {zero}  = z≤n
pred[n]≤n {suc n} = n≤1+n n

≤pred⇒≤ : m ≤ pred n → m ≤ n
≤pred⇒≤ {n = zero}  le = le
≤pred⇒≤ {n = suc n} le = m≤n⇒m≤1+n le

≤⇒pred≤ : m ≤ n → pred m ≤ n
≤⇒pred≤ {zero}  le = le
≤⇒pred≤ {suc m} le = ≤-trans (n≤1+n m) le

<⇒≤pred : m < n → m ≤ pred n
<⇒≤pred (s≤s le) = le

suc-pred : ∀ n .{{_ : NonZero n}} → suc (pred n) ≡ n
suc-pred (suc n) = refl

pred-mono-≤ : pred Preserves _≤_ ⟶ _≤_
pred-mono-≤ {zero}          _   = z≤n
pred-mono-≤ {suc _} {suc _} m≤n = s≤s⁻¹ m≤n

pred-mono-< : .{{NonZero m}} → m < n → pred m < pred n
pred-mono-< {m = suc _} {n = suc _} = s<s⁻¹

pred-cancel-≤ : pred m ≤ pred n → (m ≡ 1 × n ≡ 0) ⊎ m ≤ n
pred-cancel-≤ {m = zero}  {n = zero}  _  = inj₂ z≤n
pred-cancel-≤ {m = zero}  {n = suc _} _  = inj₂ z≤n
pred-cancel-≤ {m = suc _} {n = zero} z≤n = inj₁ (refl , refl)
pred-cancel-≤ {m = suc _} {n = suc _} le = inj₂ (s≤s le)

pred-cancel-< : pred m < pred n → m < n
pred-cancel-< {m = zero}  {n = suc _} _ = z<s
pred-cancel-< {m = suc _} {n = suc _}   = s<s

pred-injective : .{{NonZero m}} → .{{NonZero n}} → pred m ≡ pred n → m ≡ n
pred-injective {suc m} {suc n} = cong suc

pred-cancel-≡ : pred m ≡ pred n → ((m ≡ 0 × n ≡ 1) ⊎ (m ≡ 1 × n ≡ 0)) ⊎ m ≡ n
pred-cancel-≡ {m = zero}  {n = zero}  _    = inj₂ refl
pred-cancel-≡ {m = zero}  {n = suc _} refl = inj₁ (inj₁ (refl , refl))
pred-cancel-≡ {m = suc _} {n = zero}  refl = inj₁ (inj₂ (refl , refl))
pred-cancel-≡ {m = suc _} {n = suc _}      = inj₂ ∘ pred-injective

------------------------------------------------------------------------
-- Properties of ∣_-_∣
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Basic

m≡n⇒∣m-n∣≡0 : m ≡ n → ∣ m - n ∣ ≡ 0
m≡n⇒∣m-n∣≡0 {zero}  refl = refl
m≡n⇒∣m-n∣≡0 {suc m} refl = m≡n⇒∣m-n∣≡0 {m} refl

∣m-n∣≡0⇒m≡n :  ∣ m - n ∣ ≡ 0 → m ≡ n
∣m-n∣≡0⇒m≡n {zero}  {zero}  eq = refl
∣m-n∣≡0⇒m≡n {suc m} {suc n} eq = cong suc (∣m-n∣≡0⇒m≡n eq)

m≤n⇒∣n-m∣≡n∸m : m ≤ n → ∣ n - m ∣ ≡ n ∸ m
m≤n⇒∣n-m∣≡n∸m {n = zero}  z≤n       = refl
m≤n⇒∣n-m∣≡n∸m {n = suc n} z≤n       = refl
m≤n⇒∣n-m∣≡n∸m {n = _}     (s≤s m≤n) = m≤n⇒∣n-m∣≡n∸m m≤n

m≤n⇒∣m-n∣≡n∸m : m ≤ n → ∣ m - n ∣ ≡ n ∸ m
m≤n⇒∣m-n∣≡n∸m {n = zero}  z≤n       = refl
m≤n⇒∣m-n∣≡n∸m {n = suc n} z≤n       = refl
m≤n⇒∣m-n∣≡n∸m {n = _}     (s≤s m≤n) = m≤n⇒∣m-n∣≡n∸m m≤n

∣m-n∣≡m∸n⇒n≤m : ∣ m - n ∣ ≡ m ∸ n → n ≤ m
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
∣m-n∣≤m⊔n (suc m) (suc n) = m≤n⇒m≤1+n (∣m-n∣≤m⊔n m n)

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

*-distribˡ-∣-∣ : _*_ DistributesOverˡ ∣_-_∣
*-distribˡ-∣-∣ a = wlog ≤-total (comm⇒sym[distribˡ] {_◦_ = _*_} ∣-∣-comm a)
  $′ λ m n m≤n → begin-equality
    a * ∣ m - n ∣     ≡⟨ cong (a *_) (m≤n⇒∣m-n∣≡n∸m m≤n) ⟩
    a * (n ∸ m)       ≡⟨ *-distribˡ-∸ a n m ⟩
    a * n ∸ a * m     ≡⟨ m≤n⇒∣m-n∣≡n∸m (*-monoʳ-≤ a m≤n) ⟨
    ∣ a * m - a * n ∣ ∎

*-distribʳ-∣-∣ : _*_ DistributesOverʳ ∣_-_∣
*-distribʳ-∣-∣ = comm∧distrˡ⇒distrʳ *-comm *-distribˡ-∣-∣

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

∣-∣≡∣-∣′ : ∀ m n → ∣ m - n ∣ ≡ ∣ m - n ∣′
∣-∣≡∣-∣′ m n with m <ᵇ n in eq
... | false = m≤n⇒∣n-m∣≡n∸m {n} {m} (≮⇒≥ (λ m<n → subst T eq (<⇒<ᵇ m<n)))
... | true  = m≤n⇒∣m-n∣≡n∸m {m} {n} (<⇒≤ (<ᵇ⇒< m n (subst T (sym eq) _)))

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
⌊n/2⌋≤n (suc (suc n)) = s≤s (m≤n⇒m≤1+n (⌊n/2⌋≤n n))

⌊n/2⌋<n : ∀ n → ⌊ suc n /2⌋ < suc n
⌊n/2⌋<n zero    = z<s
⌊n/2⌋<n (suc n) = s<s (s≤s (⌊n/2⌋≤n n))

n≡⌊n+n/2⌋ : ∀ n → n ≡ ⌊ n + n /2⌋
n≡⌊n+n/2⌋ zero          = refl
n≡⌊n+n/2⌋ (suc zero)    = refl
n≡⌊n+n/2⌋ (suc n′@(suc n)) =
  cong suc (trans (n≡⌊n+n/2⌋ _) (cong ⌊_/2⌋ (sym (+-suc n n′))))

⌈n/2⌉≤n : ∀ n → ⌈ n /2⌉ ≤ n
⌈n/2⌉≤n zero    = z≤n
⌈n/2⌉≤n (suc n) = s≤s (⌊n/2⌋≤n n)

⌈n/2⌉<n : ∀ n → ⌈ suc (suc n) /2⌉ < suc (suc n)
⌈n/2⌉<n n = s<s (⌊n/2⌋<n n)

n≡⌈n+n/2⌉ : ∀ n → n ≡ ⌈ n + n /2⌉
n≡⌈n+n/2⌉ zero            = refl
n≡⌈n+n/2⌉ (suc zero)      = refl
n≡⌈n+n/2⌉ (suc n′@(suc n)) =
  cong suc (trans (n≡⌈n+n/2⌉ _) (cong ⌈_/2⌉ (sym (+-suc n n′))))

------------------------------------------------------------------------
-- Properties of !_

1≤n! : ∀ n → 1 ≤ n !
1≤n! zero    = ≤-refl
1≤n! (suc n) = *-mono-≤ (m≤m+n 1 n) (1≤n! n)

infix 4 _!≢0 _!*_!≢0

_!≢0 : ∀ n → NonZero (n !)
n !≢0 = >-nonZero (1≤n! n)

_!*_!≢0 : ∀ m n → NonZero (m ! * n !)
m !* n !≢0 = m*n≢0 _ _ {{m !≢0}} {{n !≢0}}

------------------------------------------------------------------------
-- Properties of _≤′_ and _<′_

≤′-trans : Transitive _≤′_
≤′-trans m≤n ≤′-refl       = m≤n
≤′-trans m≤n (≤′-step n≤o) = ≤′-step (≤′-trans m≤n n≤o)

z≤′n : zero ≤′ n
z≤′n {zero}  = ≤′-refl
z≤′n {suc n} = ≤′-step z≤′n

s≤′s : m ≤′ n → suc m ≤′ suc n
s≤′s (≤′-reflexive m≡n) = ≤′-reflexive (cong suc m≡n)
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

≤′⇒≤ : _≤′_ ⇒ _≤_
≤′⇒≤ (≤′-reflexive m≡n) = ≤-reflexive m≡n
≤′⇒≤ (≤′-step m≤′n) = m≤n⇒m≤1+n (≤′⇒≤ m≤′n)

≤⇒≤′ : _≤_ ⇒ _≤′_
≤⇒≤′ z≤n       = z≤′n
≤⇒≤′ (s≤s m≤n) = s≤′s (≤⇒≤′ m≤n)

≤′-step-injective : {p q : m ≤′ n} → ≤′-step p ≡ ≤′-step q → p ≡ q
≤′-step-injective refl = refl

------------------------------------------------------------------------
-- Properties of _<′_ and _<_
------------------------------------------------------------------------

z<′s : zero <′ suc n
z<′s {zero}  = <′-base
z<′s {suc n} = <′-step (z<′s {n})

s<′s : m <′ n → suc m <′ suc n
s<′s <′-base        = <′-base
s<′s (<′-step m<′n) = <′-step (s<′s m<′n)

<⇒<′ : m < n → m <′ n
<⇒<′ z<s               = z<′s
<⇒<′ (s<s m<n@(s≤s _)) = s<′s (<⇒<′ m<n)

<′⇒< : m <′ n → m < n
<′⇒< <′-base        = n<1+n _
<′⇒< (<′-step m<′n) = m<n⇒m<1+n (<′⇒< m<′n)

m<1+n⇒m<n∨m≡n′ : m < suc n → m < n ⊎ m ≡ n
m<1+n⇒m<n∨m≡n′ m<n with <⇒<′ m<n
... | <′-base      = inj₂ refl
... | <′-step m<′n = inj₁ (<′⇒< m<′n)

------------------------------------------------------------------------
-- Other properties of _≤′_ and _<′_
------------------------------------------------------------------------

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

-- equivalence of  _≤″_ to _≤_

≤⇒≤″ : _≤_ ⇒ _≤″_
≤⇒≤″ = (_ ,_) ∘ m+[n∸m]≡n

<⇒<″ : _<_ ⇒ _<″_
<⇒<″ = ≤⇒≤″

≤″⇒≤ : _≤″_ ⇒ _≤_
≤″⇒≤ (k , refl) = m≤m+n _ k

-- equivalence to the old definition of _≤″_

≤″-proof : (le : m ≤″ n) → let k , _ = le in m + k ≡ n
≤″-proof (_ , prf) = prf

-- yielding analogous proof for _≤_

m≤n⇒∃[o]m+o≡n : .(m ≤ n) → ∃ λ k → m + k ≡ n
m≤n⇒∃[o]m+o≡n m≤n = _ , m+[n∸m]≡n (recompute (_ ≤? _) m≤n)

-- whose witness is equal to monus

guarded-∸≗∸ : ∀ {m n} → .(m≤n : m ≤ n) →
              let k , _ = m≤n⇒∃[o]m+o≡n m≤n in k ≡ n ∸ m
guarded-∸≗∸ m≤n = refl

-- equivalence of _<″_ to _<ᵇ_

m<ᵇn⇒1+m+[n-1+m]≡n : ∀ m n → T (m <ᵇ n) → suc m + (n ∸ suc m) ≡ n
m<ᵇn⇒1+m+[n-1+m]≡n m n lt = m+[n∸m]≡n (<ᵇ⇒< m n lt)

m<ᵇ1+m+n : ∀ m {n} → T (m <ᵇ suc (m + n))
m<ᵇ1+m+n m = <⇒<ᵇ (m≤m+n (suc m) _)

<ᵇ⇒<″ : T (m <ᵇ n) → m <″ n
<ᵇ⇒<″ {m} {n} = <⇒<″ ∘ (<ᵇ⇒< m n)

<″⇒<ᵇ : ∀ {m n} → m <″ n → T (m <ᵇ n)
<″⇒<ᵇ {m} (k , refl) = <⇒<ᵇ (m≤m+n (suc m) k)

-- NB: we use the builtin function `_<ᵇ_ : (m n : ℕ) → Bool` here so
-- that the function quickly decides whether to return `yes` or `no`.
-- It still takes a linear amount of time to generate the proof if it
-- is inspected. We expect the main benefit to be visible for compiled
-- code: the backend erases proofs.

infix 4 _<″?_ _≤″?_ _≥″?_ _>″?_

_<″?_ : Decidable _<″_
m <″? n = map′ <ᵇ⇒<″ <″⇒<ᵇ (T? (m <ᵇ n))

_≤″?_ : Decidable _≤″_
zero  ≤″? n = yes (n , refl)
suc m ≤″? n = m <″? n

_≥″?_ : Decidable _≥″_
_≥″?_ = flip _≤″?_

_>″?_ : Decidable _>″_
_>″?_ = flip _<″?_

≤″-irrelevant : Irrelevant _≤″_
≤″-irrelevant {m} (_ , eq₁) (_ , eq₂)
  with refl ← +-cancelˡ-≡ m _ _ (trans eq₁ (sym eq₂))
  = cong (_ ,_) (≡-irrelevant eq₁ eq₂)

<″-irrelevant : Irrelevant _<″_
<″-irrelevant = ≤″-irrelevant

>″-irrelevant : Irrelevant _>″_
>″-irrelevant = ≤″-irrelevant

≥″-irrelevant : Irrelevant _≥″_
≥″-irrelevant = ≤″-irrelevant

------------------------------------------------------------------------
-- Properties of _≤‴_
------------------------------------------------------------------------

≤‴⇒≤″ : m ≤‴ n → m ≤″ n
≤‴⇒≤″ ≤‴-refl       = _ , +-identityʳ _
≤‴⇒≤″ (≤‴-step m≤n) = _ , trans (+-suc _ _) (≤″-proof (≤‴⇒≤″ m≤n))

m≤‴m+k : m + k ≡ n → m ≤‴ n
m≤‴m+k {k = zero}  = ≤‴-reflexive ∘ trans (sym (+-identityʳ _))
m≤‴m+k {k = suc _} = ≤‴-step ∘ m≤‴m+k ∘ trans (sym (+-suc _ _))

≤″⇒≤‴ : m ≤″ n → m ≤‴ n
≤″⇒≤‴ = m≤‴m+k ∘ ≤″-proof

0≤‴n : 0 ≤‴ n
0≤‴n = m≤‴m+k refl

<ᵇ⇒<‴ : T (m <ᵇ n) → m <‴ n
<ᵇ⇒<‴ = ≤″⇒≤‴ ∘ <ᵇ⇒<″

<‴⇒<ᵇ : m <‴ n → T (m <ᵇ n)
<‴⇒<ᵇ = <″⇒<ᵇ ∘ ≤‴⇒≤″

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

<‴-irrefl : Irreflexive _≡_ _<‴_
<‴-irrefl eq = <-irrefl eq ∘ ≤‴⇒≤

≤‴-irrelevant : Irrelevant _≤‴_
≤‴-irrelevant (≤‴-reflexive eq₁) (≤‴-reflexive eq₂) = cong ≤‴-reflexive (≡-irrelevant eq₁ eq₂)
≤‴-irrelevant (≤‴-reflexive eq₁) (≤‴-step q)        with () ← <‴-irrefl eq₁ q
≤‴-irrelevant (≤‴-step p)        (≤‴-reflexive eq₂) with () ← <‴-irrefl eq₂ p
≤‴-irrelevant (≤‴-step p)        (≤‴-step q)        = cong ≤‴-step (≤‴-irrelevant p q)

<‴-irrelevant : Irrelevant {A = ℕ} _<‴_
<‴-irrelevant = ≤‴-irrelevant

>‴-irrelevant : Irrelevant {A = ℕ} _>‴_
>‴-irrelevant = ≤‴-irrelevant

≥‴-irrelevant : Irrelevant {A = ℕ} _≥‴_
≥‴-irrelevant = ≤‴-irrelevant

------------------------------------------------------------------------
-- Other properties
------------------------------------------------------------------------

-- If there is an injection from a type to ℕ, then the type has
-- decidable equality.

eq? : ∀ {a} {A : Set a} → A ↣ ℕ → DecidableEquality A
eq? inj = via-injection inj _≟_

-- It's possible to decide existential and universal predicates up to
-- a limit.

module _ {p} {P : Pred ℕ p} (P? : U.Decidable P) where

  anyUpTo? : ∀ v → Dec (∃ λ n → n < v × P n)
  anyUpTo? zero    = no λ {(_ , () , _)}
  anyUpTo? (suc v) with P? v | anyUpTo? v
  ... | yes Pv | _                  = yes (v , ≤-refl , Pv)
  ... | _      | yes (n , n<v , Pn) = yes (n , m≤n⇒m≤1+n n<v , Pn)
  ... | no ¬Pv | no ¬Pn<v           = no ¬Pn<1+v
    where
    ¬Pn<1+v : ¬ (∃ λ n → n < suc v × P n)
    ¬Pn<1+v (n , s≤s n≤v , Pn) with n ≟ v
    ... | yes refl = ¬Pv Pn
    ... | no  n≢v  = ¬Pn<v (n , ≤∧≢⇒< n≤v n≢v , Pn)

  allUpTo? : ∀ v → Dec (∀ {n} → n < v → P n)
  allUpTo? zero    = yes λ()
  allUpTo? (suc v) with P? v | allUpTo? v
  ... | no ¬Pv | _        = no λ prf → ¬Pv   (prf ≤-refl)
  ... | _      | no ¬Pn<v = no λ prf → ¬Pn<v (prf ∘ m≤n⇒m≤1+n)
  ... | yes Pn | yes Pn<v = yes Pn<1+v
    where
      Pn<1+v : ∀ {n} → n < suc v → P n
      Pn<1+v {n} (s≤s n≤v) with n ≟ v
      ... | yes refl = Pn
      ... | no  n≢v  = Pn<v (≤∧≢⇒< n≤v n≢v)



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

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

∣m+n-m+o∣≡∣n-o| = ∣m+n-m+o∣≡∣n-o∣
{-# WARNING_ON_USAGE ∣m+n-m+o∣≡∣n-o|
"Warning: ∣m+n-m+o∣≡∣n-o| was deprecated in v1.6.
Please use ∣m+n-m+o∣≡∣n-o∣ instead. Note the final is a \\| rather than a |"
#-}
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

-- Version 2.0

suc[pred[n]]≡n : n ≢ 0 → suc (pred n) ≡ n
suc[pred[n]]≡n {zero}  0≢0 = contradiction refl 0≢0
suc[pred[n]]≡n {suc n} _   = refl
{-# WARNING_ON_USAGE suc[pred[n]]≡n
"Warning: suc[pred[n]]≡n was deprecated in v2.0. Please use suc-pred instead. Note that the proof now uses instance arguments"
#-}

≤-step = m≤n⇒m≤1+n
{-# WARNING_ON_USAGE ≤-step
"Warning: ≤-step was deprecated in v2.0. Please use m≤n⇒m≤1+n instead. "
#-}

≤-stepsˡ = m≤n⇒m≤o+n
{-# WARNING_ON_USAGE ≤-stepsˡ
"Warning: ≤-stepsˡ was deprecated in v2.0. Please use m≤n⇒m≤o+n instead. "
#-}

≤-stepsʳ = m≤n⇒m≤n+o
{-# WARNING_ON_USAGE ≤-stepsʳ
"Warning: ≤-stepsʳ was deprecated in v2.0. Please use m≤n⇒m≤n+o instead. "
#-}

<-step = m<n⇒m<1+n
{-# WARNING_ON_USAGE <-step
"Warning: <-step was deprecated in v2.0. Please use m<n⇒m<1+n instead. "
#-}

pred-mono = pred-mono-≤
{-# WARNING_ON_USAGE pred-mono
"Warning: pred-mono was deprecated in v2.0. Please use pred-mono-≤ instead. "
#-}

{- issue1844/issue1755: raw bundles have moved to `Data.X.Base` -}
open Data.Nat.Base public
  using (*-rawMagma; *-1-rawMonoid)

<-transʳ = ≤-<-trans
{-# WARNING_ON_USAGE <-transʳ
"Warning: <-transʳ was deprecated in v2.0. Please use ≤-<-trans instead. "
#-}

<-transˡ = <-≤-trans
{-# WARNING_ON_USAGE <-transˡ
"Warning: <-transˡ was deprecated in v2.0. Please use <-≤-trans instead. "
#-}
