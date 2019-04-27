------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bool.Properties where

open import Algebra
open import Data.Bool.Base
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Level using (Level; 0ℓ)
open import Relation.Binary as B
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True)
open import Relation.Unary as U using (Irrelevant)

open import Algebra.FunctionProperties {A = Bool} _≡_
open import Algebra.Structures {A = Bool} _≡_
open ≡-Reasoning

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Properties of _≡_

infix 4 _≟_

_≟_ : Decidable {A = Bool} _≡_
true  ≟ true  = yes refl
false ≟ false = yes refl
true  ≟ false = no λ()
false ≟ true  = no λ()

------------------------------------------------------------------------
-- Properties of _≤_

-- Relational properties

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive refl = b≤b

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym b≤b _ = refl

≤-trans : Transitive _≤_
≤-trans f≤t b≤b = f≤t
≤-trans b≤b f≤t = f≤t
≤-trans b≤b b≤b = b≤b

≤-total : Total _≤_
≤-total false false = inj₁ b≤b
≤-total false true  = inj₁ f≤t
≤-total true  false = inj₂ f≤t
≤-total true  true  = inj₁ b≤b

infix 4 _≤?_

_≤?_ : Decidable _≤_
false ≤? false = yes b≤b
false ≤? true  = yes f≤t
true  ≤? false = no λ()
true  ≤? true  = yes b≤b

≤-minimum : Minimum _≤_ false
≤-minimum false = b≤b
≤-minimum true  = f≤t

≤-maximum : Maximum _≤_ true
≤-maximum false = f≤t
≤-maximum true  = b≤b

≤-irrelevant : B.Irrelevant _≤_
≤-irrelevant {_}     f≤t f≤t = refl
≤-irrelevant {false} b≤b b≤b = refl
≤-irrelevant {true}  b≤b b≤b = refl

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

-- Packages

≤-poset : Poset 0ℓ 0ℓ 0ℓ
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

≤-preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder = record
  { isPreorder = ≤-isPreorder
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
-- Properties of _<_

-- Relational properties

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl ()

<-asym : Asymmetric _<_
<-asym f<t ()

<-trans : Transitive _<_
<-trans f<t ()

<-transʳ : Trans _≤_ _<_ _<_
<-transʳ b≤b f<t = f<t

<-transˡ : Trans _<_ _≤_ _<_
<-transˡ f<t b≤b = f<t

<-cmp : Trichotomous _≡_ _<_
<-cmp false false = tri≈ (λ()) refl  (λ())
<-cmp false true  = tri< f<t   (λ()) (λ())
<-cmp true  false = tri> (λ()) (λ()) f<t
<-cmp true  true  = tri≈ (λ()) refl  (λ())

infix 4 _<?_

_<?_ : Decidable _<_
false <? false = no  (λ())
false <? true  = yes f<t
true  <? _     = no  (λ())

<-resp₂-≡ : _<_ Respects₂ _≡_
<-resp₂-≡ = subst (_ <_) , subst (_< _)

<-irrelevant : B.Irrelevant _<_
<-irrelevant f<t f<t = refl

-- Structures

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

-- Packages

<-strictPartialOrder : StrictPartialOrder 0ℓ 0ℓ 0ℓ
<-strictPartialOrder = record
  { isStrictPartialOrder = <-isStrictPartialOrder
  }

<-strictTotalOrder : StrictTotalOrder 0ℓ 0ℓ 0ℓ
<-strictTotalOrder = record
  { isStrictTotalOrder = <-isStrictTotalOrder
  }

------------------------------------------------------------------------
-- Properties of _∨_

∨-assoc : Associative _∨_
∨-assoc true  y z = refl
∨-assoc false y z = refl

∨-comm : Commutative _∨_
∨-comm true  true  = refl
∨-comm true  false = refl
∨-comm false true  = refl
∨-comm false false = refl

∨-identityˡ : LeftIdentity false _∨_
∨-identityˡ _ = refl

∨-identityʳ : RightIdentity false _∨_
∨-identityʳ false = refl
∨-identityʳ true  = refl

∨-identity : Identity false _∨_
∨-identity = ∨-identityˡ , ∨-identityʳ

∨-zeroˡ : LeftZero true _∨_
∨-zeroˡ _ = refl

∨-zeroʳ : RightZero true _∨_
∨-zeroʳ false = refl
∨-zeroʳ true  = refl

∨-zero : Zero true _∨_
∨-zero = ∨-zeroˡ , ∨-zeroʳ

∨-inverseˡ : LeftInverse true not _∨_
∨-inverseˡ false = refl
∨-inverseˡ true  = refl

∨-inverseʳ : RightInverse true not _∨_
∨-inverseʳ x = ∨-comm x (not x) ⟨ trans ⟩ ∨-inverseˡ x

∨-inverse : Inverse true not _∨_
∨-inverse = ∨-inverseˡ , ∨-inverseʳ

∨-idem : Idempotent _∨_
∨-idem false = refl
∨-idem true  = refl

∨-sel : Selective _∨_
∨-sel false y = inj₂ refl
∨-sel true y  = inj₁ refl

∨-isMagma : IsMagma _∨_
∨-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _∨_
  }

∨-magma : Magma 0ℓ 0ℓ
∨-magma = record
  { isMagma = ∨-isMagma
  }

∨-isSemigroup : IsSemigroup _∨_
∨-isSemigroup = record
  { isMagma = ∨-isMagma
  ; assoc   = ∨-assoc
  }

∨-semigroup : Semigroup 0ℓ 0ℓ
∨-semigroup = record
  { isSemigroup = ∨-isSemigroup
  }

∨-isBand : IsBand _∨_
∨-isBand = record
  { isSemigroup = ∨-isSemigroup
  ; idem        = ∨-idem
  }

∨-band : Band 0ℓ 0ℓ
∨-band = record
  { isBand = ∨-isBand
  }

∨-isSemilattice : IsSemilattice _∨_
∨-isSemilattice = record
  { isBand = ∨-isBand
  ; comm   = ∨-comm
  }

∨-semilattice : Semilattice 0ℓ 0ℓ
∨-semilattice = record
  { isSemilattice = ∨-isSemilattice
  }

∨-isCommutativeMonoid : IsCommutativeMonoid _∨_ false
∨-isCommutativeMonoid = record
  { isSemigroup = ∨-isSemigroup
  ; identityˡ   = ∨-identityˡ
  ; comm        = ∨-comm
  }

∨-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
∨-commutativeMonoid = record
  { isCommutativeMonoid = ∨-isCommutativeMonoid
  }

∨-isIdempotentCommutativeMonoid :
  IsIdempotentCommutativeMonoid _∨_ false
∨-isIdempotentCommutativeMonoid = record
    { isCommutativeMonoid = ∨-isCommutativeMonoid
   ; idem = ∨-idem
   }

∨-idempotentCommutativeMonoid : IdempotentCommutativeMonoid 0ℓ 0ℓ
∨-idempotentCommutativeMonoid = record
  { isIdempotentCommutativeMonoid = ∨-isIdempotentCommutativeMonoid
  }

------------------------------------------------------------------------
-- Properties of _∧_

∧-assoc : Associative _∧_
∧-assoc true  y z = refl
∧-assoc false y z = refl

∧-comm : Commutative _∧_
∧-comm true  true  = refl
∧-comm true  false = refl
∧-comm false true  = refl
∧-comm false false = refl

∧-identityˡ : LeftIdentity true _∧_
∧-identityˡ _ = refl

∧-identityʳ : RightIdentity true _∧_
∧-identityʳ false = refl
∧-identityʳ true  = refl

∧-identity : Identity true _∧_
∧-identity = ∧-identityˡ , ∧-identityʳ

∧-zeroˡ : LeftZero false _∧_
∧-zeroˡ _ = refl

∧-zeroʳ : RightZero false _∧_
∧-zeroʳ false = refl
∧-zeroʳ true  = refl

∧-zero : Zero false _∧_
∧-zero = ∧-zeroˡ , ∧-zeroʳ

∧-inverseˡ : LeftInverse false not _∧_
∧-inverseˡ false = refl
∧-inverseˡ true = refl

∧-inverseʳ : RightInverse false not _∧_
∧-inverseʳ x = ∧-comm x (not x) ⟨ trans ⟩ ∧-inverseˡ x

∧-inverse : Inverse false not _∧_
∧-inverse = ∧-inverseˡ , ∧-inverseʳ

∧-idem : Idempotent _∧_
∧-idem false = refl
∧-idem true  = refl

∧-sel : Selective _∧_
∧-sel false y = inj₁ refl
∧-sel true y  = inj₂ refl

∧-distribˡ-∨ : _∧_ DistributesOverˡ _∨_
∧-distribˡ-∨ true  y z = refl
∧-distribˡ-∨ false y z = refl

∧-distribʳ-∨ : _∧_ DistributesOverʳ _∨_
∧-distribʳ-∨ x y z = begin
  (y ∨ z) ∧ x     ≡⟨ ∧-comm (y ∨ z) x ⟩
  x ∧ (y ∨ z)     ≡⟨ ∧-distribˡ-∨ x y z ⟩
  x ∧ y ∨ x ∧ z  ≡⟨ cong₂ _∨_ (∧-comm x y) (∧-comm x z) ⟩
  y ∧ x ∨ z ∧ x  ∎

∧-distrib-∨ : _∧_ DistributesOver _∨_
∧-distrib-∨ = ∧-distribˡ-∨ , ∧-distribʳ-∨

∨-distribˡ-∧ : _∨_ DistributesOverˡ _∧_
∨-distribˡ-∧ true  y z = refl
∨-distribˡ-∧ false y z = refl

∨-distribʳ-∧ : _∨_ DistributesOverʳ _∧_
∨-distribʳ-∧ x y z = begin
  (y ∧ z) ∨ x        ≡⟨ ∨-comm (y ∧ z) x ⟩
  x ∨ (y ∧ z)        ≡⟨ ∨-distribˡ-∧ x y z ⟩
  (x ∨ y) ∧ (x ∨ z)  ≡⟨ cong₂ _∧_ (∨-comm x y) (∨-comm x z) ⟩
  (y ∨ x) ∧ (z ∨ x)  ∎

∨-distrib-∧ : _∨_ DistributesOver _∧_
∨-distrib-∧ = ∨-distribˡ-∧ , ∨-distribʳ-∧

∧-abs-∨ : _∧_ Absorbs _∨_
∧-abs-∨ true  y = refl
∧-abs-∨ false y = refl

∨-abs-∧ : _∨_ Absorbs _∧_
∨-abs-∧ true  y = refl
∨-abs-∧ false y = refl

∨-∧-absorptive : Absorptive _∨_ _∧_
∨-∧-absorptive = ∨-abs-∧ , ∧-abs-∨

∧-isMagma : IsMagma _∧_
∧-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _∧_
  }

∧-magma : Magma 0ℓ 0ℓ
∧-magma = record
  { isMagma = ∧-isMagma
  }

∧-isSemigroup : IsSemigroup _∧_
∧-isSemigroup = record
  { isMagma = ∧-isMagma
  ; assoc   = ∧-assoc
  }

∧-semigroup : Semigroup 0ℓ 0ℓ
∧-semigroup = record
  { isSemigroup = ∧-isSemigroup
  }

∧-isBand : IsBand _∧_
∧-isBand = record
  { isSemigroup = ∧-isSemigroup
  ; idem        = ∧-idem
  }

∧-band : Band 0ℓ 0ℓ
∧-band = record
  { isBand = ∧-isBand
  }

∧-isSemilattice : IsSemilattice _∧_
∧-isSemilattice = record
  { isBand = ∧-isBand
  ; comm   = ∧-comm
  }

∧-semilattice : Semilattice 0ℓ 0ℓ
∧-semilattice = record
  { isSemilattice = ∧-isSemilattice
  }

∧-isCommutativeMonoid : IsCommutativeMonoid _∧_ true
∧-isCommutativeMonoid = record
  { isSemigroup = ∧-isSemigroup
  ; identityˡ   = ∧-identityˡ
  ; comm        = ∧-comm
  }

∧-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
∧-commutativeMonoid = record
  { isCommutativeMonoid = ∧-isCommutativeMonoid
  }

∧-isIdempotentCommutativeMonoid :
  IsIdempotentCommutativeMonoid _∧_ true
∧-isIdempotentCommutativeMonoid = record
  { isCommutativeMonoid = ∧-isCommutativeMonoid
  ; idem = ∧-idem
  }

∧-idempotentCommutativeMonoid : IdempotentCommutativeMonoid 0ℓ 0ℓ
∧-idempotentCommutativeMonoid = record
  { isIdempotentCommutativeMonoid = ∧-isIdempotentCommutativeMonoid
  }

∨-∧-isCommutativeSemiring
  : IsCommutativeSemiring _∨_ _∧_ false true
∨-∧-isCommutativeSemiring = record
  { +-isCommutativeMonoid = ∨-isCommutativeMonoid
  ; *-isCommutativeMonoid = ∧-isCommutativeMonoid
  ; distribʳ = ∧-distribʳ-∨
  ; zeroˡ    = ∧-zeroˡ
  }

∨-∧-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
∨-∧-commutativeSemiring = record
  { _+_                   = _∨_
  ; _*_                   = _∧_
  ; 0#                    = false
  ; 1#                    = true
  ; isCommutativeSemiring = ∨-∧-isCommutativeSemiring
  }

∧-∨-isCommutativeSemiring
  : IsCommutativeSemiring _∧_ _∨_ true false
∧-∨-isCommutativeSemiring = record
  { +-isCommutativeMonoid = ∧-isCommutativeMonoid
  ; *-isCommutativeMonoid = ∨-isCommutativeMonoid
  ; distribʳ = ∨-distribʳ-∧
  ; zeroˡ    = ∨-zeroˡ
  }

∧-∨-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
∧-∨-commutativeSemiring = record
  { _+_                   = _∧_
  ; _*_                   = _∨_
  ; 0#                    = true
  ; 1#                    = false
  ; isCommutativeSemiring = ∧-∨-isCommutativeSemiring
  }

∨-∧-isLattice : IsLattice _∨_ _∧_
∨-∧-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = ∨-comm
  ; ∨-assoc       = ∨-assoc
  ; ∨-cong        = cong₂ _∨_
  ; ∧-comm        = ∧-comm
  ; ∧-assoc       = ∧-assoc
  ; ∧-cong        = cong₂ _∧_
  ; absorptive    = ∨-∧-absorptive
  }

∨-∧-lattice : Lattice 0ℓ 0ℓ
∨-∧-lattice = record
  { isLattice = ∨-∧-isLattice
  }

∨-∧-isDistributiveLattice : IsDistributiveLattice _∨_ _∧_
∨-∧-isDistributiveLattice = record
  { isLattice     = ∨-∧-isLattice
  ; ∨-∧-distribʳ = ∨-distribʳ-∧
  }

∨-∧-distributiveLattice : DistributiveLattice 0ℓ 0ℓ
∨-∧-distributiveLattice = record
  { isDistributiveLattice = ∨-∧-isDistributiveLattice
  }

∨-∧-isBooleanAlgebra : IsBooleanAlgebra _∨_ _∧_ not true false
∨-∧-isBooleanAlgebra = record
  { isDistributiveLattice = ∨-∧-isDistributiveLattice
  ; ∨-complementʳ = ∨-inverseʳ
  ; ∧-complementʳ = ∧-inverseʳ
  ; ¬-cong        = cong not
  }

∨-∧-booleanAlgebra : BooleanAlgebra 0ℓ 0ℓ
∨-∧-booleanAlgebra = record
  { isBooleanAlgebra = ∨-∧-isBooleanAlgebra
  }

------------------------------------------------------------------------
-- Properties of _xor_

xor-is-ok : ∀ x y → x xor y ≡ (x ∨ y) ∧ not (x ∧ y)
xor-is-ok true  y = refl
xor-is-ok false y = sym (∧-identityʳ _)

xor-∧-commutativeRing : CommutativeRing 0ℓ 0ℓ
xor-∧-commutativeRing = commutativeRing
  where
  import Algebra.Properties.BooleanAlgebra as BA
  open BA ∨-∧-booleanAlgebra
  open XorRing _xor_ xor-is-ok

------------------------------------------------------------------------
-- Miscellaneous other properties

not-involutive : Involutive not
not-involutive true  = refl
not-involutive false = refl

not-¬ : ∀ {x y} → x ≡ y → x ≢ not y
not-¬ {true}  refl ()
not-¬ {false} refl ()

¬-not : ∀ {x y} → x ≢ y → x ≡ not y
¬-not {true}  {true}  x≢y = ⊥-elim (x≢y refl)
¬-not {true}  {false} _   = refl
¬-not {false} {true}  _   = refl
¬-not {false} {false} x≢y = ⊥-elim (x≢y refl)

⇔→≡ : {x y z : Bool} → x ≡ z ⇔ y ≡ z → x ≡ y
⇔→≡ {true } {true }         hyp = refl
⇔→≡ {true } {false} {true } hyp = sym (Equivalence.to hyp ⟨$⟩ refl)
⇔→≡ {true } {false} {false} hyp = Equivalence.from hyp ⟨$⟩ refl
⇔→≡ {false} {true } {true } hyp = Equivalence.from hyp ⟨$⟩ refl
⇔→≡ {false} {true } {false} hyp = sym (Equivalence.to hyp ⟨$⟩ refl)
⇔→≡ {false} {false}         hyp = refl

T-≡ : ∀ {x} → T x ⇔ x ≡ true
T-≡ {false} = equivalence (λ ())       (λ ())
T-≡ {true}  = equivalence (const refl) (const _)

T-not-≡ : ∀ {x} → T (not x) ⇔ x ≡ false
T-not-≡ {false} = equivalence (const refl) (const _)
T-not-≡ {true}  = equivalence (λ ())       (λ ())

T-∧ : ∀ {x y} → T (x ∧ y) ⇔ (T x × T y)
T-∧ {true}  {true}  = equivalence (const (_ , _)) (const _)
T-∧ {true}  {false} = equivalence (λ ())          proj₂
T-∧ {false} {_}     = equivalence (λ ())          proj₁

T-∨ : ∀ {x y} → T (x ∨ y) ⇔ (T x ⊎ T y)
T-∨ {true}  {_}     = equivalence inj₁ (const _)
T-∨ {false} {true}  = equivalence inj₂ (const _)
T-∨ {false} {false} = equivalence inj₁ [ id , id ]

T-irrelevant : U.Irrelevant T
T-irrelevant {true}  _  _  = refl

T? : U.Decidable T
T? true  = yes _
T? false = no (λ ())

T?-diag : ∀ b → T b → True (T? b)
T?-diag true  _ = _

push-function-into-if : ∀ (f : A → B) x {y z} →
                        f (if x then y else z) ≡ (if x then f y else f z)
push-function-into-if _ true  = refl
push-function-into-if _ false = refl

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

∧-∨-distˡ   = ∧-distribˡ-∨
{-# WARNING_ON_USAGE ∧-∨-distˡ
"Warning: ∧-∨-distˡ was deprecated in v0.15.
Please use ∧-distribˡ-∨ instead."
#-}
∧-∨-distʳ   = ∧-distribʳ-∨
{-# WARNING_ON_USAGE ∧-∨-distʳ
"Warning: ∧-∨-distʳ was deprecated in v0.15.
Please use ∧-distribʳ-∨ instead."
#-}
distrib-∧-∨ = ∧-distrib-∨
{-# WARNING_ON_USAGE distrib-∧-∨
"Warning: distrib-∧-∨ was deprecated in v0.15.
Please use ∧-distrib-∨ instead."
#-}
∨-∧-distˡ   = ∨-distribˡ-∧
{-# WARNING_ON_USAGE ∨-∧-distˡ
"Warning: ∨-∧-distˡ was deprecated in v0.15.
Please use ∨-distribˡ-∧ instead."
#-}
∨-∧-distʳ   = ∨-distribʳ-∧
{-# WARNING_ON_USAGE ∨-∧-distʳ
"Warning: ∨-∧-distʳ was deprecated in v0.15.
Please use ∨-distribʳ-∧ instead."
#-}
∨-∧-distrib = ∨-distrib-∧
{-# WARNING_ON_USAGE ∨-∧-distrib
"Warning: ∨-∧-distrib was deprecated in v0.15.
Please use ∨-distrib-∧ instead."
#-}
∨-∧-abs    = ∨-abs-∧
{-# WARNING_ON_USAGE ∨-∧-abs
"Warning: ∨-∧-abs was deprecated in v0.15.
Please use ∨-abs-∧ instead."
#-}
∧-∨-abs    = ∧-abs-∨
{-# WARNING_ON_USAGE ∧-∨-abs
"Warning: ∧-∨-abs was deprecated in v0.15.
Please use ∧-abs-∨ instead."
#-}
not-∧-inverseˡ = ∧-inverseˡ
{-# WARNING_ON_USAGE not-∧-inverseˡ
"Warning: not-∧-inverseˡ was deprecated in v0.15.
Please use ∧-inverseˡ instead."
#-}
not-∧-inverseʳ = ∧-inverseʳ
{-# WARNING_ON_USAGE not-∧-inverseʳ
"Warning: not-∧-inverseʳ was deprecated in v0.15.
Please use ∧-inverseʳ instead."
#-}
not-∧-inverse = ∧-inverse
{-# WARNING_ON_USAGE not-∧-inverse
"Warning: not-∧-inverse was deprecated in v0.15.
Please use ∧-inverse instead."
#-}
not-∨-inverseˡ = ∨-inverseˡ
{-# WARNING_ON_USAGE not-∨-inverseˡ
"Warning: not-∨-inverseˡ was deprecated in v0.15.
Please use ∨-inverseˡ instead."
#-}
not-∨-inverseʳ = ∨-inverseʳ
{-# WARNING_ON_USAGE not-∨-inverseʳ
"Warning: not-∨-inverseʳ was deprecated in v0.15.
Please use ∨-inverseʳ instead."
#-}
not-∨-inverse = ∨-inverse
{-# WARNING_ON_USAGE not-∨-inverse
"Warning: not-∨-inverse was deprecated in v0.15.
Please use ∨-inverse instead."
#-}
isCommutativeSemiring-∨-∧ = ∨-∧-isCommutativeSemiring
{-# WARNING_ON_USAGE isCommutativeSemiring-∨-∧
"Warning: isCommutativeSemiring-∨-∧ was deprecated in v0.15.
Please use ∨-∧-isCommutativeSemiring instead."
#-}
commutativeSemiring-∨-∧   =  ∨-∧-commutativeSemiring
{-# WARNING_ON_USAGE commutativeSemiring-∨-∧
"Warning: commutativeSemiring-∨-∧ was deprecated in v0.15.
Please use ∨-∧-commutativeSemiring instead."
#-}
isCommutativeSemiring-∧-∨ = ∧-∨-isCommutativeSemiring
{-# WARNING_ON_USAGE isCommutativeSemiring-∧-∨
"Warning: isCommutativeSemiring-∧-∨ was deprecated in v0.15.
Please use ∧-∨-isCommutativeSemiring instead."
#-}
commutativeSemiring-∧-∨   = ∧-∨-commutativeSemiring
{-# WARNING_ON_USAGE commutativeSemiring-∧-∨
"Warning: commutativeSemiring-∧-∨ was deprecated in v0.15.
Please use ∧-∨-commutativeSemiring instead."
#-}
isBooleanAlgebra          = ∨-∧-isBooleanAlgebra
{-# WARNING_ON_USAGE isBooleanAlgebra
"Warning: isBooleanAlgebra was deprecated in v0.15.
Please use ∨-∧-isBooleanAlgebra instead."
#-}
booleanAlgebra            = ∨-∧-booleanAlgebra
{-# WARNING_ON_USAGE booleanAlgebra
"Warning: booleanAlgebra was deprecated in v0.15.
Please use ∨-∧-booleanAlgebra instead."
#-}
commutativeRing-xor-∧     = xor-∧-commutativeRing
{-# WARNING_ON_USAGE commutativeRing-xor-∧
"Warning: commutativeRing-xor-∧ was deprecated in v0.15.
Please use xor-∧-commutativeRing instead."
#-}
proof-irrelevance = T-irrelevant
{-# WARNING_ON_USAGE proof-irrelevance
"Warning: proof-irrelevance was deprecated in v0.15.
Please use T-irrelevant instead."
#-}

-- Version 1.0

T-irrelevance = T-irrelevant
{-# WARNING_ON_USAGE T-irrelevance
"Warning: T-irrelevance was deprecated in v1.0.
Please use T-irrelevant instead."
#-}
