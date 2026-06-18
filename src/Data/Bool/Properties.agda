------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bool.Properties where
open import Algebra.Bundles
  using (Magma; Semigroup; Band; Monoid; CommutativeMonoid
        ; IdempotentCommutativeMonoid; CommutativeSemiring; CommutativeRing)
open import Algebra.Lattice.Bundles
  using (Lattice; DistributiveLattice; BooleanAlgebra; Semilattice)
import Algebra.Lattice.Properties.BooleanAlgebra as BooleanAlgebraProperties
open import Data.Bool.Base
  using (Bool; true; false; not; _∧_; _∨_; _xor_ ; if_then_else_; T; _≤_; _<_
        ; b≤b; f≤t; f<t)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Function.Base using (_⟨_⟩_; const; id)
open import Function.Bundles hiding (Inverse; LeftInverse; RightInverse)
open import Induction.WellFounded using (Acc; WellFounded; acc)
open import Level using (0ℓ; Level)
open import Relation.Binary.Bundles using (DecSetoid; DecTotalOrder; Poset;
  Preorder; Setoid; StrictPartialOrder; StrictTotalOrder; TotalOrder)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder; IsTotalOrder; IsDecTotalOrder
        ; IsStrictPartialOrder; IsStrictTotalOrder)
open import Relation.Binary.Bundles
  using (Setoid; DecSetoid; Poset; Preorder; TotalOrder; DecTotalOrder
        ; StrictPartialOrder; StrictTotalOrder)
open import Relation.Binary.Definitions
  using (Decidable; DecidableEquality ; Reflexive; Transitive; Antisymmetric
        ; Minimum; Maximum; Total; Irrelevant ; Irreflexive; Asymmetric; Trans
        ; Trichotomous; tri≈; tri<; tri>; _Respects₂_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong; cong₂; subst; trans; _≢_; ¬[x≢x])
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning; setoid; decSetoid; isEquivalence)
open import Relation.Nullary.Decidable.Core
  using (True; yes; no; fromWitness ; toWitness)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
import Relation.Unary as U

open import Algebra.Definitions {A = Bool} _≡_
open import Algebra.Structures {A = Bool} _≡_
open import Algebra.Lattice.Structures {A = Bool} _≡_

open ≡-Reasoning

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Properties of _≡_

infix 4 _≡?_

_≡?_ : DecidableEquality Bool
true  ≡? true  = yes refl
false ≡? false = yes refl
true  ≡? false = no λ()
false ≡? true  = no λ()

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid Bool

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≡?_

------------------------------------------------------------------------
-- Properties of _≤_

-- Relational properties

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive refl = b≤b

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-trans : Transitive _≤_
≤-trans b≤b p   = p
≤-trans f≤t b≤b = f≤t

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym b≤b _ = refl

≤-minimum : Minimum _≤_ false
≤-minimum false = b≤b
≤-minimum true  = f≤t

≤-maximum : Maximum _≤_ true
≤-maximum false = f≤t
≤-maximum true  = b≤b

≤-total : Total _≤_
≤-total false b = inj₁ (≤-minimum b)
≤-total true  b = inj₂ (≤-maximum b)

infix 4 _≤?_

_≤?_ : Decidable _≤_
false ≤? b     = yes (≤-minimum b)
true  ≤? false = no λ ()
true  ≤? true  = yes b≤b

≤-irrelevant : Irrelevant _≤_
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
  ; _≈?_         = _≡?_
  ; _≤?_         = _≤?_
  }

-- Bundles

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
<-resp₂-≡ = subst (_< _) , subst (_ <_)

<-irrelevant : Irrelevant _<_
<-irrelevant f<t f<t = refl

<-wellFounded : WellFounded _<_
<-wellFounded _ = acc <-acc
  where
    <-acc : ∀ {x y} → y < x → Acc _<_ y
    <-acc f<t = acc λ ()

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
  { isStrictPartialOrder = <-isStrictPartialOrder
  ; compare              = <-cmp
  }

-- Bundles

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

∨-conicalˡ : LeftConical false _∨_
∨-conicalˡ false false _ = refl

∨-conicalʳ : RightConical false _∨_
∨-conicalʳ false false _ = refl

∨-conical : Conical false _∨_
∨-conical = ∨-conicalˡ , ∨-conicalʳ

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

∨-isMonoid : IsMonoid _∨_ false
∨-isMonoid = record
  { isSemigroup = ∨-isSemigroup
  ; identity = ∨-identity
  }

∨-monoid : Monoid 0ℓ 0ℓ
∨-monoid = record
  { isMonoid = ∨-isMonoid
  }

∨-isCommutativeMonoid : IsCommutativeMonoid _∨_ false
∨-isCommutativeMonoid = record
  { isMonoid = ∨-isMonoid
  ; comm = ∨-comm
  }

∨-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
∨-commutativeMonoid = record
  { isCommutativeMonoid = ∨-isCommutativeMonoid
  }

∨-isIdempotentCommutativeMonoid :
  IsIdempotentCommutativeMonoid _∨_ false
∨-isIdempotentCommutativeMonoid = record
  { isCommutativeMonoid = ∨-isCommutativeMonoid
  ; idem                = ∨-idem
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

∧-conicalˡ : LeftConical true _∧_
∧-conicalˡ true true _ = refl

∧-conicalʳ : RightConical true _∧_
∧-conicalʳ true true _ = refl

∧-conical : Conical true _∧_
∧-conical = ∧-conicalˡ , ∧-conicalʳ

∧-distribˡ-∨ : _∧_ DistributesOverˡ _∨_
∧-distribˡ-∨ true  y z = refl
∧-distribˡ-∨ false y z = refl

∧-distribʳ-∨ : _∧_ DistributesOverʳ _∨_
∧-distribʳ-∨ x y z = begin
  (y ∨ z) ∧ x     ≡⟨ ∧-comm (y ∨ z) x ⟩
  x ∧ (y ∨ z)     ≡⟨ ∧-distribˡ-∨ x y z ⟩
  x ∧ y ∨ x ∧ z   ≡⟨ cong₂ _∨_ (∧-comm x y) (∧-comm x z) ⟩
  y ∧ x ∨ z ∧ x   ∎

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

∧-isMonoid : IsMonoid _∧_ true
∧-isMonoid = record
  { isSemigroup = ∧-isSemigroup
  ; identity = ∧-identity
  }

∧-monoid : Monoid 0ℓ 0ℓ
∧-monoid = record
  { isMonoid = ∧-isMonoid
  }

∧-isCommutativeMonoid : IsCommutativeMonoid _∧_ true
∧-isCommutativeMonoid = record
  { isMonoid = ∧-isMonoid
  ; comm = ∧-comm
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

∨-∧-isSemiring : IsSemiring _∨_ _∧_ false true
∨-∧-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = ∨-isCommutativeMonoid
    ; *-cong = cong₂ _∧_
    ; *-assoc = ∧-assoc
    ; *-identity = ∧-identity
    ; distrib = ∧-distrib-∨
    }
  ; zero = ∧-zero
  }

∨-∧-isCommutativeSemiring
  : IsCommutativeSemiring _∨_ _∧_ false true
∨-∧-isCommutativeSemiring = record
  { isSemiring = ∨-∧-isSemiring
  ; *-comm = ∧-comm
  }

∨-∧-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
∨-∧-commutativeSemiring = record
  { _+_                   = _∨_
  ; _*_                   = _∧_
  ; 0#                    = false
  ; 1#                    = true
  ; isCommutativeSemiring = ∨-∧-isCommutativeSemiring
  }

∧-∨-isSemiring : IsSemiring _∧_ _∨_ true false
∧-∨-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = ∧-isCommutativeMonoid
    ; *-cong = cong₂ _∨_
    ; *-assoc = ∨-assoc
    ; *-identity = ∨-identity
    ; distrib = ∨-distrib-∧
    }
  ; zero = ∨-zero
  }

∧-∨-isCommutativeSemiring
  : IsCommutativeSemiring _∧_ _∨_ true false
∧-∨-isCommutativeSemiring = record
  { isSemiring = ∧-∨-isSemiring
  ; *-comm = ∨-comm
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
  { isLattice   = ∨-∧-isLattice
  ; ∨-distrib-∧ = ∨-distrib-∧
  ; ∧-distrib-∨ = ∧-distrib-∨
  }

∨-∧-distributiveLattice : DistributiveLattice 0ℓ 0ℓ
∨-∧-distributiveLattice = record
  { isDistributiveLattice = ∨-∧-isDistributiveLattice
  }

∨-∧-isBooleanAlgebra : IsBooleanAlgebra _∨_ _∧_ not true false
∨-∧-isBooleanAlgebra = record
  { isDistributiveLattice = ∨-∧-isDistributiveLattice
  ; ∨-complement          = ∨-inverse
  ; ∧-complement          = ∧-inverse
  ; ¬-cong                = cong not
  }

∨-∧-booleanAlgebra : BooleanAlgebra 0ℓ 0ℓ
∨-∧-booleanAlgebra = record
  { isBooleanAlgebra = ∨-∧-isBooleanAlgebra
  }

------------------------------------------------------------------------
-- Properties of not

not-involutive : Involutive not
not-involutive true  = refl
not-involutive false = refl

not-injective : ∀ {x y} → not x ≡ not y → x ≡ y
not-injective {false} {false} nx≢ny = refl
not-injective {true}  {true}  nx≢ny = refl

not-¬ : ∀ {x y} → x ≡ y → x ≢ not y
not-¬ {true}  refl ()
not-¬ {false} refl ()

¬-not : ∀ {x y} → x ≢ y → x ≡ not y
¬-not {true}  {true}  x≢y = ¬[x≢x] x≢y
¬-not {true}  {false} _   = refl
¬-not {false} {true}  _   = refl
¬-not {false} {false} x≢y = ¬[x≢x] x≢y

------------------------------------------------------------------------
-- Properties of _xor_

xor-is-ok : ∀ x y → x xor y ≡ (x ∨ y) ∧ not (x ∧ y)
xor-is-ok true  y = refl
xor-is-ok false y = sym (∧-identityʳ _)

true-xor : ∀ x → true xor x ≡ not x
true-xor false = refl
true-xor true  = refl

xor-same : ∀ x → x xor x ≡ false
xor-same false = refl
xor-same true  = refl

not-distribˡ-xor : ∀ x y → not (x xor y) ≡ (not x) xor y
not-distribˡ-xor false y = refl
not-distribˡ-xor true  y = not-involutive _

not-distribʳ-xor : ∀ x y → not (x xor y) ≡ x xor (not y)
not-distribʳ-xor false y = refl
not-distribʳ-xor true  y = refl

xor-assoc : Associative _xor_
xor-assoc true  y z = sym (not-distribˡ-xor y z)
xor-assoc false y z = refl

xor-comm : Commutative _xor_
xor-comm false false = refl
xor-comm false true  = refl
xor-comm true  false = refl
xor-comm true  true  = refl

xor-identityˡ : LeftIdentity false _xor_
xor-identityˡ _ = refl

xor-identityʳ : RightIdentity false _xor_
xor-identityʳ false = refl
xor-identityʳ true  = refl

xor-identity : Identity false _xor_
xor-identity = xor-identityˡ , xor-identityʳ

xor-inverseˡ : LeftInverse true not _xor_
xor-inverseˡ false = refl
xor-inverseˡ true = refl

xor-inverseʳ : RightInverse true not _xor_
xor-inverseʳ x = xor-comm x (not x) ⟨ trans ⟩ xor-inverseˡ x

xor-inverse : Inverse true not _xor_
xor-inverse = xor-inverseˡ , xor-inverseʳ

∧-distribˡ-xor : _∧_ DistributesOverˡ _xor_
∧-distribˡ-xor false y z = refl
∧-distribˡ-xor true  y z = refl

∧-distribʳ-xor : _∧_ DistributesOverʳ _xor_
∧-distribʳ-xor x false z    = refl
∧-distribʳ-xor x true false = sym (xor-identityʳ x)
∧-distribʳ-xor x true true  = sym (xor-same x)

∧-distrib-xor : _∧_ DistributesOver _xor_
∧-distrib-xor = ∧-distribˡ-xor , ∧-distribʳ-xor

xor-annihilates-not : ∀ x y → (not x) xor (not y) ≡ x xor y
xor-annihilates-not false y = not-involutive _
xor-annihilates-not true  y = refl

xor-∧-commutativeRing : CommutativeRing 0ℓ 0ℓ
xor-∧-commutativeRing = ⊕-∧-commutativeRing
  where
  open BooleanAlgebraProperties ∨-∧-booleanAlgebra
  open XorRing _xor_ xor-is-ok

------------------------------------------------------------------------
-- Properties of if_then_else_

if-float : ∀ (f : A → B) b {x y} →
           f (if b then x else y) ≡ (if b then f x else f y)
if-float _ true  = refl
if-float _ false = refl

if-eta : ∀ b {x : A} →
         (if b then x else x) ≡ x
if-eta false = refl
if-eta true  = refl

if-idem-then : ∀ b {x y : A} →
               (if b then (if b then x else y) else y)
             ≡ (if b then x                    else y)
if-idem-then false = refl
if-idem-then true  = refl

if-idem-else : ∀ b {x y : A} →
               (if b then x else (if b then x else y))
             ≡ (if b then x else y)
if-idem-else false = refl
if-idem-else true  = refl

if-swap-then : ∀ b c {x y : A} →
          (if b then (if c then x else y) else y)
        ≡ (if c then (if b then x else y) else y)
if-swap-then false false = refl
if-swap-then false true  = refl
if-swap-then true  _     = refl

if-swap-else : ∀ b c {x y : A} →
          (if b then x else (if c then x else y))
        ≡ (if c then x else (if b then x else y))
if-swap-else false _     = refl
if-swap-else true  false = refl
if-swap-else true  true  = refl

if-not : ∀ b {x y : A} →
         (if not b then x else y) ≡ (if b then y else x)
if-not false = refl
if-not true  = refl

if-∧ : ∀ b {c} {x y : A} →
       (if b ∧ c then x else y) ≡ (if b then (if c then x else y) else y)
if-∧ false = refl
if-∧ true  = refl

if-∨ : ∀ b {c} {x y : A} →
       (if b ∨ c then x else y) ≡ (if b then x else (if c then x else y))
if-∨ false = refl
if-∨ true  = refl

if-xor : ∀ b {c} {x y : A} →
         (if b xor c then x else y)
       ≡ (if b then (if c then y else x) else (if c then x else y))
if-xor false = refl
if-xor true {false} = refl
if-xor true {true } = refl

-- The following congruence lemmas are short hands for
--   cong (if_then x else y)
--   cong (if b then_else y)
--   cong (if b then x else_)
--   cong (if b then_else_)
-- on the different sub-terms in an if_then_else_ expression.
-- With these short hands, the branches x and y can be inferred
-- automatically (i.e., they are implicit arguments) whereas
-- the branches have to be spelled out explicitly when using cong.
-- (Using underscores as in "cong (if b then _ else_)"
-- unfortunately fails to resolve the omitted argument.)

if-cong : ∀ {b c} {x y : A} → b ≡ c →
          (if b then x else y)
        ≡ (if c then x else y)
if-cong refl = refl

if-cong-then : ∀ b {x y z : A} → x ≡ z →
               (if b then x else y)
             ≡ (if b then z else y)
if-cong-then _ refl = refl

if-cong-else : ∀ b {x y z : A} → y ≡ z →
               (if b then x else y)
             ≡ (if b then x else z)
if-cong-else _ refl = refl

if-cong₂ : ∀ b {x y z w : A} → x ≡ z → y ≡ w →
           (if b then x else y)
         ≡ (if b then z else w)
if-cong₂ _ refl refl = refl

------------------------------------------------------------------------
-- Properties of T

open Relation.Nullary.Decidable.Core public using (T?)

¬T-≡ : ∀ {x} → (¬ T x) ⇔ x ≡ false
¬T-≡ {false} = mk⇔ (const refl) (const id)
¬T-≡ {true}  = mk⇔ (contradiction _) (λ ())

T-≡ : ∀ {x} → T x ⇔ x ≡ true
T-≡ {false} = mk⇔ (λ ())       (λ ())
T-≡ {true}  = mk⇔ (const refl) (const _)

T-not-≡ : ∀ {x} → T (not x) ⇔ x ≡ false
T-not-≡ {false} = mk⇔ (const refl) (const _)
T-not-≡ {true}  = mk⇔ (λ ())       (λ ())

T-∧ : ∀ {x y} → T (x ∧ y) ⇔ (T x × T y)
T-∧ {true}  {true}  = mk⇔ (const (_ , _)) (const _)
T-∧ {true}  {false} = mk⇔ (λ ())          proj₂
T-∧ {false} {_}     = mk⇔ (λ ())          proj₁

T-∨ : ∀ {x y} → T (x ∨ y) ⇔ (T x ⊎ T y)
T-∨ {true}  {_}     = mk⇔ inj₁ (const _)
T-∨ {false} {true}  = mk⇔ inj₂ (const _)
T-∨ {false} {false} = mk⇔ inj₁ [ id , id ]

T-irrelevant : U.Irrelevant T
T-irrelevant {true}  _  _  = refl

T?-diag : ∀ b → T b → True (T? b)
T?-diag b = fromWitness

------------------------------------------------------------------------
-- Miscellaneous other properties

⇔→≡ : {x y z : Bool} → x ≡ z ⇔ y ≡ z → x ≡ y
⇔→≡ {true } {true }         hyp = refl
⇔→≡ {true } {false} {true } hyp = sym (Equivalence.to hyp refl)
⇔→≡ {true } {false} {false} hyp = Equivalence.from hyp refl
⇔→≡ {false} {true } {true } hyp = Equivalence.from hyp refl
⇔→≡ {false} {true } {false} hyp = sym (Equivalence.to hyp refl)
⇔→≡ {false} {false}         hyp = refl


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

push-function-into-if = if-float
{-# WARNING_ON_USAGE push-function-into-if
"Warning: push-function-into-if was deprecated in v2.0.
Please use if-float instead."
#-}

-- Version 2.4

infix 4 _≟_
_≟_ = _≡?_
{-# WARNING_ON_USAGE _≟_
"Warning: _≟_ was deprecated in v2.4.
Please use _≡?_ instead."
#-}
