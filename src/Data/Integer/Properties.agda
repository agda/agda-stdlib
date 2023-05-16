------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about integers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.Properties where

open import Algebra.Bundles
import Algebra.Morphism as Morphism
open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MinMaxOp as MinMaxOp
import Algebra.Lattice.Construct.NaturalChoice.MinMaxOp as LatticeMinMaxOp
import Algebra.Properties.AbelianGroup
open import Data.Bool.Base using (T; true; false)
open import Data.Integer.Base renaming (suc to sucℤ)
open import Data.Nat as ℕ
  using (ℕ; suc; zero; _∸_; s≤s; z≤n; s<s; z<s)
  hiding (module ℕ)
import Data.Nat.Properties as ℕ
open import Data.Nat.Solver
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sign as Sign using (Sign) renaming (_*_ to _𝕊*_)
import Data.Sign.Properties as 𝕊ₚ
open import Data.Product using (_×_)
open import Function.Base using (_∘_; _$_; id)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no; ¬_)
import Relation.Nullary.Reflects as Reflects
open import Relation.Nullary.Negation using (contradiction)
import Relation.Nullary.Decidable as Dec

open import Algebra.Definitions {A = ℤ} _≡_
open import Algebra.Consequences.Propositional
open import Algebra.Structures {A = ℤ} _≡_
module ℤtoℕ = Morphism.Definitions ℤ ℕ _≡_
module ℕtoℤ = Morphism.Definitions ℕ ℤ _≡_
open +-*-Solver

private
  variable
    m n o : ℕ
    i j k : ℤ
    s t   : Sign

------------------------------------------------------------------------
-- Equality
------------------------------------------------------------------------

+-injective : + m ≡ + n → m ≡ n
+-injective refl = refl

-[1+-injective : -[1+ m ] ≡ -[1+ n ] → m ≡ n
-[1+-injective refl = refl

+[1+-injective : +[1+ m ] ≡ +[1+ n ] → m ≡ n
+[1+-injective refl = refl

infix 4 _≟_
_≟_ : DecidableEquality ℤ
+ m      ≟ + n      = Dec.map′ (cong (+_)) +-injective (m ℕ.≟ n)
+ m      ≟ -[1+ n ] = no λ()
-[1+ m ] ≟ + n      = no λ()
-[1+ m ] ≟ -[1+ n ] = Dec.map′ (cong -[1+_]) -[1+-injective (m ℕ.≟ n)

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid ℤ

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------

drop‿+≤+ : + m ≤ + n → m ℕ.≤ n
drop‿+≤+ (+≤+ m≤n) = m≤n

drop‿-≤- : -[1+ m ] ≤ -[1+ n ] → n ℕ.≤ m
drop‿-≤- (-≤- n≤m) = n≤m

------------------------------------------------------------------------
-- Relational properties

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive { -[1+ n ]} refl = -≤- ℕ.≤-refl
≤-reflexive {+ n}       refl = +≤+ ℕ.≤-refl

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive refl

≤-trans : Transitive _≤_
≤-trans -≤+       (+≤+ n≤m) = -≤+
≤-trans (-≤- n≤m) -≤+       = -≤+
≤-trans (-≤- n≤m) (-≤- k≤n) = -≤- (ℕ.≤-trans k≤n n≤m)
≤-trans (+≤+ m≤n) (+≤+ n≤k) = +≤+ (ℕ.≤-trans m≤n n≤k)

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym (-≤- n≤m) (-≤- m≤n) = cong -[1+_] $ ℕ.≤-antisym m≤n n≤m
≤-antisym (+≤+ m≤n) (+≤+ n≤m) = cong (+_)   $ ℕ.≤-antisym m≤n n≤m

≤-total : Total _≤_
≤-total (-[1+ m ]) (-[1+ n ]) = Sum.map -≤- -≤- (ℕ.≤-total n m)
≤-total (-[1+ m ]) (+    n  ) = inj₁ -≤+
≤-total (+    m  ) (-[1+ n ]) = inj₂ -≤+
≤-total (+    m  ) (+    n  ) = Sum.map +≤+ +≤+ (ℕ.≤-total m n)

infix  4 _≤?_
_≤?_ : Decidable _≤_
-[1+ m ] ≤? -[1+ n ] = Dec.map′ -≤- drop‿-≤- (n ℕ.≤? m)
-[1+ m ] ≤? +    n   = yes -≤+
+    m   ≤? -[1+ n ] = no λ ()
+    m   ≤? +    n   = Dec.map′ +≤+ drop‿+≤+ (m ℕ.≤? n)

≤-irrelevant : Irrelevant _≤_
≤-irrelevant -≤+       -≤+         = refl
≤-irrelevant (-≤- n≤m₁) (-≤- n≤m₂) = cong -≤- (ℕ.≤-irrelevant n≤m₁ n≤m₂)
≤-irrelevant (+≤+ n≤m₁) (+≤+ n≤m₂) = cong +≤+ (ℕ.≤-irrelevant n≤m₁ n≤m₂)

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
-- Properties of _≤ᵇ_
------------------------------------------------------------------------

≤ᵇ⇒≤ : T (i ≤ᵇ j) → i ≤ j
≤ᵇ⇒≤ {+ _}       {+ _}       i≤j = +≤+ (ℕ.≤ᵇ⇒≤ _ _ i≤j)
≤ᵇ⇒≤ { -[1+ _ ]} {+ _}       i≤j = -≤+
≤ᵇ⇒≤ { -[1+ _ ]} { -[1+ _ ]} i≤j = -≤- (ℕ.≤ᵇ⇒≤ _ _ i≤j)

≤⇒≤ᵇ : i ≤ j → T (i ≤ᵇ j)
≤⇒≤ᵇ (-≤- n≤m) = ℕ.≤⇒≤ᵇ n≤m
≤⇒≤ᵇ -≤+ = _
≤⇒≤ᵇ (+≤+ m≤n) = ℕ.≤⇒≤ᵇ m≤n

------------------------------------------------------------------------
-- Properties _<_
------------------------------------------------------------------------

drop‿+<+ : + m < + n → m ℕ.< n
drop‿+<+ (+<+ m<n) = m<n

drop‿-<- : -[1+ m ] < -[1+ n ] → n ℕ.< m
drop‿-<- (-<- n<m) = n<m

+≮0 : + n ≮ +0
+≮0 (+<+ ())

+≮- : + m ≮ -[1+ n ]
+≮- ()

------------------------------------------------------------------------
-- Relationship between other operators

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (-<- i<j) = -≤- (ℕ.<⇒≤ i<j)
<⇒≤ -<+       = -≤+
<⇒≤ (+<+ i<j) = +≤+ (ℕ.<⇒≤ i<j)

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ (-<- n<m) refl = ℕ.<⇒≢ n<m refl
<⇒≢ (+<+ m<n) refl = ℕ.<⇒≢ m<n refl

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ (-<- n<m) = ℕ.<⇒≱ n<m ∘ drop‿-≤-
<⇒≱ (+<+ m<n) = ℕ.<⇒≱ m<n ∘ drop‿+≤+

≤⇒≯ : _≤_ ⇒ _≯_
≤⇒≯ (-≤- n≤m) (-<- n<m) = ℕ.≤⇒≯ n≤m n<m
≤⇒≯ -≤+ = +≮-
≤⇒≯ (+≤+ m≤n) (+<+ m<n) = ℕ.≤⇒≯ m≤n m<n

≰⇒> : _≰_ ⇒ _>_
≰⇒> {+ n}       {+_ n₁}      i≰j = +<+ (ℕ.≰⇒> (i≰j ∘ +≤+))
≰⇒> {+ n}       { -[1+_] n₁} i≰j = -<+
≰⇒> { -[1+_] n} {+_ n₁}      i≰j = contradiction -≤+ i≰j
≰⇒> { -[1+_] n} { -[1+_] n₁} i≰j = -<- (ℕ.≰⇒> (i≰j ∘ -≤-))

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ {+ i}       {+ j}       i≮j = +≤+ (ℕ.≮⇒≥ (i≮j ∘ +<+))
≮⇒≥ {+ i}       { -[1+_] j} i≮j = -≤+
≮⇒≥ { -[1+_] i} {+ j}       i≮j = contradiction -<+ i≮j
≮⇒≥ { -[1+_] i} { -[1+_] j} i≮j = -≤- (ℕ.≮⇒≥ (i≮j ∘ -<-))

>⇒≰ : _>_ ⇒ _≰_
>⇒≰ = <⇒≱

≤∧≢⇒< : i ≤ j → i ≢ j → i < j
≤∧≢⇒< (-≤- m≤n) i≢j = -<- (ℕ.≤∧≢⇒< m≤n (i≢j ∘ cong -[1+_] ∘ sym))
≤∧≢⇒< -≤+  i≢j      = -<+
≤∧≢⇒< (+≤+ n≤m) i≢j = +<+ (ℕ.≤∧≢⇒< n≤m (i≢j ∘ cong (+_)))

≤∧≮⇒≡ : i ≤ j → i ≮ j → i ≡ j
≤∧≮⇒≡ i≤j i≮j = ≤-antisym i≤j (≮⇒≥ i≮j)

------------------------------------------------------------------------
-- Relational properties

<-irrefl : Irreflexive _≡_ _<_
<-irrefl { -[1+ n ]} refl = ℕ.<-irrefl refl ∘ drop‿-<-
<-irrefl { +0}       refl (+<+ ())
<-irrefl { +[1+ n ]} refl = ℕ.<-irrefl refl ∘ drop‿+<+

<-asym : Asymmetric _<_
<-asym (-<- n<m) = ℕ.<-asym n<m ∘ drop‿-<-
<-asym (+<+ m<n) = ℕ.<-asym m<n ∘ drop‿+<+

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans (-≤- n≤m) (-<- o<n) = -<- (ℕ.<-transˡ o<n n≤m)
≤-<-trans (-≤- n≤m) -<+       = -<+
≤-<-trans -≤+       (+<+ m<o) = -<+
≤-<-trans (+≤+ m≤n) (+<+ n<o) = +<+ (ℕ.<-transʳ m≤n n<o)

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans (-<- n<m) (-≤- o≤n) = -<- (ℕ.<-transʳ o≤n n<m)
<-≤-trans (-<- n<m) -≤+       = -<+
<-≤-trans -<+       (+≤+ m≤n) = -<+
<-≤-trans (+<+ m<n) (+≤+ n≤o) = +<+ (ℕ.<-transˡ m<n n≤o)

<-trans : Transitive _<_
<-trans m<n n<p = ≤-<-trans (<⇒≤ m<n) n<p

<-cmp : Trichotomous _≡_ _<_
<-cmp +0       +0       = tri≈ +≮0 refl +≮0
<-cmp +0       +[1+ n ] = tri< (+<+ z<s) (λ()) +≮0
<-cmp +[1+ n ] +0       = tri> +≮0 (λ()) (+<+ z<s)
<-cmp (+ m)    -[1+ n ] = tri> +≮- (λ()) -<+
<-cmp -[1+ m ] (+ n)    = tri< -<+ (λ()) +≮-
<-cmp -[1+ m ] -[1+ n ] with ℕ.<-cmp m n
... | tri< m<n m≢n n≯m = tri> (n≯m ∘ drop‿-<-) (m≢n ∘ -[1+-injective) (-<- m<n)
... | tri≈ m≮n m≡n n≯m = tri≈ (n≯m ∘ drop‿-<-) (cong -[1+_] m≡n) (m≮n ∘ drop‿-<-)
... | tri> m≮n m≢n n>m = tri< (-<- n>m) (m≢n ∘ -[1+-injective) (m≮n ∘ drop‿-<-)
<-cmp +[1+ m ] +[1+ n ] with ℕ.<-cmp m n
... | tri< m<n m≢n n≯m = tri< (+<+ (s<s m<n))              (m≢n ∘ +[1+-injective) (n≯m ∘ ℕ.≤-pred ∘ drop‿+<+)
... | tri≈ m≮n m≡n n≯m = tri≈ (m≮n ∘ ℕ.≤-pred ∘ drop‿+<+) (cong (+_ ∘ suc) m≡n)  (n≯m ∘ ℕ.≤-pred ∘ drop‿+<+)
... | tri> m≮n m≢n n>m = tri> (m≮n ∘ ℕ.≤-pred ∘ drop‿+<+) (m≢n ∘ +[1+-injective) (+<+ (s<s n>m))

infix 4 _<?_
_<?_ : Decidable _<_
-[1+ m ] <? -[1+ n ] = Dec.map′ -<- drop‿-<- (n ℕ.<? m)
-[1+ m ] <? + n      = yes -<+
+ m      <? -[1+ n ] = no λ()
+ m      <? + n      = Dec.map′ +<+ drop‿+<+ (m ℕ.<? n)

<-irrelevant : Irrelevant _<_
<-irrelevant (-<- n<m₁) (-<- n<m₂) = cong -<- (ℕ.<-irrelevant n<m₁ n<m₂)
<-irrelevant -<+       -<+         = refl
<-irrelevant (+<+ m<n₁) (+<+ m<n₂) = cong +<+ (ℕ.<-irrelevant m<n₁ m<n₂)

------------------------------------------------------------------------
-- Structures

<-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<_
<-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl        = <-irrefl
  ; trans         = <-trans
  ; <-resp-≈      = subst (_ <_) , subst (_< _)
  }

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

------------------------------------------------------------------------
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
-- Other properties of _<_

i≮i : i ≮ i
i≮i = <-irrefl refl

>-irrefl : Irreflexive _≡_ _>_
>-irrefl = <-irrefl ∘ sym

------------------------------------------------------------------------
-- A specialised module for reasoning about the _≤_ and _<_ relations
------------------------------------------------------------------------

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    (resp₂ _<_)
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public
    hiding (step-≈; step-≈˘)

------------------------------------------------------------------------
-- Properties of Positive/NonPositive/Negative/NonNegative and _≤_/_<_

positive⁻¹ : ∀ i → .{{Positive i}} → i > 0ℤ
positive⁻¹ +[1+ n ] = +<+ z<s

negative⁻¹ : ∀ i → .{{Negative i}} → i < 0ℤ
negative⁻¹ -[1+ n ] = -<+

nonPositive⁻¹ : ∀ i → .{{NonPositive i}} → i ≤ 0ℤ
nonPositive⁻¹ +0       = +≤+ z≤n
nonPositive⁻¹ -[1+ n ] = -≤+

nonNegative⁻¹ : ∀ i → .{{NonNegative i}} → i ≥ 0ℤ
nonNegative⁻¹ (+ n) = +≤+ z≤n

negative<positive : ∀ i j → .{{Negative i}} → .{{Positive j}} → i < j
negative<positive i j = <-trans (negative⁻¹ i) (positive⁻¹ j)

------------------------------------------------------------------------
-- Properties of -_
------------------------------------------------------------------------

neg-involutive : ∀ i → - - i ≡ i
neg-involutive -[1+ n ] = refl
neg-involutive +0       = refl
neg-involutive +[1+ n ] = refl

neg-injective : - i ≡ - j → i ≡ j
neg-injective {i} {j} -i≡-j = begin
  i     ≡˘⟨ neg-involutive i ⟩
  - - i ≡⟨  cong -_ -i≡-j ⟩
  - - j ≡⟨  neg-involutive j ⟩
  j     ∎ where open ≡-Reasoning

neg-≤-pos : ∀ {m n} → - (+ m) ≤ + n
neg-≤-pos {zero}  = +≤+ z≤n
neg-≤-pos {suc m} = -≤+

neg-mono-≤ : -_ Preserves _≤_ ⟶ _≥_
neg-mono-≤ -≤+             = neg-≤-pos
neg-mono-≤ (-≤- n≤m)       = +≤+ (s≤s n≤m)
neg-mono-≤ (+≤+ z≤n)       = neg-≤-pos
neg-mono-≤ (+≤+ (s≤s m≤n)) = -≤- m≤n

neg-cancel-≤ : - i ≤ - j → i ≥ j
neg-cancel-≤ { +[1+ m ]} { +[1+ n ]} (-≤- n≤m)        = +≤+ (s≤s n≤m)
neg-cancel-≤ { +[1+ m ]} { +0}        -≤+             = +≤+ z≤n
neg-cancel-≤ { +[1+ m ]} { -[1+ n ]}  -≤+             = -≤+
neg-cancel-≤ { +0}       { +0}        _               = +≤+ z≤n
neg-cancel-≤ { +0}       { -[1+ n ]}  _               = -≤+
neg-cancel-≤ { -[1+ m ]} { +0}        (+≤+ ())
neg-cancel-≤ { -[1+ m ]} { -[1+ n ]}  (+≤+ (s≤s m≤n)) = -≤- m≤n

neg-mono-< : -_ Preserves _<_ ⟶ _>_
neg-mono-< { -[1+ _ ]} { -[1+ _ ]} (-<- n<m) = +<+ (s<s n<m)
neg-mono-< { -[1+ _ ]} { +0}       -<+       = +<+ z<s
neg-mono-< { -[1+ _ ]} { +[1+ n ]} -<+       = -<+
neg-mono-< { +0}       { +[1+ n ]} (+<+ _)   = -<+
neg-mono-< { +[1+ m ]} { +[1+ n ]} (+<+ m<n) = -<- (ℕ.≤-pred m<n)

neg-cancel-< : - i < - j → i > j
neg-cancel-< { +[1+ m ]} { +[1+ n ]} (-<- n<m)       = +<+ (s<s n<m)
neg-cancel-< { +[1+ m ]} { +0}        -<+            = +<+ z<s
neg-cancel-< { +[1+ m ]} { -[1+ n ]}  -<+            = -<+
neg-cancel-< { +0}       { +0}       (+<+ ())
neg-cancel-< { +0}       { -[1+ n ]} _               = -<+
neg-cancel-< { -[1+ m ]} { +0}       (+<+ ())
neg-cancel-< { -[1+ m ]} { -[1+ n ]} (+<+ (s<s m<n)) = -<- m<n

------------------------------------------------------------------------
-- Properties of ∣_∣
------------------------------------------------------------------------

∣i∣≡0⇒i≡0 : ∣ i ∣ ≡ 0 → i ≡ + 0
∣i∣≡0⇒i≡0 {+0} refl = refl

∣-i∣≡∣i∣ : ∀ i → ∣ - i ∣ ≡ ∣ i ∣
∣-i∣≡∣i∣ -[1+ n ] = refl
∣-i∣≡∣i∣ +0       = refl
∣-i∣≡∣i∣ +[1+ n ] = refl

0≤i⇒+∣i∣≡i : 0ℤ ≤ i → + ∣ i ∣ ≡ i
0≤i⇒+∣i∣≡i (+≤+ _) = refl

+∣i∣≡i⇒0≤i : + ∣ i ∣ ≡ i → 0ℤ ≤ i
+∣i∣≡i⇒0≤i {+ n} _ = +≤+ z≤n

+∣i∣≡i⊎+∣i∣≡-i : ∀ i → + ∣ i ∣ ≡ i ⊎ + ∣ i ∣ ≡ - i
+∣i∣≡i⊎+∣i∣≡-i (+ n)      = inj₁ refl
+∣i∣≡i⊎+∣i∣≡-i (-[1+ n ]) = inj₂ refl

∣m⊝n∣≤m⊔n : ∀ m n → ∣ m ⊖ n ∣ ℕ.≤ m ℕ.⊔ n
∣m⊝n∣≤m⊔n m n with m ℕ.<ᵇ n
... | true = begin
  ∣ - + (n ℕ.∸ m) ∣                ≡⟨ ∣-i∣≡∣i∣ (+ (n ℕ.∸ m)) ⟩
  ∣ + (n ℕ.∸ m) ∣                  ≡⟨⟩
  n ℕ.∸ m                          ≤⟨ ℕ.m∸n≤m n m ⟩
  n                                ≤⟨ ℕ.m≤n⊔m m n ⟩
  m ℕ.⊔ n                          ∎
  where open ℕ.≤-Reasoning
... | false = begin
  ∣ + (m ℕ.∸ n) ∣                  ≡⟨⟩
  m ℕ.∸ n                          ≤⟨ ℕ.m∸n≤m m n ⟩
  m                                ≤⟨ ℕ.m≤m⊔n m n ⟩
  m ℕ.⊔ n                          ∎
  where open ℕ.≤-Reasoning

∣i+j∣≤∣i∣+∣j∣ : ∀ i j → ∣ i + j ∣ ℕ.≤ ∣ i ∣ ℕ.+ ∣ j ∣
∣i+j∣≤∣i∣+∣j∣ +[1+ m ] (+ n)    = ℕ.≤-refl
∣i+j∣≤∣i∣+∣j∣ +0       (+ n)    = ℕ.≤-refl
∣i+j∣≤∣i∣+∣j∣ +0       -[1+ n ] = ℕ.≤-refl
∣i+j∣≤∣i∣+∣j∣ -[1+ m ] -[1+ n ] rewrite ℕ.+-suc (suc m) n = ℕ.≤-refl
∣i+j∣≤∣i∣+∣j∣ +[1+ m ] -[1+ n ] = begin
  ∣ suc m ⊖ suc n ∣  ≤⟨ ∣m⊝n∣≤m⊔n (suc m) (suc n) ⟩
  suc m ℕ.⊔ suc n    ≤⟨ ℕ.m⊔n≤m+n (suc m) (suc n) ⟩
  suc m ℕ.+ suc n    ∎
  where open ℕ.≤-Reasoning
∣i+j∣≤∣i∣+∣j∣ -[1+ m ] (+ n)    = begin
  ∣ n ⊖ suc m ∣  ≤⟨ ∣m⊝n∣≤m⊔n  n (suc m) ⟩
  n ℕ.⊔ suc m    ≤⟨ ℕ.m⊔n≤m+n n (suc m) ⟩
  n ℕ.+ suc m    ≡⟨ ℕ.+-comm  n (suc m) ⟩
  suc m ℕ.+ n    ∎
  where open ℕ.≤-Reasoning

∣i-j∣≤∣i∣+∣j∣ : ∀ i j → ∣ i - j ∣ ℕ.≤ ∣ i ∣ ℕ.+ ∣ j ∣
∣i-j∣≤∣i∣+∣j∣ i j = begin
  ∣ i   -       j ∣        ≤⟨ ∣i+j∣≤∣i∣+∣j∣ i (- j) ⟩
  ∣ i ∣ ℕ.+ ∣ - j ∣        ≡⟨ cong (∣ i ∣ ℕ.+_) (∣-i∣≡∣i∣ j) ⟩
  ∣ i ∣ ℕ.+ ∣   j ∣        ∎
  where open ℕ.≤-Reasoning

------------------------------------------------------------------------
-- Properties of sign and _◃_

◃-inverse : ∀ i → sign i ◃ ∣ i ∣ ≡ i
◃-inverse -[1+ n ] = refl
◃-inverse +0       = refl
◃-inverse +[1+ n ] = refl

◃-cong : sign i ≡ sign j → ∣ i ∣ ≡ ∣ j ∣ → i ≡ j
◃-cong {+ m}       {+ n }      ≡-sign refl = refl
◃-cong { -[1+ m ]} { -[1+ n ]} ≡-sign refl = refl

+◃n≡+n : ∀ n → Sign.+ ◃ n ≡ + n
+◃n≡+n zero    = refl
+◃n≡+n (suc _) = refl

-◃n≡-n : ∀ n → Sign.- ◃ n ≡ - + n
-◃n≡-n zero    = refl
-◃n≡-n (suc _) = refl

sign-◃ : ∀ s n .{{_ : ℕ.NonZero n}} → sign (s ◃ n) ≡ s
sign-◃ Sign.- (suc _) = refl
sign-◃ Sign.+ (suc _) = refl

abs-◃ : ∀ s n → ∣ s ◃ n ∣ ≡ n
abs-◃ _      zero    = refl
abs-◃ Sign.- (suc n) = refl
abs-◃ Sign.+ (suc n) = refl

signᵢ◃∣i∣≡i : ∀ i → sign i ◃ ∣ i ∣ ≡ i
signᵢ◃∣i∣≡i (+ n)    = +◃n≡+n n
signᵢ◃∣i∣≡i -[1+ n ] = refl

sign-cong : .{{_ : ℕ.NonZero m}} .{{_ : ℕ.NonZero n}} →
            s ◃ m ≡ t ◃ n → s ≡ t
sign-cong {n@(suc _)} {m@(suc _)} {s} {t} eq = begin
  s             ≡˘⟨ sign-◃ s n ⟩
  sign (s ◃ n)  ≡⟨  cong sign eq ⟩
  sign (t ◃ m)  ≡⟨  sign-◃ t m ⟩
  t             ∎ where open ≡-Reasoning

sign-cong′ : s ◃ m ≡ t ◃ n → s ≡ t ⊎ (m ≡ 0 × n ≡ 0)
sign-cong′ {s}       {zero}  {t}       {zero}  eq = inj₂ (refl , refl)
sign-cong′ {s}       {zero}  {Sign.- } {suc n} ()
sign-cong′ {s}       {zero}  {Sign.+ } {suc n} ()
sign-cong′ {Sign.- } {suc m} {t}       {zero}  ()
sign-cong′ {Sign.+ } {suc m} {t}       {zero}  ()
sign-cong′ {s}       {suc m} {t}       {suc n} eq = inj₁ (sign-cong eq)

abs-cong : s ◃ m ≡ t ◃ n → m ≡ n
abs-cong {s} {m} {t} {n} eq = begin
  m          ≡˘⟨ abs-◃ s m ⟩
  ∣ s ◃ m ∣  ≡⟨  cong ∣_∣ eq ⟩
  ∣ t ◃ n ∣  ≡⟨  abs-◃ t n ⟩
  n          ∎ where open ≡-Reasoning

∣s◃m∣*∣t◃n∣≡m*n : ∀ s t m n → ∣ s ◃ m ∣ ℕ.* ∣ t ◃ n ∣ ≡ m ℕ.* n
∣s◃m∣*∣t◃n∣≡m*n s t m n = cong₂ ℕ._*_ (abs-◃ s m) (abs-◃ t n)

+◃-mono-< : m ℕ.< n → Sign.+ ◃ m < Sign.+ ◃ n
+◃-mono-< {zero}  {suc n} m<n = +<+ m<n
+◃-mono-< {suc m} {suc n} m<n = +<+ m<n

+◃-cancel-< : Sign.+ ◃ m < Sign.+ ◃ n → m ℕ.< n
+◃-cancel-< {zero}  {zero}  (+<+ ())
+◃-cancel-< {suc m} {zero}  (+<+ ())
+◃-cancel-< {zero}  {suc n} (+<+ m<n) = m<n
+◃-cancel-< {suc m} {suc n} (+<+ m<n) = m<n

neg◃-cancel-< : Sign.- ◃ m < Sign.- ◃ n → n ℕ.< m
neg◃-cancel-< {zero}  {zero}  (+<+ ())
neg◃-cancel-< {suc m} {zero}  -<+       = z<s
neg◃-cancel-< {suc m} {suc n} (-<- n<m) = s<s n<m

-◃<+◃ : ∀ m n .{{_ : ℕ.NonZero m}} → Sign.- ◃ m < Sign.+ ◃ n
-◃<+◃ (suc _) zero    = -<+
-◃<+◃ (suc _) (suc _) = -<+

+◃≮-◃ : Sign.+ ◃ m ≮ Sign.- ◃ n
+◃≮-◃ {zero}  {zero} (+<+ ())
+◃≮-◃ {suc m} {zero} (+<+ ())

------------------------------------------------------------------------
-- Properties of _⊖_
------------------------------------------------------------------------

n⊖n≡0 : ∀ n → n ⊖ n ≡ 0ℤ
n⊖n≡0 n with n ℕ.<ᵇ n in leq
... | true  = cong (-_ ∘ +_) (ℕ.n∸n≡0 n) -- this is actually impossible!
... | false = cong +_ (ℕ.n∸n≡0 n)

[1+m]⊖[1+n]≡m⊖n : ∀ m n → suc m ⊖ suc n ≡ m ⊖ n
[1+m]⊖[1+n]≡m⊖n m n with m ℕ.<ᵇ n
... | true  = refl
... | false = refl

⊖-swap : ∀ m n → m ⊖ n ≡ - (n ⊖ m)
⊖-swap zero    zero    = refl
⊖-swap zero    (suc m) = refl
⊖-swap (suc m) zero    = refl
⊖-swap (suc m) (suc n) = begin
  suc m ⊖ suc n     ≡⟨ [1+m]⊖[1+n]≡m⊖n m n ⟩
  m ⊖ n             ≡⟨ ⊖-swap m n ⟩
  - (n ⊖ m)         ≡˘⟨ cong -_ ([1+m]⊖[1+n]≡m⊖n n m) ⟩
  - (suc n ⊖ suc m) ∎ where open ≡-Reasoning

⊖-≥ : m ℕ.≥ n → m ⊖ n ≡ + (m ∸ n)
⊖-≥ {m} {n} p with m ℕ.<ᵇ n | Reflects.invert (ℕ.<ᵇ-reflects-< m n)
... | true  | q = contradiction (ℕ.<-transʳ p q) (ℕ.<-irrefl refl)
... | false | q = refl

≤-⊖ : m ℕ.≤ n → n ⊖ m ≡ + (n ∸ m)
≤-⊖ (z≤n {n})       = refl
≤-⊖ (s≤s {m} {n} p) = begin
  suc n ⊖ suc m     ≡⟨ [1+m]⊖[1+n]≡m⊖n n m ⟩
  n ⊖ m             ≡⟨ ≤-⊖ p ⟩
  + (n ∸ m)         ≡⟨⟩
  + (suc n ∸ suc m) ∎ where open ≡-Reasoning

⊖-≤ : m ℕ.≤ n → m ⊖ n ≡ - + (n ∸ m)
⊖-≤ {m} {n} p with m ℕ.<ᵇ n | Reflects.invert (ℕ.<ᵇ-reflects-< m n)
... | true  | q = refl
... | false | q rewrite ℕ.≤-antisym p (ℕ.≮⇒≥ q) | ℕ.n∸n≡0 n = refl

⊖-< : m ℕ.< n → m ⊖ n ≡ - + (n ∸ m)
⊖-< = ⊖-≤ ∘ ℕ.<⇒≤

⊖-≰ : n ℕ.≰ m → m ⊖ n ≡ - + (n ∸ m)
⊖-≰ = ⊖-< ∘ ℕ.≰⇒>

∣⊖∣-≤ : m ℕ.≤ n → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-≤ {m} {n} p = begin
  ∣ m ⊖ n ∣         ≡⟨ cong ∣_∣ (⊖-≤ p) ⟩
  ∣ - (+ (n ∸ m)) ∣ ≡⟨ ∣-i∣≡∣i∣ (+ (n ∸ m)) ⟩
  ∣ + (n ∸ m) ∣     ≡⟨⟩
  n ∸ m             ∎ where open ≡-Reasoning

∣⊖∣-< : m ℕ.< n → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-< {m} {n} p = begin
  ∣ m ⊖ n ∣         ≡⟨ cong ∣_∣ (⊖-< p) ⟩
  ∣ - (+ (n ∸ m)) ∣ ≡⟨ ∣-i∣≡∣i∣ (+ (n ∸ m)) ⟩
  ∣ + (n ∸ m) ∣     ≡⟨⟩
  n ∸ m             ∎ where open ≡-Reasoning

∣⊖∣-≰ : n ℕ.≰ m → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-≰ = ∣⊖∣-< ∘ ℕ.≰⇒>

-m+n≡n⊖m : ∀ m n → - (+ m) + + n ≡ n ⊖ m
-m+n≡n⊖m zero    n = refl
-m+n≡n⊖m (suc m) n = refl

m-n≡m⊖n : ∀ m n → + m + (- + n) ≡ m ⊖ n
m-n≡m⊖n zero    zero    = refl
m-n≡m⊖n zero    (suc n) = refl
m-n≡m⊖n (suc m) zero    = cong +[1+_] (ℕ.+-identityʳ m)
m-n≡m⊖n (suc m) (suc n) = refl

-[n⊖m]≡-m+n : ∀ m n → - (m ⊖ n) ≡ (- (+ m)) + (+ n)
-[n⊖m]≡-m+n m n with m ℕ.<ᵇ n | Reflects.invert (ℕ.<ᵇ-reflects-< m n)
... | true  | p = begin
  - (- (+ (n ∸ m))) ≡⟨ neg-involutive (+ (n ∸ m)) ⟩
  + (n ∸ m)         ≡˘⟨ ⊖-≥ (ℕ.≤-trans (ℕ.m≤n+m m 1) p) ⟩
  n ⊖ m             ≡˘⟨ -m+n≡n⊖m m n ⟩
  - (+ m) + + n     ∎ where open ≡-Reasoning
... | false | p = begin
  - (+ (m ∸ n))     ≡˘⟨ ⊖-≤ (ℕ.≮⇒≥ p) ⟩
  n ⊖ m             ≡˘⟨ -m+n≡n⊖m m n ⟩
  - (+ m) + + n     ∎ where open ≡-Reasoning

∣m⊖n∣≡∣n⊖m∣ : ∀ m n → ∣ m ⊖ n ∣ ≡ ∣ n ⊖ m ∣
∣m⊖n∣≡∣n⊖m∣ m n = begin
  ∣ m ⊖ n ∣     ≡⟨ cong ∣_∣ (⊖-swap m n) ⟩
  ∣ - (n ⊖ m) ∣ ≡⟨ ∣-i∣≡∣i∣ (n ⊖ m) ⟩
  ∣ n ⊖ m ∣     ∎ where open ≡-Reasoning

+-cancelˡ-⊖ : ∀ m n o → (m ℕ.+ n) ⊖ (m ℕ.+ o) ≡ n ⊖ o
+-cancelˡ-⊖ zero    n o = refl
+-cancelˡ-⊖ (suc m) n o = begin
  suc (m ℕ.+ n) ⊖ suc (m ℕ.+ o) ≡⟨ [1+m]⊖[1+n]≡m⊖n (m ℕ.+ n) (m ℕ.+ o) ⟩
  m ℕ.+ n ⊖ (m ℕ.+ o)           ≡⟨ +-cancelˡ-⊖ m n o ⟩
  n ⊖ o                         ∎ where open ≡-Reasoning

m⊖n≤m : ∀ m n → m ⊖ n ≤ + m
m⊖n≤m m       zero    = ≤-refl
m⊖n≤m zero    (suc n) = -≤+
m⊖n≤m (suc m) (suc n) = begin
  suc m ⊖ suc n ≡⟨ [1+m]⊖[1+n]≡m⊖n m n ⟩
  m ⊖ n         ≤⟨ m⊖n≤m m n ⟩
  + m           ≤⟨ +≤+ (ℕ.n≤1+n m) ⟩
  +[1+ m ]      ∎ where open ≤-Reasoning

m⊖n<1+m : ∀ m n → m ⊖ n < +[1+ m ]
m⊖n<1+m m n = ≤-<-trans (m⊖n≤m m n) (+<+ (ℕ.m<n+m m z<s))

m⊖1+n<m : ∀ m n .{{_ : ℕ.NonZero n}} → m ⊖ n < + m
m⊖1+n<m zero    (suc n) = -<+
m⊖1+n<m (suc m) (suc n) = begin-strict
  suc m ⊖ suc n ≡⟨ [1+m]⊖[1+n]≡m⊖n m n ⟩
  m ⊖ n         <⟨ m⊖n<1+m m n ⟩
  +[1+ m ]      ∎ where open ≤-Reasoning

-1+m<n⊖m : ∀ m n → -[1+ m ] < n ⊖ m
-1+m<n⊖m zero    n       = -<+
-1+m<n⊖m (suc m) zero    = -<- ℕ.≤-refl
-1+m<n⊖m (suc m) (suc n) = begin-strict
  -[1+ suc m ]  <⟨ -<- ℕ.≤-refl ⟩
  -[1+ m ]      <⟨ -1+m<n⊖m m n ⟩
  n ⊖ m         ≡˘⟨ [1+m]⊖[1+n]≡m⊖n n m ⟩
  suc n ⊖ suc m ∎ where open ≤-Reasoning

-[1+m]≤n⊖m+1 : ∀ m n → -[1+ m ] ≤ n ⊖ suc m
-[1+m]≤n⊖m+1 m zero    = ≤-refl
-[1+m]≤n⊖m+1 m (suc n) = begin
  -[1+ m ]      ≤⟨ <⇒≤ (-1+m<n⊖m m n) ⟩
  n ⊖ m         ≡˘⟨ [1+m]⊖[1+n]≡m⊖n n m ⟩
  suc n ⊖ suc m ∎ where open ≤-Reasoning

-1+m≤n⊖m : ∀ m n → -[1+ m ] ≤ n ⊖ m
-1+m≤n⊖m m n = <⇒≤ (-1+m<n⊖m m n)

0⊖m≤+ : ∀ m {n} → 0 ⊖ m ≤ + n
0⊖m≤+ zero    = +≤+ z≤n
0⊖m≤+ (suc m) = -≤+

sign-⊖-< : m ℕ.< n → sign (m ⊖ n) ≡ Sign.-
sign-⊖-< {zero}          (ℕ.z<s) = refl
sign-⊖-< {suc m} {suc n} (ℕ.s<s m<n) = begin
  sign (suc m ⊖ suc n) ≡⟨ cong sign ([1+m]⊖[1+n]≡m⊖n m n) ⟩
  sign (m ⊖ n)         ≡⟨ sign-⊖-< m<n ⟩
  Sign.-               ∎ where open ≡-Reasoning

sign-⊖-≰ : n ℕ.≰ m → sign (m ⊖ n) ≡ Sign.-
sign-⊖-≰ = sign-⊖-< ∘ ℕ.≰⇒>

⊖-monoʳ-≥-≤ : ∀ n → (n ⊖_) Preserves ℕ._≥_ ⟶ _≤_
⊖-monoʳ-≥-≤ zero    {m}     z≤n      = 0⊖m≤+ m
⊖-monoʳ-≥-≤ zero    {_}    (s≤s m≤n) = -≤- m≤n
⊖-monoʳ-≥-≤ (suc n) {zero}  z≤n      = ≤-refl
⊖-monoʳ-≥-≤ (suc n) {suc m} z≤n      = begin
  suc n ⊖ suc m ≡⟨ [1+m]⊖[1+n]≡m⊖n n m ⟩
  n ⊖ m         <⟨ m⊖n<1+m n m ⟩
  +[1+ n ]      ∎ where open ≤-Reasoning
⊖-monoʳ-≥-≤ (suc n) {suc m} {suc o} (s≤s m≤o) = begin
  suc n ⊖ suc m ≡⟨  [1+m]⊖[1+n]≡m⊖n n m ⟩
  n ⊖ m         ≤⟨  ⊖-monoʳ-≥-≤ n m≤o ⟩
  n ⊖ o         ≡˘⟨ [1+m]⊖[1+n]≡m⊖n n o ⟩
  suc n ⊖ suc o ∎ where open ≤-Reasoning

⊖-monoˡ-≤ : ∀ n → (_⊖ n) Preserves ℕ._≤_ ⟶ _≤_
⊖-monoˡ-≤ zero    {_} {_}     m≤o = +≤+ m≤o
⊖-monoˡ-≤ (suc n) {_} {0}     z≤n = ≤-refl
⊖-monoˡ-≤ (suc n) {_} {suc o} z≤n = begin
  zero ⊖ suc n  ≤⟨  ⊖-monoʳ-≥-≤ 0 (ℕ.n≤1+n n) ⟩
  zero ⊖ n      ≤⟨  ⊖-monoˡ-≤ n z≤n ⟩
  o ⊖ n         ≡˘⟨ [1+m]⊖[1+n]≡m⊖n o n ⟩
  suc o ⊖ suc n ∎ where open ≤-Reasoning
⊖-monoˡ-≤ (suc n) {suc m} {suc o} (s≤s m≤o) = begin
  suc m ⊖ suc n ≡⟨  [1+m]⊖[1+n]≡m⊖n m n ⟩
  m ⊖ n         ≤⟨  ⊖-monoˡ-≤ n m≤o ⟩
  o ⊖ n         ≡˘⟨ [1+m]⊖[1+n]≡m⊖n o n ⟩
  suc o ⊖ suc n ∎ where open ≤-Reasoning

⊖-monoʳ->-< : ∀ p → (p ⊖_) Preserves ℕ._>_ ⟶ _<_
⊖-monoʳ->-< zero    {_}     z<s       = -<+
⊖-monoʳ->-< zero    {_}     (s<s m<n@(s≤s _)) = -<- m<n
⊖-monoʳ->-< (suc p) {suc m} z<s       = begin-strict
  suc p ⊖ suc m ≡⟨ [1+m]⊖[1+n]≡m⊖n p m ⟩
  p ⊖ m         <⟨ m⊖n<1+m p m ⟩
  +[1+ p ]      ∎ where open ≤-Reasoning
⊖-monoʳ->-< (suc p) {suc m} {suc n} (s<s m<n@(s≤s _)) = begin-strict
  suc p ⊖ suc m ≡⟨  [1+m]⊖[1+n]≡m⊖n p m ⟩
  p ⊖ m         <⟨  ⊖-monoʳ->-< p m<n ⟩
  p ⊖ n         ≡˘⟨ [1+m]⊖[1+n]≡m⊖n p n ⟩
  suc p ⊖ suc n ∎ where open ≤-Reasoning

⊖-monoˡ-< : ∀ n → (_⊖ n) Preserves ℕ._<_ ⟶ _<_
⊖-monoˡ-< zero    m<o             = +<+ m<o
⊖-monoˡ-< (suc n) {_} {suc o} z<s = begin-strict
  -[1+ n ]      <⟨  -1+m<n⊖m n _ ⟩
  o ⊖ n         ≡˘⟨ [1+m]⊖[1+n]≡m⊖n o n ⟩
  suc o ⊖ suc n ∎ where open ≤-Reasoning
⊖-monoˡ-< (suc n) {suc m} {suc (suc o)} (s<s m<o@(s≤s _)) = begin-strict
  suc m ⊖ suc n       ≡⟨  [1+m]⊖[1+n]≡m⊖n m n ⟩
  m ⊖ n               <⟨  ⊖-monoˡ-< n m<o ⟩
  suc o ⊖ n           ≡˘⟨ [1+m]⊖[1+n]≡m⊖n (suc o) n ⟩
  suc (suc o) ⊖ suc n ∎ where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _+_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties of _+_

+-comm : Commutative _+_
+-comm -[1+ m ] -[1+ n ] = cong (-[1+_] ∘ suc) (ℕ.+-comm m n)
+-comm (+ m)    (+ n)    = cong +_ (ℕ.+-comm m n)
+-comm -[1+ _ ] (+ _)    = refl
+-comm (+ _)    -[1+ _ ] = refl

+-identityˡ : LeftIdentity +0 _+_
+-identityˡ -[1+ _ ] = refl
+-identityˡ (+ _)    = refl

+-identityʳ : RightIdentity +0 _+_
+-identityʳ = comm+idˡ⇒idʳ +-comm +-identityˡ

+-identity : Identity +0 _+_
+-identity = +-identityˡ , +-identityʳ

distribˡ-⊖-+-pos : ∀ m n o → n ⊖ o + + m ≡ n ℕ.+ m ⊖ o
distribˡ-⊖-+-pos _ zero    zero    = refl
distribˡ-⊖-+-pos _ zero    (suc _) = refl
distribˡ-⊖-+-pos _ (suc _) zero    = refl
distribˡ-⊖-+-pos m (suc n) (suc o) = begin
  suc n ⊖ suc o + + m   ≡⟨ cong (_+ + m) ([1+m]⊖[1+n]≡m⊖n n o) ⟩
  n ⊖ o + + m           ≡⟨ distribˡ-⊖-+-pos m n o ⟩
  n ℕ.+ m ⊖ o           ≡˘⟨ [1+m]⊖[1+n]≡m⊖n (n ℕ.+ m) o ⟩
  suc (n ℕ.+ m) ⊖ suc o ∎ where open ≡-Reasoning

distribˡ-⊖-+-neg : ∀ m n o → n ⊖ o + -[1+ m ] ≡ n ⊖ (suc o ℕ.+ m)
distribˡ-⊖-+-neg _ zero    zero    = refl
distribˡ-⊖-+-neg _ zero    (suc _) = refl
distribˡ-⊖-+-neg _ (suc _) zero    = refl
distribˡ-⊖-+-neg m (suc n) (suc o) = begin
  suc n ⊖ suc o + -[1+ m ]    ≡⟨ cong (_+ -[1+ m ]) ([1+m]⊖[1+n]≡m⊖n n o) ⟩
  n ⊖ o + -[1+ m ]            ≡⟨ distribˡ-⊖-+-neg m n o ⟩
  n ⊖ (suc o ℕ.+ m)           ≡˘⟨ [1+m]⊖[1+n]≡m⊖n n (suc o ℕ.+ m) ⟩
  suc n ⊖ (suc (suc o) ℕ.+ m) ∎ where open ≡-Reasoning

distribʳ-⊖-+-pos : ∀ m n o → + m + (n ⊖ o) ≡ m ℕ.+ n ⊖ o
distribʳ-⊖-+-pos m n o = begin
  + m + (n ⊖ o) ≡⟨ +-comm (+ m) (n ⊖ o) ⟩
  (n ⊖ o) + + m ≡⟨ distribˡ-⊖-+-pos m n o ⟩
  n ℕ.+ m ⊖ o   ≡⟨ cong (_⊖ o) (ℕ.+-comm n m) ⟩
  m ℕ.+ n ⊖ o   ∎ where open ≡-Reasoning

distribʳ-⊖-+-neg : ∀ m n o → -[1+ m ] + (n ⊖ o) ≡ n ⊖ (suc m ℕ.+ o)
distribʳ-⊖-+-neg m n o = begin
  -[1+ m ] + (n ⊖ o) ≡⟨ +-comm -[1+ m ] (n ⊖ o) ⟩
  (n ⊖ o) + -[1+ m ] ≡⟨ distribˡ-⊖-+-neg m n o ⟩
  n ⊖ suc (o ℕ.+ m)  ≡⟨ cong (λ x → n ⊖ suc x) (ℕ.+-comm o m) ⟩
  n ⊖ suc (m ℕ.+ o)  ∎ where open ≡-Reasoning

+-assoc : Associative _+_
+-assoc +0 j k rewrite +-identityˡ      j  | +-identityˡ (j + k) = refl
+-assoc i +0 k rewrite +-identityʳ  i      | +-identityˡ      k  = refl
+-assoc i j +0 rewrite +-identityʳ (i + j) | +-identityʳ  j      = refl
+-assoc -[1+ m ] -[1+ n ] +[1+ o ] = begin
  suc o ⊖ suc (suc (m ℕ.+ n)) ≡⟨ [1+m]⊖[1+n]≡m⊖n o (suc m ℕ.+ n) ⟩
  o ⊖ (suc m ℕ.+ n)           ≡˘⟨ distribʳ-⊖-+-neg m o n ⟩
  -[1+ m ] + (o ⊖ n)          ≡˘⟨ cong (λ z → -[1+ m ] + z) ([1+m]⊖[1+n]≡m⊖n o n) ⟩
  -[1+ m ] + (suc o ⊖ suc n)  ∎ where open ≡-Reasoning
+-assoc -[1+ m ] +[1+ n ] +[1+ o ] = begin
  suc n ⊖ suc m + +[1+ o ]  ≡⟨ cong (_+ +[1+ o ]) ([1+m]⊖[1+n]≡m⊖n n m) ⟩
  (n ⊖ m) + +[1+ o ]        ≡⟨ distribˡ-⊖-+-pos (suc o) n m ⟩
  n ℕ.+ suc o ⊖ m           ≡˘⟨ [1+m]⊖[1+n]≡m⊖n (n ℕ.+ suc o) m ⟩
  suc (n ℕ.+ suc o) ⊖ suc m ∎ where open ≡-Reasoning
+-assoc +[1+ m ] -[1+ n ] -[1+ o ] = begin
  (suc m ⊖ suc n) + -[1+ o ]  ≡⟨ cong (_+ -[1+ o ]) ([1+m]⊖[1+n]≡m⊖n m n) ⟩
  (m ⊖ n) + -[1+ o ]          ≡⟨ distribˡ-⊖-+-neg o m n ⟩
  m ⊖ suc (n ℕ.+ o)           ≡˘⟨ [1+m]⊖[1+n]≡m⊖n m (suc n ℕ.+ o) ⟩
  suc m ⊖ suc (suc (n ℕ.+ o)) ∎ where open ≡-Reasoning
+-assoc +[1+ m ] -[1+ n ] +[1+ o ]
  rewrite [1+m]⊖[1+n]≡m⊖n m n
        | [1+m]⊖[1+n]≡m⊖n o n
        | distribˡ-⊖-+-pos (suc o) m n
        | distribʳ-⊖-+-pos (suc m) o n
        | sym (ℕ.+-assoc m 1 o)
        | ℕ.+-comm m 1
        = refl
+-assoc +[1+ m ] +[1+ n ] -[1+ o ]
  rewrite [1+m]⊖[1+n]≡m⊖n n o
        | [1+m]⊖[1+n]≡m⊖n (m ℕ.+ suc n) o
        | distribʳ-⊖-+-pos (suc m) n o
        | sym (ℕ.+-assoc m 1 n)
        | ℕ.+-comm m 1
        = refl
+-assoc -[1+ m ] -[1+ n ] -[1+ o ]
  rewrite sym (ℕ.+-assoc m 1 (n ℕ.+ o))
        | ℕ.+-comm m 1
        | ℕ.+-assoc m n o
        = refl
+-assoc -[1+ m ] +[1+ n ] -[1+ o ]
  rewrite [1+m]⊖[1+n]≡m⊖n n m
        | [1+m]⊖[1+n]≡m⊖n n o
        | distribʳ-⊖-+-neg m n o
        | distribˡ-⊖-+-neg o n m
        = refl
+-assoc +[1+ m ] +[1+ n ] +[1+ o ]
  rewrite ℕ.+-assoc (suc m) (suc n) (suc o)
        = refl

+-inverseˡ : LeftInverse +0 -_ _+_
+-inverseˡ -[1+ n ] = n⊖n≡0 (suc n)
+-inverseˡ +0       = refl
+-inverseˡ +[1+ n ] = n⊖n≡0 (suc n)

+-inverseʳ : RightInverse +0 -_ _+_
+-inverseʳ = comm+invˡ⇒invʳ +-comm +-inverseˡ

+-inverse : Inverse +0 -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

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

+-0-isMonoid : IsMonoid _+_ +0
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ +0
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm     = +-comm
  }

+-0-isGroup : IsGroup _+_ +0 (-_)
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse  = +-inverse
  ; ⁻¹-cong  = cong (-_)
  }

+-0-isAbelianGroup : IsAbelianGroup _+_ +0 (-_)
+-0-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm    = +-comm
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

+-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-0-isAbelianGroup
  }

------------------------------------------------------------------------
-- Properties of _+_ and +_/-_.

pos-+ : ℕtoℤ.Homomorphic₂ +_ ℕ._+_ _+_
pos-+ zero    n = refl
pos-+ (suc m) n = cong sucℤ (pos-+ m n)

neg-distrib-+ : ∀ i j → - (i + j) ≡ (- i) + (- j)
neg-distrib-+ +0        +0        = refl
neg-distrib-+ +0        +[1+ n ]  = refl
neg-distrib-+ +[1+ m ]  +0        = cong -[1+_] (ℕ.+-identityʳ m)
neg-distrib-+ +[1+ m ]  +[1+ n ]  = cong -[1+_] (ℕ.+-suc m n)
neg-distrib-+ -[1+ m ]  -[1+ n ]  = cong +[1+_] (sym (ℕ.+-suc m n))
neg-distrib-+ (+   m)   -[1+ n ]  = -[n⊖m]≡-m+n m (suc n)
neg-distrib-+ -[1+ m ]  (+   n)   =
  trans (-[n⊖m]≡-m+n n (suc m)) (+-comm (- + n) (+ suc m))

◃-distrib-+ : ∀ s m n → s ◃ (m ℕ.+ n) ≡ (s ◃ m) + (s ◃ n)
◃-distrib-+ Sign.- m n = begin
  Sign.- ◃ (m ℕ.+ n)          ≡⟨ -◃n≡-n (m ℕ.+ n) ⟩
  - (+ (m ℕ.+ n))             ≡⟨⟩
  - ((+ m) + (+ n))           ≡⟨ neg-distrib-+ (+ m) (+ n) ⟩
  (- (+ m)) + (- (+ n))       ≡⟨ sym (cong₂ _+_ (-◃n≡-n m) (-◃n≡-n n)) ⟩
  (Sign.- ◃ m) + (Sign.- ◃ n) ∎ where open ≡-Reasoning
◃-distrib-+ Sign.+ m n = begin
  Sign.+ ◃ (m ℕ.+ n)          ≡⟨ +◃n≡+n (m ℕ.+ n) ⟩
  + (m ℕ.+ n)                 ≡⟨⟩
  (+ m) + (+ n)               ≡⟨ sym (cong₂ _+_ (+◃n≡+n m) (+◃n≡+n n)) ⟩
  (Sign.+ ◃ m) + (Sign.+ ◃ n) ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of _+_ and _≤_

+-monoʳ-≤ : ∀ n → (_+_ n) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ (+ n)    {_}         (-≤- o≤m) = ⊖-monoʳ-≥-≤ n (s≤s o≤m)
+-monoʳ-≤ (+ n)    { -[1+ m ]} -≤+       = ≤-trans (m⊖n≤m n (suc m)) (+≤+ (ℕ.m≤m+n n _))
+-monoʳ-≤ (+ n)    {_}         (+≤+ m≤o) = +≤+ (ℕ.+-monoʳ-≤ n m≤o)
+-monoʳ-≤ -[1+ n ] {_} {_}     (-≤- n≤m) = -≤- (ℕ.+-monoʳ-≤ (suc n) n≤m)
+-monoʳ-≤ -[1+ n ] {_} {+ m}   -≤+       = ≤-trans (-≤- (ℕ.m≤m+n (suc n) _)) (-1+m≤n⊖m (suc n) m)
+-monoʳ-≤ -[1+ n ] {_} {_}     (+≤+ m≤n) = ⊖-monoˡ-≤ (suc n) m≤n

+-monoˡ-≤ : ∀ n → (_+ n) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ n {i} {j} rewrite +-comm i n | +-comm j n = +-monoʳ-≤ n

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {m} {n} {i} {j} m≤n i≤j = begin
  m + i ≤⟨ +-monoˡ-≤ i m≤n ⟩
  n + i ≤⟨ +-monoʳ-≤ n i≤j ⟩
  n + j ∎
  where open ≤-Reasoning

i≤j⇒i≤k+j : ∀ k .{{_ : NonNegative k}} → i ≤ j → i ≤ k + j
i≤j⇒i≤k+j (+ n) i≤j = subst (_≤ _) (+-identityˡ _) (+-mono-≤ (+≤+ z≤n) i≤j)

i≤j+i : ∀ i j .{{_ : NonNegative j}} → i ≤ j + i
i≤j+i i j = i≤j⇒i≤k+j j ≤-refl

i≤i+j : ∀ i j .{{_ : NonNegative j}} → i ≤ i + j
i≤i+j i j rewrite +-comm i j = i≤j+i i j

------------------------------------------------------------------------
-- Properties of _+_ and _<_

+-monoʳ-< : ∀ i → (_+_ i) Preserves _<_ ⟶ _<_
+-monoʳ-< (+ n)    {_} {_}   (-<- o<m) = ⊖-monoʳ->-< n (s<s o<m)
+-monoʳ-< (+ n)    {_} {_}   -<+       = <-≤-trans (m⊖1+n<m n _) (+≤+ (ℕ.m≤m+n n _))
+-monoʳ-< (+ n)    {_} {_}   (+<+ m<o) = +<+ (ℕ.+-monoʳ-< n m<o)
+-monoʳ-< -[1+ n ] {_} {_}   (-<- o<m) = -<- (ℕ.+-monoʳ-< (suc n) o<m)
+-monoʳ-< -[1+ n ] {_} {+ o} -<+       = <-≤-trans (-<- (ℕ.m≤m+n (suc n) _)) (-[1+m]≤n⊖m+1 n o)
+-monoʳ-< -[1+ n ] {_} {_}   (+<+ m<o) = ⊖-monoˡ-< (suc n) m<o

+-monoˡ-< : ∀ i → (_+ i) Preserves _<_ ⟶ _<_
+-monoˡ-< i {j} {k} rewrite +-comm j i | +-comm k i = +-monoʳ-< i

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< {i} {j} {k} {l} i<j k<l = begin-strict
  i + k <⟨ +-monoˡ-< k i<j ⟩
  j + k <⟨ +-monoʳ-< j k<l ⟩
  j + l ∎
  where open ≤-Reasoning

+-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {i} {j} {k} i≤j j<k = ≤-<-trans (+-monoˡ-≤ k i≤j) (+-monoʳ-< j j<k)

+-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {i} {j} {k} i<j j≤k = <-≤-trans (+-monoˡ-< k i<j) (+-monoʳ-≤ j j≤k)

------------------------------------------------------------------------
-- Properties of _-_
------------------------------------------------------------------------

neg-minus-pos : ∀ m n → -[1+ m ] - (+ n) ≡ -[1+ (n ℕ.+ m) ]
neg-minus-pos m       zero    = refl
neg-minus-pos zero    (suc n) = cong (-[1+_] ∘ suc) (sym (ℕ.+-identityʳ n))
neg-minus-pos (suc m) (suc n) = cong (-[1+_] ∘ suc) (ℕ.+-comm (suc m) n)

+-minus-telescope : ∀ i j k → (i - j) + (j - k) ≡ i - k
+-minus-telescope i j k = begin
  (i - j) + (j - k)   ≡⟨  +-assoc i (- j) (j - k) ⟩
  i + (- j + (j - k)) ≡˘⟨ cong (λ v → i + v) (+-assoc (- j) j _) ⟩
  i + ((- j + j) - k) ≡˘⟨ +-assoc i (- j + j) (- k) ⟩
  i + (- j + j) - k   ≡⟨  cong (λ a → i + a - k) (+-inverseˡ j) ⟩
  i + 0ℤ - k          ≡⟨  cong (_- k) (+-identityʳ i) ⟩
  i - k               ∎ where open ≡-Reasoning

[+m]-[+n]≡m⊖n : ∀ m n → (+ m) - (+ n) ≡ m ⊖ n
[+m]-[+n]≡m⊖n zero    zero    = refl
[+m]-[+n]≡m⊖n zero    (suc n) = refl
[+m]-[+n]≡m⊖n (suc m) zero    = cong +[1+_] (ℕ.+-identityʳ m)
[+m]-[+n]≡m⊖n (suc m) (suc n) = refl

∣i-j∣≡∣j-i∣ : ∀ i j → ∣ i - j ∣ ≡ ∣ j - i ∣
∣i-j∣≡∣j-i∣ -[1+ m ] -[1+ n ] = ∣m⊖n∣≡∣n⊖m∣ (suc n) (suc m)
∣i-j∣≡∣j-i∣ -[1+ m ] (+ n)    = begin
  ∣ -[1+ m ] - (+ n) ∣  ≡⟨  cong ∣_∣ (neg-minus-pos m n) ⟩
  suc (n ℕ.+ m)         ≡˘⟨ ℕ.+-suc n m ⟩
  n ℕ.+ suc m           ∎ where open ≡-Reasoning
∣i-j∣≡∣j-i∣ (+ m) -[1+ n ] = begin
  m ℕ.+ suc n          ≡⟨  ℕ.+-suc m n ⟩
  suc (m ℕ.+ n)        ≡˘⟨ cong ∣_∣ (neg-minus-pos n m) ⟩
  ∣ -[1+ n ] + - + m ∣ ∎ where open ≡-Reasoning
∣i-j∣≡∣j-i∣ (+ m) (+ n) = begin
  ∣ + m - + n ∣  ≡⟨  cong ∣_∣ ([+m]-[+n]≡m⊖n m n) ⟩
  ∣ m ⊖ n ∣      ≡⟨  ∣m⊖n∣≡∣n⊖m∣ m n ⟩
  ∣ n ⊖ m ∣      ≡˘⟨ cong ∣_∣ ([+m]-[+n]≡m⊖n n m) ⟩
  ∣ + n - + m ∣  ∎ where open ≡-Reasoning

∣-∣-≤ : i ≤ j → + ∣ i - j ∣ ≡ j - i
∣-∣-≤ (-≤- {m} {n} n≤m) = begin
  + ∣ -[1+ m ] + +[1+ n ] ∣ ≡⟨ cong (λ j → + ∣ j ∣) ([1+m]⊖[1+n]≡m⊖n n m) ⟩
  + ∣ n ⊖ m ∣               ≡⟨ cong +_ (∣⊖∣-≤ n≤m) ⟩
  + ( m ∸ n )              ≡⟨ sym (≤-⊖ n≤m) ⟩
  m ⊖ n                    ≡⟨ sym ([1+m]⊖[1+n]≡m⊖n m n) ⟩
  suc m ⊖ suc n            ∎ where open ≡-Reasoning
∣-∣-≤ (-≤+ {m} {zero}) = refl
∣-∣-≤ (-≤+ {m} {suc n}) = begin
  + ∣ -[1+ m ] - + suc n ∣ ≡⟨⟩
  + suc (suc m ℕ.+ n)    ≡⟨ cong (λ n → + suc n) (ℕ.+-comm (suc m) n) ⟩
  + (suc n ℕ.+ suc m)    ≡⟨⟩
  + suc n - -[1+ m ]      ∎ where open ≡-Reasoning
∣-∣-≤ (+≤+ {m} {n} m≤n) = begin
  + ∣ + m - + n ∣ ≡⟨ cong (λ j → + ∣ j ∣) (m-n≡m⊖n m n) ⟩
  + ∣ m ⊖ n ∣     ≡⟨ cong +_ ( ∣⊖∣-≤ m≤n ) ⟩
  + (n ∸ m)      ≡⟨ sym (≤-⊖  m≤n) ⟩
  n ⊖ m          ≡⟨ sym (m-n≡m⊖n n m) ⟩
  + n - + m      ∎ where open ≡-Reasoning

i≡j⇒i-j≡0 : i ≡ j → i - j ≡ 0ℤ
i≡j⇒i-j≡0 {i} refl = +-inverseʳ i

i-j≡0⇒i≡j : ∀ i j → i - j ≡ 0ℤ → i ≡ j
i-j≡0⇒i≡j i j i-j≡0 = begin
  i             ≡˘⟨ +-identityʳ i ⟩
  i + 0ℤ        ≡˘⟨ cong (_+_ i) (+-inverseˡ j) ⟩
  i + (- j + j) ≡˘⟨ +-assoc i (- j) j ⟩
  (i - j) + j   ≡⟨  cong (_+ j) i-j≡0 ⟩
  0ℤ + j        ≡⟨  +-identityˡ j ⟩
  j             ∎ where open ≡-Reasoning

i≤j⇒i-k≤j : ∀ k .{{_ : NonNegative k}} → i ≤ j → i - k ≤ j
i≤j⇒i-k≤j {i}         +0       i≤j rewrite +-identityʳ i = i≤j
i≤j⇒i-k≤j {+ m}       +[1+ n ] i≤j = ≤-trans (m⊖n≤m m (suc n)) i≤j
i≤j⇒i-k≤j { -[1+ m ]} +[1+ n ] i≤j = ≤-trans (-≤- (ℕ.≤-trans (ℕ.m≤m+n m n) (ℕ.n≤1+n _))) i≤j

i-j≤i : ∀ i j .{{_ : NonNegative j}} → i - j ≤ i
i-j≤i i j = i≤j⇒i-k≤j j ≤-refl

i≤j⇒i-j≤0 : i ≤ j → i - j ≤ 0ℤ
i≤j⇒i-j≤0 {_}         {j}         -≤+       = i≤j⇒i-k≤j j -≤+
i≤j⇒i-j≤0 { -[1+ m ]} { -[1+ n ]} (-≤- n≤m) = begin
  suc n ⊖ suc m ≡⟨ [1+m]⊖[1+n]≡m⊖n n m ⟩
  n ⊖ m         ≤⟨ ⊖-monoʳ-≥-≤ n n≤m ⟩
  n ⊖ n         ≡⟨ n⊖n≡0 n ⟩
  0ℤ            ∎ where open ≤-Reasoning
i≤j⇒i-j≤0 {_}        {+0}       (+≤+ z≤n) = +≤+ z≤n
i≤j⇒i-j≤0 {_}        {+[1+ n ]} (+≤+ z≤n) = -≤+
i≤j⇒i-j≤0 {+[1+ m ]} {+[1+ n ]} (+≤+ (s≤s m≤n)) = begin
  suc m ⊖ suc n ≡⟨ [1+m]⊖[1+n]≡m⊖n m n ⟩
  m ⊖ n         ≤⟨ ⊖-monoʳ-≥-≤ m m≤n ⟩
  m ⊖ m         ≡⟨ n⊖n≡0 m ⟩
  0ℤ            ∎ where open ≤-Reasoning

i-j≤0⇒i≤j : i - j ≤ 0ℤ → i ≤ j
i-j≤0⇒i≤j {i} {j} i-j≤0 = begin
  i             ≡˘⟨ +-identityʳ i ⟩
  i + 0ℤ        ≡˘⟨ cong (_+_ i) (+-inverseˡ j) ⟩
  i + (- j + j) ≡˘⟨ +-assoc i (- j) j ⟩
  (i - j) + j   ≤⟨  +-monoˡ-≤ j i-j≤0 ⟩
  0ℤ + j        ≡⟨  +-identityˡ j ⟩
  j             ∎
  where open ≤-Reasoning

i≤j⇒0≤j-i : i ≤ j → 0ℤ ≤ j - i
i≤j⇒0≤j-i {i} {j} i≤j = begin
  0ℤ    ≡˘⟨ +-inverseʳ i ⟩
  i - i ≤⟨  +-monoˡ-≤ (- i) i≤j ⟩
  j - i ∎
  where open ≤-Reasoning

0≤i-j⇒j≤i : 0ℤ ≤ i - j → j ≤ i
0≤i-j⇒j≤i {i} {j} 0≤i-j = begin
  j             ≡˘⟨ +-identityˡ j ⟩
  0ℤ + j        ≤⟨  +-monoˡ-≤ j 0≤i-j ⟩
  i - j + j     ≡⟨  +-assoc i (- j) j ⟩
  i + (- j + j) ≡⟨  cong (_+_ i) (+-inverseˡ j) ⟩
  i + 0ℤ        ≡⟨  +-identityʳ i ⟩
  i             ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of suc
------------------------------------------------------------------------

i≤j⇒i≤1+j : i ≤ j → i ≤ sucℤ j
i≤j⇒i≤1+j = i≤j⇒i≤k+j (+ 1)

i≤suc[i] : ∀ i → i ≤ sucℤ i
i≤suc[i] i = i≤j+i i (+ 1)

suc-+ : ∀ m n → +[1+ m ] + n ≡ sucℤ (+ m + n)
suc-+ m (+ n)      = refl
suc-+ m (-[1+ n ]) = sym (distribʳ-⊖-+-pos 1 m (suc n))

i≢suc[i] : i ≢ sucℤ i
i≢suc[i] {+ _}           ()
i≢suc[i] { -[1+ 0 ]}     ()
i≢suc[i] { -[1+ suc n ]} ()

1-[1+n]≡-n : ∀ n → sucℤ -[1+ n ] ≡ - (+ n)
1-[1+n]≡-n zero    = refl
1-[1+n]≡-n (suc n) = refl

suc-mono : sucℤ Preserves _≤_ ⟶ _≤_
suc-mono (-≤+ {m} {n}) = begin
  1 ⊖ suc m  ≡⟨ [1+m]⊖[1+n]≡m⊖n 0 m ⟩
  0 ⊖ m      ≤⟨ 0⊖m≤+ m ⟩
  sucℤ (+ n) ∎ where open ≤-Reasoning
suc-mono (-≤- n≤m) = ⊖-monoʳ-≥-≤ 1 (s≤s n≤m)
suc-mono (+≤+ m≤n) = +≤+ (s≤s m≤n)

suc[i]≤j⇒i<j : sucℤ i ≤ j → i < j
suc[i]≤j⇒i<j {+ i}           {+ _}       (+≤+ i≤j) = +<+ i≤j
suc[i]≤j⇒i<j { -[1+ 0 ]}     {+ j}       p         = -<+
suc[i]≤j⇒i<j { -[1+ suc i ]} {+ j}       -≤+       = -<+
suc[i]≤j⇒i<j { -[1+ suc i ]} { -[1+ j ]} (-≤- j≤i) = -<- (ℕ.s≤s j≤i)

i<j⇒suc[i]≤j : i < j → sucℤ i ≤ j
i<j⇒suc[i]≤j {+ _}           {+ _}       (+<+ i<j) = +≤+ i<j
i<j⇒suc[i]≤j { -[1+ 0 ]}     {+ _}       -<+       = +≤+ z≤n
i<j⇒suc[i]≤j { -[1+ suc i ]} { -[1+ _ ]} (-<- j<i) = -≤- (ℕ.≤-pred j<i)
i<j⇒suc[i]≤j { -[1+ suc i ]} {+ _}       -<+       = -≤+

------------------------------------------------------------------------
-- Properties of pred
------------------------------------------------------------------------

suc-pred : ∀ i → sucℤ (pred i) ≡ i
suc-pred i = begin
  sucℤ (pred i) ≡˘⟨ +-assoc 1ℤ -1ℤ i ⟩
  0ℤ + i        ≡⟨  +-identityˡ i ⟩
  i             ∎ where open ≡-Reasoning

pred-suc : ∀ i → pred (sucℤ i) ≡ i
pred-suc i = begin
  pred (sucℤ i) ≡˘⟨ +-assoc -1ℤ 1ℤ i ⟩
  0ℤ + i        ≡⟨  +-identityˡ i ⟩
  i             ∎ where open ≡-Reasoning

+-pred : ∀ i j → i + pred j ≡ pred (i + j)
+-pred i j = begin
  i + (-1ℤ + j) ≡˘⟨ +-assoc i -1ℤ j ⟩
  i + -1ℤ + j   ≡⟨  cong (_+ j) (+-comm i -1ℤ) ⟩
  -1ℤ + i + j   ≡⟨  +-assoc -1ℤ i j ⟩
  -1ℤ + (i + j) ∎ where open ≡-Reasoning

pred-+ : ∀ i j → pred i + j ≡ pred (i + j)
pred-+ i j = begin
  pred i + j   ≡⟨ +-comm (pred i) j ⟩
  j + pred i   ≡⟨ +-pred j i ⟩
  pred (j + i) ≡⟨ cong pred (+-comm j i) ⟩
  pred (i + j) ∎ where open ≡-Reasoning

neg-suc : ∀ m → -[1+ m ] ≡ pred (- + m)
neg-suc zero    = refl
neg-suc (suc m) = refl

minus-suc : ∀ m n → m - +[1+ n ] ≡ pred (m - + n)
minus-suc m n = begin
  m + - +[1+ n ]     ≡⟨ cong (_+_ m) (neg-suc n) ⟩
  m + pred (- (+ n)) ≡⟨ +-pred m (- + n) ⟩
  pred (m - + n)     ∎ where open ≡-Reasoning

i≤pred[j]⇒i<j : i ≤ pred j → i < j
i≤pred[j]⇒i<j {_} { + n}      leq = ≤-<-trans leq (m⊖1+n<m n 1)
i≤pred[j]⇒i<j {_} { -[1+ n ]} leq = ≤-<-trans leq (-<- ℕ.≤-refl)

i<j⇒i≤pred[j] : i < j → i ≤ pred j
i<j⇒i≤pred[j] {_} { +0}       -<+       = -≤- z≤n
i<j⇒i≤pred[j] {_} { +[1+ n ]} -<+       = -≤+
i<j⇒i≤pred[j] {_} { +[1+ n ]} (+<+ m<n) = +≤+ (ℕ.≤-pred m<n)
i<j⇒i≤pred[j] {_} { -[1+ n ]} (-<- n<m) = -≤- n<m

i≤j⇒pred[i]≤j : i ≤ j → pred i ≤ j
i≤j⇒pred[i]≤j -≤+               = -≤+
i≤j⇒pred[i]≤j (-≤- n≤m)         = -≤- (ℕ.m≤n⇒m≤1+n n≤m)
i≤j⇒pred[i]≤j (+≤+ z≤n)         = -≤+
i≤j⇒pred[i]≤j (+≤+ (s≤s m≤n)) = +≤+ (ℕ.m≤n⇒m≤1+n m≤n)

pred-mono : pred Preserves _≤_ ⟶ _≤_
pred-mono (-≤+ {n = 0})     = -≤- z≤n
pred-mono (-≤+ {n = suc n}) = -≤+
pred-mono (-≤- n≤m)         = -≤- (s≤s n≤m)
pred-mono (+≤+ m≤n)         = ⊖-monoˡ-≤ 1 m≤n

------------------------------------------------------------------------
-- Properties of _*_
------------------------------------------------------------------------
-- Algebraic properties

*-comm : Commutative _*_
*-comm -[1+ m ] -[1+ n ] rewrite ℕ.*-comm (suc m) (suc n) = refl
*-comm -[1+ m ] (+ n)    rewrite ℕ.*-comm (suc m) n       = refl
*-comm (+ m)    -[1+ n ] rewrite ℕ.*-comm m       (suc n) = refl
*-comm (+ m)    (+ n)    rewrite ℕ.*-comm m       n       = refl

*-identityˡ : LeftIdentity 1ℤ _*_
*-identityˡ -[1+ n ] rewrite ℕ.+-identityʳ n = refl
*-identityˡ +0       = refl
*-identityˡ +[1+ n ] rewrite ℕ.+-identityʳ n = refl

*-identityʳ : RightIdentity 1ℤ _*_
*-identityʳ = comm+idˡ⇒idʳ *-comm *-identityˡ

*-identity : Identity 1ℤ _*_
*-identity = *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero 0ℤ _*_
*-zeroˡ _ = refl

*-zeroʳ : RightZero 0ℤ _*_
*-zeroʳ = comm+zeˡ⇒zeʳ *-comm *-zeroˡ

*-zero : Zero 0ℤ _*_
*-zero = *-zeroˡ , *-zeroʳ

private
  lemma : ∀ m n o → o ℕ.+ (n ℕ.+ m ℕ.* suc n) ℕ.* suc o
                  ≡ o ℕ.+ n ℕ.* suc o ℕ.+ m ℕ.* suc (o ℕ.+ n ℕ.* suc o)
  lemma =
    solve 3 (λ m n o → o :+ (n :+ m :* (con 1 :+ n)) :* (con 1 :+ o)
                    := o :+ n :* (con 1 :+ o) :+
                       m :* (con 1 :+ (o :+ n :* (con 1 :+ o))))
            refl

*-assoc : Associative _*_
*-assoc +0 _ _ = refl
*-assoc i +0 _ rewrite ℕ.*-zeroʳ ∣ i ∣ = refl
*-assoc i j +0 rewrite
    ℕ.*-zeroʳ ∣ j ∣
  | ℕ.*-zeroʳ ∣ i ∣
  | ℕ.*-zeroʳ ∣ sign i 𝕊* sign j ◃ ∣ i ∣ ℕ.* ∣ j ∣ ∣
  = refl
*-assoc -[1+ m ] -[1+ n ] +[1+ o ] = cong (+_ ∘ suc) (lemma m n o)
*-assoc -[1+ m ] +[1+ n ] -[1+ o ] = cong (+_ ∘ suc) (lemma m n o)
*-assoc +[1+ m ] +[1+ n ] +[1+ o ] = cong (+_ ∘ suc) (lemma m n o)
*-assoc +[1+ m ] -[1+ n ] -[1+ o ] = cong (+_ ∘ suc) (lemma m n o)
*-assoc -[1+ m ] -[1+ n ] -[1+ o ] = cong -[1+_] (lemma m n o)
*-assoc -[1+ m ] +[1+ n ] +[1+ o ] = cong -[1+_] (lemma m n o)
*-assoc +[1+ m ] -[1+ n ] +[1+ o ] = cong -[1+_] (lemma m n o)
*-assoc +[1+ m ] +[1+ n ] -[1+ o ] = cong -[1+_] (lemma m n o)

private

  -- lemma used to prove distributivity.
  distrib-lemma : ∀ m n o → (o ⊖ n) * -[1+ m ] ≡ m ℕ.+ n ℕ.* suc m ⊖ (m ℕ.+ o ℕ.* suc m)
  distrib-lemma m n o
    rewrite +-cancelˡ-⊖ m (n ℕ.* suc m) (o ℕ.* suc m)
          | ⊖-swap (n ℕ.* suc m) (o ℕ.* suc m)
    with n ℕ.≤? o
  ... | yes n≤o
    rewrite ⊖-≥ n≤o
          | ⊖-≥ (ℕ.*-mono-≤ n≤o (ℕ.≤-refl {x = suc m}))
          | -◃n≡-n ((o ∸ n) ℕ.* suc m)
          | ℕ.*-distribʳ-∸ (suc m) o n
          = refl
  ... | no n≰o
    rewrite sign-⊖-≰ n≰o
          | ∣⊖∣-≰ n≰o
          | +◃n≡+n ((n ∸ o) ℕ.* suc m)
          | ⊖-≰ (n≰o ∘ ℕ.*-cancelʳ-≤ n o (suc m))
          | neg-involutive (+ (n ℕ.* suc m ∸ o ℕ.* suc m))
          | ℕ.*-distribʳ-∸ (suc m) n o
          = refl

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ +0 y z
  rewrite ℕ.*-zeroʳ ∣ y ∣
        | ℕ.*-zeroʳ ∣ z ∣
        | ℕ.*-zeroʳ ∣ y + z ∣
        = refl
*-distribʳ-+ x +0 z
  rewrite +-identityˡ z
        | +-identityˡ (sign z 𝕊* sign x ◃ ∣ z ∣ ℕ.* ∣ x ∣)
        = refl
*-distribʳ-+ x y +0
  rewrite +-identityʳ y
        | +-identityʳ (sign y 𝕊* sign x ◃ ∣ y ∣ ℕ.* ∣ x ∣)
        = refl
*-distribʳ-+ -[1+ m ] -[1+ n ] -[1+ o ] = cong (+_) $
  solve 3 (λ m n o → (con 2 :+ n :+ o) :* (con 1 :+ m)
                  := (con 1 :+ n) :* (con 1 :+ m) :+
                     (con 1 :+ o) :* (con 1 :+ m))
          refl m n o
*-distribʳ-+ +[1+ m ] +[1+ n ] +[1+ o ] = cong (+_) $
  solve 3 (λ m n o → (con 1 :+ n :+ (con 1 :+ o)) :* (con 1 :+ m)
                  := (con 1 :+ n) :* (con 1 :+ m) :+
                     (con 1 :+ o) :* (con 1 :+ m))
        refl m n o
*-distribʳ-+ -[1+ m ] +[1+ n ] +[1+ o ] = cong -[1+_] $
  solve 3 (λ m n o → m :+ (n :+ (con 1 :+ o)) :* (con 1 :+ m)
                   := (con 1 :+ n) :* (con 1 :+ m) :+
                      (m :+ o :* (con 1 :+ m)))
         refl m n o
*-distribʳ-+ +[1+ m ] -[1+ n ] -[1+ o ] = cong -[1+_] $
  solve 3 (λ m n o → m :+ (con 1 :+ m :+ (n :+ o) :* (con 1 :+ m))
                  := (con 1 :+ n) :* (con 1 :+ m) :+
                     (m :+ o :* (con 1 :+ m)))
         refl m n o
*-distribʳ-+ -[1+ m ] -[1+ n ] +[1+ o ] = begin
  (suc o ⊖ suc n) * -[1+ m ]                ≡⟨ cong (_* -[1+ m ]) ([1+m]⊖[1+n]≡m⊖n o n) ⟩
  (o ⊖ n) * -[1+ m ]                        ≡⟨ distrib-lemma m n o ⟩
  m ℕ.+ n ℕ.* suc m ⊖ (m ℕ.+ o ℕ.* suc m)   ≡˘⟨ [1+m]⊖[1+n]≡m⊖n (m ℕ.+ n ℕ.* suc m) (m ℕ.+ o ℕ.* suc m) ⟩
  -[1+ n ] * -[1+ m ] + +[1+ o ] * -[1+ m ] ∎ where open ≡-Reasoning
*-distribʳ-+ -[1+ m ] +[1+ n ] -[1+ o ] = begin
  (+[1+ n ] + -[1+ o ]) * -[1+ m ]          ≡⟨ cong (_* -[1+ m ]) ([1+m]⊖[1+n]≡m⊖n n o) ⟩
  (n ⊖ o) * -[1+ m ]                        ≡⟨ distrib-lemma m o n ⟩
  m ℕ.+ o ℕ.* suc m ⊖ (m ℕ.+ n ℕ.* suc m)   ≡˘⟨ [1+m]⊖[1+n]≡m⊖n (m ℕ.+ o ℕ.* suc m) (m ℕ.+ n ℕ.* suc m) ⟩
  +[1+ n ] * -[1+ m ] + -[1+ o ] * -[1+ m ] ∎ where open ≡-Reasoning
*-distribʳ-+ +[1+ m ] -[1+ n ] +[1+ o ] with n ℕ.≤? o
... | yes n≤o
  rewrite [1+m]⊖[1+n]≡m⊖n o n
        | [1+m]⊖[1+n]≡m⊖n (m ℕ.+ o ℕ.* suc m) (m ℕ.+ n ℕ.* suc m)
        | +-cancelˡ-⊖ m (o ℕ.* suc m) (n ℕ.* suc m)
        | ⊖-≥ n≤o
        | +-comm (- (+ (m ℕ.+ n ℕ.* suc m))) (+ (m ℕ.+ o ℕ.* suc m))
        | ⊖-≥ (ℕ.*-mono-≤ n≤o (ℕ.≤-refl {x = suc m}))
        | ℕ.*-distribʳ-∸ (suc m) o n
        | +◃n≡+n (o ℕ.* suc m ∸ n ℕ.* suc m)
        = refl
... | no n≰o
  rewrite [1+m]⊖[1+n]≡m⊖n o n
        | [1+m]⊖[1+n]≡m⊖n (m ℕ.+ o ℕ.* suc m) (m ℕ.+ n ℕ.* suc m)
        | +-cancelˡ-⊖ m (o ℕ.* suc m) (n ℕ.* suc m)
        | sign-⊖-≰ n≰o
        | ∣⊖∣-≰ n≰o
        | -◃n≡-n ((n ∸ o) ℕ.* suc m)
        | ⊖-≰ (n≰o ∘ ℕ.*-cancelʳ-≤ n o (suc m))
        | ℕ.*-distribʳ-∸ (suc m) n o
        = refl
*-distribʳ-+ +[1+ o ] +[1+ m ] -[1+ n ] with n ℕ.≤? m
... | yes n≤m
  rewrite [1+m]⊖[1+n]≡m⊖n m n
        | [1+m]⊖[1+n]≡m⊖n (o ℕ.+ m ℕ.* suc o) (o ℕ.+ n ℕ.* suc o)
        | +-cancelˡ-⊖ o (m ℕ.* suc o) (n ℕ.* suc o)
        | ⊖-≥ n≤m
        | ⊖-≥ (ℕ.*-mono-≤ n≤m (ℕ.≤-refl {x = suc o}))
        | +◃n≡+n ((m ∸ n) ℕ.* suc o)
        | ℕ.*-distribʳ-∸ (suc o) m n
        = refl
... | no n≰m
  rewrite [1+m]⊖[1+n]≡m⊖n m n
        | [1+m]⊖[1+n]≡m⊖n (o ℕ.+ m ℕ.* suc o) (o ℕ.+ n ℕ.* suc o)
        | +-cancelˡ-⊖ o (m ℕ.* suc o) (n ℕ.* suc o)
        | sign-⊖-≰ n≰m
        | ∣⊖∣-≰ n≰m
        | ⊖-≰ (n≰m ∘ ℕ.*-cancelʳ-≤ n m (suc o))
        | -◃n≡-n ((n ∸ m) ℕ.* suc o)
        | ℕ.*-distribʳ-∸ (suc o) n m
        = refl

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ = comm+distrʳ⇒distrˡ *-comm *-distribʳ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

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

*-1-isMonoid : IsMonoid _*_ 1ℤ
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1ℤ
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = *-comm
  }

+-*-isSemiring : IsSemiring _+_ _*_ 0ℤ 1ℤ
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-0-isCommutativeMonoid
    ; *-cong = cong₂ _*_
    ; *-assoc = *-assoc
    ; *-identity = *-identity
    ; distrib = *-distrib-+
    }
  ; zero = *-zero
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ 0ℤ 1ℤ
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm = *-comm
  }

+-*-isRing : IsRing _+_ _*_ -_ 0ℤ 1ℤ
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-cong           = cong₂ _*_
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  ; zero             = *-zero
  }

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0ℤ 1ℤ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
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

+-*-ring : Ring 0ℓ 0ℓ
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }

------------------------------------------------------------------------
-- Other properties of _*_ and _≡_

abs-* : ℤtoℕ.Homomorphic₂ ∣_∣ _*_ ℕ._*_
abs-* i j = abs-◃ _ _

*-cancelʳ-≡ : ∀ i j k .{{_ : NonZero k}} → i * k ≡ j * k → i ≡ j
*-cancelʳ-≡ i j k eq with sign-cong′ eq
... | inj₁ s[ik]≡s[jk] = ◃-cong
  (𝕊ₚ.*-cancelʳ-≡ (sign k) (sign i) (sign j) s[ik]≡s[jk])
  (ℕ.*-cancelʳ-≡ ∣ i ∣ ∣ j ∣ _ (abs-cong eq))
... | inj₂ (∣ik∣≡0 , ∣jk∣≡0) = trans
  (∣i∣≡0⇒i≡0 (ℕ.m*n≡0⇒m≡0 _ _ ∣ik∣≡0))
  (sym (∣i∣≡0⇒i≡0 (ℕ.m*n≡0⇒m≡0 _ _ ∣jk∣≡0)))

*-cancelˡ-≡ : ∀ i j k .{{_ : NonZero i}} → i * j ≡ i * k → j ≡ k
*-cancelˡ-≡ i j k rewrite *-comm i j | *-comm i k = *-cancelʳ-≡ j k i

suc-* : ∀ i j → sucℤ i * j ≡ j + i * j
suc-* i j = begin
  sucℤ i * j      ≡⟨ *-distribʳ-+ j (+ 1) i ⟩
  + 1 * j + i * j ≡⟨ cong (_+ i * j) (*-identityˡ j) ⟩
  j + i * j       ∎
  where open ≡-Reasoning

*-suc : ∀ i j → i * sucℤ j ≡ i + i * j
*-suc i j = begin
  i * sucℤ j ≡⟨ *-comm i _ ⟩
  sucℤ j * i ≡⟨ suc-* j i ⟩
  i + j * i  ≡⟨ cong (λ v → i + v) (*-comm j i) ⟩
  i + i * j  ∎
  where open ≡-Reasoning

-1*i≡-i : ∀ i → -1ℤ * i ≡ - i
-1*i≡-i -[1+ n ] = cong +[1+_] (ℕ.+-identityʳ n)
-1*i≡-i +0       = refl
-1*i≡-i +[1+ n ] = cong -[1+_] (ℕ.+-identityʳ n)

i*j≡0⇒i≡0∨j≡0 : ∀ i {j} → i * j ≡ 0ℤ → i ≡ 0ℤ ⊎ j ≡ 0ℤ
i*j≡0⇒i≡0∨j≡0 i p with ℕ.m*n≡0⇒m≡0∨n≡0 ∣ i ∣ (abs-cong {t = Sign.+} p)
... | inj₁ ∣i∣≡0 = inj₁ (∣i∣≡0⇒i≡0 ∣i∣≡0)
... | inj₂ ∣j∣≡0 = inj₂ (∣i∣≡0⇒i≡0 ∣j∣≡0)

------------------------------------------------------------------------
-- Properties of _^_
------------------------------------------------------------------------

^-identityʳ : ∀ i → i ^ 1 ≡ i
^-identityʳ =  *-identityʳ

^-zeroˡ : ∀ n → 1ℤ ^ n ≡ 1ℤ
^-zeroˡ zero  = refl
^-zeroˡ (suc n) = begin
  1ℤ ^ suc n    ≡⟨⟩
  1ℤ * (1ℤ ^ n) ≡⟨ *-identityˡ (1ℤ ^ n) ⟩
  1ℤ ^ n        ≡⟨ ^-zeroˡ n ⟩
  1ℤ            ∎
  where open ≡-Reasoning

^-distribˡ-+-* : ∀ i m n → i ^ (m ℕ.+ n) ≡ i ^ m * i ^ n
^-distribˡ-+-* i zero    n = sym (*-identityˡ (i ^ n))
^-distribˡ-+-* i (suc m) n = begin
  i * (i ^ (m ℕ.+ n))     ≡⟨ cong (i *_) (^-distribˡ-+-* i m n) ⟩
  i * ((i ^ m) * (i ^ n)) ≡⟨ sym (*-assoc i _ _) ⟩
  (i * (i ^ m)) * (i ^ n) ∎
  where open ≡-Reasoning

^-isMagmaHomomorphism : ∀ i → Morphism.IsMagmaHomomorphism ℕ.+-rawMagma *-rawMagma (i ^_)
^-isMagmaHomomorphism i = record
  { isRelHomomorphism = record { cong = cong (i ^_) }
  ; homo              = ^-distribˡ-+-* i
  }

^-isMonoidHomomorphism : ∀ i → Morphism.IsMonoidHomomorphism ℕ.+-0-rawMonoid *-1-rawMonoid (i ^_)
^-isMonoidHomomorphism i = record
  { isMagmaHomomorphism = ^-isMagmaHomomorphism i
  ; ε-homo              = refl
  }

^-*-assoc : ∀ i m n → (i ^ m) ^ n ≡ i ^ (m ℕ.* n)
^-*-assoc i m zero    = cong (i ^_) (sym $ ℕ.*-zeroʳ m)
^-*-assoc i m (suc n) = begin
  (i ^ m) * ((i ^ m) ^ n)   ≡⟨ cong ((i ^ m) *_) (^-*-assoc i m n) ⟩
  (i ^ m) * (i ^ (m ℕ.* n)) ≡⟨ sym (^-distribˡ-+-* i m (m ℕ.* n)) ⟩
  i ^ (m ℕ.+ m ℕ.* n)       ≡⟨ cong (i ^_) (sym (ℕ.*-suc m n)) ⟩
  i ^ (m ℕ.* suc n)         ∎
  where open ≡-Reasoning

i^n≡0⇒i≡0 : ∀ i n → i ^ n ≡ 0ℤ → i ≡ 0ℤ
i^n≡0⇒i≡0 i (suc n) eq = [ id , i^n≡0⇒i≡0 i n ]′ (i*j≡0⇒i≡0∨j≡0 i eq)

------------------------------------------------------------------------
-- Properties of _*_ and +_/-_

pos-* : ℕtoℤ.Homomorphic₂ +_ ℕ._*_ _*_
pos-* zero    n       = refl
pos-* (suc m) zero    = pos-* m zero
pos-* (suc m) (suc n) = refl

neg-distribˡ-* : ∀ i j → - (i * j) ≡ (- i) * j
neg-distribˡ-* i j = begin
  - (i * j)      ≡˘⟨ -1*i≡-i (i * j) ⟩
  -1ℤ * (i * j)  ≡˘⟨ *-assoc -1ℤ i j ⟩
  -1ℤ * i * j    ≡⟨ cong (_* j) (-1*i≡-i i) ⟩
  - i * j        ∎ where open ≡-Reasoning

neg-distribʳ-* : ∀ i j → - (i * j) ≡ i * (- j)
neg-distribʳ-* i j = begin
  - (i * j) ≡⟨ cong -_ (*-comm i j) ⟩
  - (j * i) ≡⟨ neg-distribˡ-* j i ⟩
  - j * i   ≡⟨ *-comm (- j) i ⟩
  i * (- j) ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of _*_ and _◃_

◃-distrib-* :  ∀ s t m n → (s 𝕊* t) ◃ (m ℕ.* n) ≡ (s ◃ m) * (t ◃ n)
◃-distrib-* s t zero    zero    = refl
◃-distrib-* s t zero    (suc n) = refl
◃-distrib-* s t (suc m) zero    =
  trans
    (cong₂ _◃_ (𝕊ₚ.*-comm s t) (ℕ.*-comm m 0))
    (*-comm (t ◃ zero) (s ◃ suc m))
◃-distrib-* s t (suc m) (suc n) =
  sym (cong₂ _◃_
    (cong₂ _𝕊*_ (sign-◃ s (suc m)) (sign-◃ t (suc n)))
    (∣s◃m∣*∣t◃n∣≡m*n s t (suc m) (suc n)))

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

*-cancelʳ-≤-pos : ∀ i j k .{{_ : Positive k}} → i * k ≤ j * k → i ≤ j
*-cancelʳ-≤-pos -[1+ m ] -[1+ n ] +[1+ o ] (-≤- n≤m) =
  -≤- (ℕ.≤-pred (ℕ.*-cancelʳ-≤ (suc n) (suc m) (suc o) (s≤s n≤m)))
*-cancelʳ-≤-pos -[1+ _ ] (+ _)    +[1+ o ] _         = -≤+
*-cancelʳ-≤-pos +0       +0       +[1+ o ] _         = +≤+ z≤n
*-cancelʳ-≤-pos +0       +[1+ _ ] +[1+ o ] _         = +≤+ z≤n
*-cancelʳ-≤-pos +[1+ _ ] +0       +[1+ o ] (+≤+ ())
*-cancelʳ-≤-pos +[1+ m ] +[1+ n ] +[1+ o ] (+≤+ m≤n) =
  +≤+ (ℕ.*-cancelʳ-≤ (suc m) (suc n) (suc o) m≤n)

*-cancelˡ-≤-pos : ∀ i j k .{{_ : Positive k}} → k * i ≤ k * j → i ≤ j
*-cancelˡ-≤-pos i j k rewrite *-comm k i | *-comm k j = *-cancelʳ-≤-pos i j k

*-monoʳ-≤-nonNeg : ∀ i .{{_ : NonNegative i}} → (_* i) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-nonNeg +0 {i} {j} i≤j rewrite *-zeroʳ i | *-zeroʳ j = +≤+ z≤n
*-monoʳ-≤-nonNeg +[1+ n ] (-≤+ {n = 0})         = -≤+
*-monoʳ-≤-nonNeg +[1+ n ] (-≤+ {n = suc _})     = -≤+
*-monoʳ-≤-nonNeg +[1+ n ] (-≤- n≤m) = -≤- (ℕ.≤-pred (ℕ.*-mono-≤ (s≤s n≤m) (ℕ.≤-refl {x = suc n})))
*-monoʳ-≤-nonNeg +[1+ n ] {+0}       {+0}       (+≤+ m≤n) = +≤+ m≤n
*-monoʳ-≤-nonNeg +[1+ n ] {+0}       {+[1+ _ ]} (+≤+ m≤n) = +≤+ z≤n
*-monoʳ-≤-nonNeg +[1+ n ] {+[1+ _ ]} {+[1+ _ ]} (+≤+ m≤n) = +≤+ (ℕ.*-monoˡ-≤ (suc n) m≤n)

*-monoˡ-≤-nonNeg : ∀ i .{{_ : NonNegative i}} → (i *_) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-nonNeg i {j} {k} rewrite *-comm i j | *-comm i k = *-monoʳ-≤-nonNeg i

*-cancelˡ-≤-neg : ∀ i j k .{{_ : Negative i}} → i * j ≤ i * k → j ≥ k
*-cancelˡ-≤-neg i@(-[1+ _ ]) j k ij≤ik = neg-cancel-≤ (*-cancelˡ-≤-pos (- j) (- k) (- i) (begin
  - i * - j   ≡˘⟨ neg-distribʳ-* (- i) j ⟩
  -(- i * j)  ≡⟨  neg-distribˡ-* (- i) j ⟩
  i * j       ≤⟨  ij≤ik ⟩
  i * k       ≡˘⟨ neg-distribˡ-* (- i) k ⟩
  -(- i * k)  ≡⟨  neg-distribʳ-* (- i) k ⟩
  - i * - k   ∎))
  where open ≤-Reasoning

*-cancelʳ-≤-neg : ∀ i j k .{{_ : Negative k}} → i * k ≤ j * k → i ≥ j
*-cancelʳ-≤-neg i j k rewrite *-comm i k | *-comm j k = *-cancelˡ-≤-neg k i j

*-monoˡ-≤-nonPos : ∀ i .{{_ : NonPositive i}} → (i *_) Preserves _≤_ ⟶ _≥_
*-monoˡ-≤-nonPos +0           {j} {k} j≤k = +≤+ z≤n
*-monoˡ-≤-nonPos i@(-[1+ m ]) {j} {k} j≤k = begin
  i * k        ≡˘⟨ neg-distribˡ-* (- i) k ⟩
  -(- i * k)   ≡⟨  neg-distribʳ-* (- i) k ⟩
  - i * - k    ≤⟨  *-monoˡ-≤-nonNeg (- i) (neg-mono-≤ j≤k) ⟩
  - i * - j    ≡˘⟨ neg-distribʳ-* (- i) j ⟩
  -(- i * j)   ≡⟨  neg-distribˡ-* (- i) j ⟩
  i * j        ∎
  where open ≤-Reasoning

*-monoʳ-≤-nonPos : ∀ i .{{_ : NonPositive i}} → (_* i) Preserves _≤_ ⟶ _≥_
*-monoʳ-≤-nonPos i {j} {k} rewrite *-comm k i | *-comm j i = *-monoˡ-≤-nonPos i

------------------------------------------------------------------------
-- Properties of _*_ and _<_

*-monoˡ-<-pos : ∀ i .{{_ : Positive i}} → (i *_) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos +[1+ n ] {+ m}       {+ o}       (+<+ m<o) = +◃-mono-< (ℕ.+-mono-<-≤ m<o (ℕ.*-monoʳ-≤ n (ℕ.<⇒≤ m<o)))
*-monoˡ-<-pos +[1+ n ] { -[1+ m ]} {+ o}       leq       = -◃<+◃ _ (suc n ℕ.* o)
*-monoˡ-<-pos +[1+ n ] { -[1+ m ]} { -[1+ o ]} (-<- o<m) = -<- (ℕ.+-mono-<-≤ o<m (ℕ.*-monoʳ-≤ n (ℕ.<⇒≤ (s≤s o<m))))

*-monoʳ-<-pos : ∀ i .{{_ : Positive i}} → (_* i) Preserves _<_ ⟶ _<_
*-monoʳ-<-pos i {j} {k} rewrite *-comm j i | *-comm k i = *-monoˡ-<-pos i

*-cancelˡ-<-nonNeg : ∀ k .{{_ : NonNegative k}} → k * i < k * j → i < j
*-cancelˡ-<-nonNeg {+ i}       {+ j}       (+ n) leq = +<+ (ℕ.*-cancelˡ-< n _ _ (+◃-cancel-< leq))
*-cancelˡ-<-nonNeg {+ i}       { -[1+ j ]} (+ n) leq = contradiction leq +◃≮-◃
*-cancelˡ-<-nonNeg { -[1+ i ]} {+ j}       (+ n)leq = -<+
*-cancelˡ-<-nonNeg { -[1+ i ]} { -[1+ j ]} (+ n) leq = -<- (ℕ.≤-pred (ℕ.*-cancelˡ-< n _ _ (neg◃-cancel-< leq)))

*-cancelʳ-<-nonNeg : ∀ k .{{_ : NonNegative k}} → i * k < j * k → i < j
*-cancelʳ-<-nonNeg {i} {j} k rewrite *-comm i k | *-comm j k = *-cancelˡ-<-nonNeg k

*-monoˡ-<-neg : ∀ i .{{_ : Negative i}} → (i *_) Preserves _<_ ⟶ _>_
*-monoˡ-<-neg i@(-[1+ _ ]) {j} {k} j<k = begin-strict
  i * k        ≡˘⟨ neg-distribˡ-* (- i) k ⟩
  -(- i * k)   ≡⟨  neg-distribʳ-* (- i) k ⟩
  - i * - k    <⟨  *-monoˡ-<-pos (- i) (neg-mono-< j<k) ⟩
  - i * - j    ≡˘⟨ neg-distribʳ-* (- i) j ⟩
  - (- i * j)  ≡⟨  neg-distribˡ-* (- i) j ⟩
  i * j        ∎
  where open ≤-Reasoning

*-monoʳ-<-neg : ∀ i .{{_ : Negative i}} → (_* i) Preserves _<_ ⟶ _>_
*-monoʳ-<-neg i {j} {k} rewrite *-comm k i | *-comm j i = *-monoˡ-<-neg i

*-cancelˡ-<-nonPos : ∀ k .{{_ : NonPositive k}} → k * i < k * j → i > j
*-cancelˡ-<-nonPos {i} {j} +0           (+<+ ())
*-cancelˡ-<-nonPos {i} {j} k@(-[1+ _ ]) ki<kj = neg-cancel-< (*-cancelˡ-<-nonNeg (- k) (begin-strict
  - k * - i   ≡˘⟨ neg-distribʳ-* (- k) i ⟩
  -(- k * i)  ≡⟨  neg-distribˡ-* (- k) i ⟩
  k * i       <⟨  ki<kj ⟩
  k * j       ≡˘⟨ neg-distribˡ-* (- k) j ⟩
  -(- k * j)  ≡⟨  neg-distribʳ-* (- k) j ⟩
  - k * - j   ∎))
  where open ≤-Reasoning

*-cancelʳ-<-nonPos : ∀ k .{{_ : NonPositive k}} → i * k < j * k → i > j
*-cancelʳ-<-nonPos {i} {j} k rewrite *-comm i k | *-comm j k = *-cancelˡ-<-nonPos k

*-cancelˡ-<-neg : ∀ n → -[1+ n ] * i < -[1+ n ] * j → i > j
*-cancelˡ-<-neg {i} {j} n = *-cancelˡ-<-nonPos -[1+ n ]

*-cancelʳ-<-neg : ∀ n → i * -[1+ n ] < j * -[1+ n ] → i > j
*-cancelʳ-<-neg {i} {j} n = *-cancelʳ-<-nonPos -[1+ n ]

------------------------------------------------------------------------
-- Properties of _*_ and ∣_∣

∣i*j∣≡∣i∣*∣j∣ : ∀ i j → ∣ i * j ∣ ≡ ∣ i ∣ ℕ.* ∣ j ∣
∣i*j∣≡∣i∣*∣j∣ i j = abs-◃ (sign i 𝕊* sign j) (∣ i ∣ ℕ.* ∣ j ∣)

------------------------------------------------------------------------
-- Properties of _⊓_ and _⊔_
------------------------------------------------------------------------
-- Basic specification in terms of _≤_

i≤j⇒i⊓j≡i : i ≤ j → i ⊓ j ≡ i
i≤j⇒i⊓j≡i (-≤- i≥j) = cong -[1+_] (ℕ.m≥n⇒m⊔n≡m i≥j)
i≤j⇒i⊓j≡i -≤+       = refl
i≤j⇒i⊓j≡i (+≤+ i≤j) = cong +_ (ℕ.m≤n⇒m⊓n≡m i≤j)

i≥j⇒i⊓j≡j : i ≥ j → i ⊓ j ≡ j
i≥j⇒i⊓j≡j (-≤- i≥j) = cong -[1+_] (ℕ.m≤n⇒m⊔n≡n i≥j)
i≥j⇒i⊓j≡j -≤+       = refl
i≥j⇒i⊓j≡j (+≤+ i≤j) = cong +_ (ℕ.m≥n⇒m⊓n≡n i≤j)

i≤j⇒i⊔j≡j : i ≤ j → i ⊔ j ≡ j
i≤j⇒i⊔j≡j (-≤- i≥j) = cong -[1+_] (ℕ.m≥n⇒m⊓n≡n i≥j)
i≤j⇒i⊔j≡j -≤+       = refl
i≤j⇒i⊔j≡j (+≤+ i≤j) = cong +_ (ℕ.m≤n⇒m⊔n≡n i≤j)

i≥j⇒i⊔j≡i : i ≥ j → i ⊔ j ≡ i
i≥j⇒i⊔j≡i (-≤- i≥j) = cong -[1+_] (ℕ.m≤n⇒m⊓n≡m i≥j)
i≥j⇒i⊔j≡i -≤+       = refl
i≥j⇒i⊔j≡i (+≤+ i≤j) = cong +_ (ℕ.m≥n⇒m⊔n≡m i≤j)

⊓-operator : MinOperator ≤-totalPreorder
⊓-operator = record
  { x≤y⇒x⊓y≈x = i≤j⇒i⊓j≡i
  ; x≥y⇒x⊓y≈y = i≥j⇒i⊓j≡j
  }

⊔-operator : MaxOperator ≤-totalPreorder
⊔-operator = record
  { x≤y⇒x⊔y≈y = i≤j⇒i⊔j≡j
  ; x≥y⇒x⊔y≈x = i≥j⇒i⊔j≡i
  }

------------------------------------------------------------------------
-- Automatically derived properties of _⊓_ and _⊔_

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
  ( x⊓y≈y⇒y≤x to i⊓j≡j⇒j≤i    -- : ∀ {i j} → i ⊓ j ≡ j → j ≤ i
  ; x⊓y≈x⇒x≤y to i⊓j≡i⇒i≤j    -- : ∀ {i j} → i ⊓ j ≡ i → i ≤ j
  ; x⊓y≤x     to i⊓j≤i        -- : ∀ i j → i ⊓ j ≤ i
  ; x⊓y≤y     to i⊓j≤j        -- : ∀ i j → i ⊓ j ≤ j
  ; x≤y⇒x⊓z≤y to i≤j⇒i⊓k≤j    -- : ∀ {i j} k → i ≤ j → i ⊓ k ≤ j
  ; x≤y⇒z⊓x≤y to i≤j⇒k⊓i≤j    -- : ∀ {i j} k → i ≤ j → k ⊓ i ≤ j
  ; x≤y⊓z⇒x≤y to i≤j⊓k⇒i≤j    -- : ∀ {i} j k → i ≤ j ⊓ k → i ≤ j
  ; x≤y⊓z⇒x≤z to i≤j⊓k⇒i≤k    -- : ∀ {i} j k → i ≤ j ⊓ k → i ≤ k

  ; x⊔y≈y⇒x≤y to i⊔j≡j⇒i≤j    -- : ∀ {i j} → i ⊔ j ≡ j → i ≤ j
  ; x⊔y≈x⇒y≤x to i⊔j≡i⇒j≤i    -- : ∀ {i j} → i ⊔ j ≡ i → j ≤ i
  ; x≤x⊔y     to i≤i⊔j        -- : ∀ i j → i ≤ i ⊔ j
  ; x≤y⊔x     to i≤j⊔i        -- : ∀ i j → i ≤ j ⊔ i
  ; x≤y⇒x≤y⊔z to i≤j⇒i≤j⊔k    -- : ∀ {i j} k → i ≤ j → i ≤ j ⊔ k
  ; x≤y⇒x≤z⊔y to i≤j⇒i≤k⊔j    -- : ∀ {i j} k → i ≤ j → i ≤ k ⊔ j
  ; x⊔y≤z⇒x≤z to i⊔j≤k⇒i≤k    -- : ∀ i j {k} → i ⊔ j ≤ k → i ≤ k
  ; x⊔y≤z⇒y≤z to i⊔j≤k⇒j≤k    -- : ∀ i j {k} → i ⊔ j ≤ k → j ≤ k

  ; x⊓y≤x⊔y   to i⊓j≤i⊔j      -- : ∀ i j → i ⊓ j ≤ i ⊔ j
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
-- Other properties of _⊓_ and _⊔_

mono-≤-distrib-⊔ : ∀ {f} → f Preserves _≤_ ⟶ _≤_ →
                   ∀ i j → f (i ⊔ j) ≡ f i ⊔ f j
mono-≤-distrib-⊔ {f} = ⊓-⊔-properties.mono-≤-distrib-⊔ (cong f)

mono-≤-distrib-⊓ : ∀ {f} → f Preserves _≤_ ⟶ _≤_ →
                   ∀ i j → f (i ⊓ j) ≡ f i ⊓ f j
mono-≤-distrib-⊓ {f} = ⊓-⊔-properties.mono-≤-distrib-⊓ (cong f)

antimono-≤-distrib-⊓ : ∀ {f} → f Preserves _≤_ ⟶ _≥_ →
                       ∀ i j → f (i ⊓ j) ≡ f i ⊔ f j
antimono-≤-distrib-⊓ {f} = ⊓-⊔-properties.antimono-≤-distrib-⊓ (cong f)

antimono-≤-distrib-⊔ : ∀ {f} → f Preserves _≤_ ⟶ _≥_ →
                       ∀ i j → f (i ⊔ j) ≡ f i ⊓ f j
antimono-≤-distrib-⊔ {f} = ⊓-⊔-properties.antimono-≤-distrib-⊔ (cong f)

mono-<-distrib-⊓ : ∀ f → f Preserves _<_ ⟶ _<_ → ∀ i j → f (i ⊓ j) ≡ f i ⊓ f j
mono-<-distrib-⊓ f f-mono-< i j with <-cmp i j
... | tri< i<j _    _   = trans (cong f (i≤j⇒i⊓j≡i (<⇒≤ i<j))) (sym (i≤j⇒i⊓j≡i (<⇒≤ (f-mono-< i<j))))
... | tri≈ _   refl _   = trans (cong f (i≤j⇒i⊓j≡i ≤-refl))    (sym (i≤j⇒i⊓j≡i ≤-refl))
... | tri> _   _    i>j = trans (cong f (i≥j⇒i⊓j≡j (<⇒≤ i>j))) (sym (i≥j⇒i⊓j≡j (<⇒≤ (f-mono-< i>j))))

mono-<-distrib-⊔ : ∀ f → f Preserves _<_ ⟶ _<_ → ∀ i j → f (i ⊔ j) ≡ f i ⊔ f j
mono-<-distrib-⊔ f f-mono-< i j with <-cmp i j
... | tri< i<j _    _   = trans (cong f (i≤j⇒i⊔j≡j (<⇒≤ i<j))) (sym (i≤j⇒i⊔j≡j (<⇒≤ (f-mono-< i<j))))
... | tri≈ _   refl _   = trans (cong f (i≤j⇒i⊔j≡j ≤-refl))    (sym (i≤j⇒i⊔j≡j ≤-refl))
... | tri> _   _    i>j = trans (cong f (i≥j⇒i⊔j≡i (<⇒≤ i>j))) (sym (i≥j⇒i⊔j≡i (<⇒≤ (f-mono-< i>j))))

antimono-<-distrib-⊔ : ∀ f  → f Preserves _<_ ⟶ _>_ → ∀ i j → f (i ⊔ j) ≡ f i ⊓ f j
antimono-<-distrib-⊔ f f-mono-< i j with <-cmp i j
... | tri< i<j _    _   = trans (cong f (i≤j⇒i⊔j≡j (<⇒≤ i<j))) (sym (i≥j⇒i⊓j≡j (<⇒≤ (f-mono-< i<j))))
... | tri≈ _   refl _   = trans (cong f (i≤j⇒i⊔j≡j ≤-refl))    (sym (i≥j⇒i⊓j≡j ≤-refl))
... | tri> _   _    i>j = trans (cong f (i≥j⇒i⊔j≡i (<⇒≤ i>j))) (sym (i≤j⇒i⊓j≡i (<⇒≤ (f-mono-< i>j))))

antimono-<-distrib-⊓ : ∀ f → f Preserves _<_ ⟶ _>_ → ∀ i j → f (i ⊓ j) ≡ f i ⊔ f j
antimono-<-distrib-⊓ f f-mono-< i j with <-cmp i j
... | tri< i<j _    _   = trans (cong f (i≤j⇒i⊓j≡i (<⇒≤ i<j))) (sym (i≥j⇒i⊔j≡i (<⇒≤ (f-mono-< i<j))))
... | tri≈ _   refl _   = trans (cong f (i≤j⇒i⊓j≡i ≤-refl))    (sym (i≥j⇒i⊔j≡i ≤-refl))
... | tri> _   _    i>j = trans (cong f (i≥j⇒i⊓j≡j (<⇒≤ i>j))) (sym (i≤j⇒i⊔j≡j (<⇒≤ (f-mono-< i>j))))

------------------------------------------------------------------------
-- Other properties of _⊓_, _⊔_ and -_

neg-distrib-⊔-⊓ : ∀ i j → - (i ⊔ j) ≡ - i ⊓ - j
neg-distrib-⊔-⊓ = antimono-<-distrib-⊔ -_ neg-mono-<

neg-distrib-⊓-⊔ : ∀ i j → - (i ⊓ j) ≡ - i ⊔ - j
neg-distrib-⊓-⊔ = antimono-<-distrib-⊓ -_ neg-mono-<

------------------------------------------------------------------------
-- Other properties of _⊓_, _⊔_ and _*_

*-distribˡ-⊓-nonNeg : ∀ i j k .{{_ : NonNegative i}} →
                      i * (j ⊓ k) ≡ (i * j) ⊓ (i * k)
*-distribˡ-⊓-nonNeg i j k = mono-≤-distrib-⊓ (*-monoˡ-≤-nonNeg i) j k

*-distribʳ-⊓-nonNeg : ∀ i j k .{{_ : NonNegative i}} →
                      (j ⊓ k) * i ≡ (j * i) ⊓ (k * i)
*-distribʳ-⊓-nonNeg i j k = mono-≤-distrib-⊓ (*-monoʳ-≤-nonNeg i) j k

*-distribˡ-⊓-nonPos : ∀ i j k .{{_ : NonPositive i}} →
                      i * (j ⊓ k) ≡ (i * j) ⊔ (i * k)
*-distribˡ-⊓-nonPos i j k = antimono-≤-distrib-⊓ (*-monoˡ-≤-nonPos i) j k

*-distribʳ-⊓-nonPos : ∀ i j k .{{_ : NonPositive i}} →
                      (j ⊓ k) * i ≡ (j * i) ⊔ (k * i)
*-distribʳ-⊓-nonPos i j k = antimono-≤-distrib-⊓ (*-monoʳ-≤-nonPos i) j k

*-distribˡ-⊔-nonNeg : ∀ i j k .{{_ : NonNegative i}} →
                      i * (j ⊔ k) ≡ (i * j) ⊔ (i * k)
*-distribˡ-⊔-nonNeg i j k = mono-≤-distrib-⊔ (*-monoˡ-≤-nonNeg i) j k

*-distribʳ-⊔-nonNeg : ∀ i j k .{{_ : NonNegative i}} →
                      (j ⊔ k) * i ≡ (j * i) ⊔ (k * i)
*-distribʳ-⊔-nonNeg i j k = mono-≤-distrib-⊔ (*-monoʳ-≤-nonNeg i) j k

*-distribˡ-⊔-nonPos : ∀ i j k .{{_ : NonPositive i}} →
                      i * (j ⊔ k) ≡ (i * j) ⊓ (i * k)
*-distribˡ-⊔-nonPos i j k = antimono-≤-distrib-⊔ (*-monoˡ-≤-nonPos i) j k

*-distribʳ-⊔-nonPos : ∀ i j k .{{_ : NonPositive i}} →
                      (j ⊔ k) * i ≡ (j * i) ⊓ (k * i)
*-distribʳ-⊔-nonPos i j k = antimono-≤-distrib-⊔ (*-monoʳ-≤-nonPos i) j k


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.5

neg-mono-<-> = neg-mono-<
{-# WARNING_ON_USAGE neg-mono-<->
"Warning: neg-mono-<-> was deprecated in v1.5.
Please use neg-mono-< instead."
#-}

neg-mono-≤-≥ = neg-mono-≤
{-# WARNING_ON_USAGE neg-mono-≤-≥
"Warning: neg-mono-≤-≥ was deprecated in v1.5.
Please use neg-mono-≤ instead."
#-}

*-monoʳ-≤-non-neg = *-monoʳ-≤-nonNeg
{-# WARNING_ON_USAGE *-monoʳ-≤-non-neg
"Warning: *-monoʳ-≤-non-neg was deprecated in v1.5.
Please use *-monoʳ-≤-nonNeg instead."
#-}

*-monoˡ-≤-non-neg = *-monoˡ-≤-nonNeg
{-# WARNING_ON_USAGE *-monoˡ-≤-non-neg
"Warning: *-monoˡ-≤-non-neg deprecated in v1.5.
Please use *-monoˡ-≤-nonNeg instead."
#-}

*-cancelˡ-<-non-neg = *-cancelˡ-<-nonNeg
{-# WARNING_ON_USAGE *-cancelˡ-<-non-neg
"Warning: *-cancelˡ-<-non-neg was deprecated in v1.5.
Please use *-cancelˡ-<-nonNeg instead."
#-}

*-cancelʳ-<-non-neg = *-cancelʳ-<-nonNeg
{-# WARNING_ON_USAGE *-cancelʳ-<-non-neg
"Warning: *-cancelʳ-<-non-neg was deprecated in v1.5.
Please use *-cancelʳ-<-nonNeg instead."
#-}

-- Version 1.6

m≤n⇒m⊓n≡m = i≤j⇒i⊓j≡i
{-# WARNING_ON_USAGE m≤n⇒m⊓n≡m
"Warning: m≤n⇒m⊓n≡m was deprecated in v1.6
Please use i≤j⇒i⊓j≡i instead."
#-}
m⊓n≡m⇒m≤n = i⊓j≡i⇒i≤j
{-# WARNING_ON_USAGE m⊓n≡m⇒m≤n
"Warning: m≤n⇒m⊓n≡m was deprecated in v1.6
Please use i⊓j≡i⇒i≤j instead."
#-}
m≥n⇒m⊓n≡n = i≥j⇒i⊓j≡j
{-# WARNING_ON_USAGE m≥n⇒m⊓n≡n
"Warning: m≥n⇒m⊓n≡n was deprecated in v1.6
Please use i≥j⇒i⊓j≡j instead."
#-}
m⊓n≡n⇒m≥n = i⊓j≡j⇒j≤i
{-# WARNING_ON_USAGE m⊓n≡n⇒m≥n
"Warning: m⊓n≡n⇒m≥n was deprecated in v1.6
Please use i⊓j≡j⇒j≤i instead."
#-}
m⊓n≤n = i⊓j≤j
{-# WARNING_ON_USAGE m⊓n≤n
"Warning: m⊓n≤n was deprecated in v1.6
Please use i⊓j≤j instead."
#-}
m⊓n≤m = i⊓j≤i
{-# WARNING_ON_USAGE m⊓n≤m
"Warning: m⊓n≤m was deprecated in v1.6
Please use i⊓j≤i instead."
#-}
m≤n⇒m⊔n≡n = i≤j⇒i⊔j≡j
{-# WARNING_ON_USAGE m≤n⇒m⊔n≡n
"Warning: m≤n⇒m⊔n≡n was deprecated in v1.6
Please use i≤j⇒i⊔j≡j instead."
#-}
m⊔n≡n⇒m≤n = i⊔j≡j⇒i≤j
{-# WARNING_ON_USAGE m⊔n≡n⇒m≤n
"Warning: m⊔n≡n⇒m≤n was deprecated in v1.6
Please use i⊔j≡j⇒i≤j instead."
#-}
m≥n⇒m⊔n≡m = i≥j⇒i⊔j≡i
{-# WARNING_ON_USAGE m≥n⇒m⊔n≡m
"Warning: m≥n⇒m⊔n≡m was deprecated in v1.6
Please use i≥j⇒i⊔j≡i instead."
#-}
m⊔n≡m⇒m≥n = i⊔j≡i⇒j≤i
{-# WARNING_ON_USAGE m⊔n≡m⇒m≥n
"Warning: m⊔n≡m⇒m≥n was deprecated in v1.6
Please use i⊔j≡i⇒j≤i instead."
#-}
m≤m⊔n = i≤i⊔j
{-# WARNING_ON_USAGE m≤m⊔n
"Warning: m≤m⊔n was deprecated in v1.6
Please use i≤i⊔j instead."
#-}
n≤m⊔n = i≤j⊔i
{-# WARNING_ON_USAGE n≤m⊔n
"Warning: n≤m⊔n was deprecated in v1.6
Please use i≤j⊔i instead."
#-}

-- Version 2.0

+-pos-monoʳ-≤ : ∀ n → (_+_ (+ n)) Preserves _≤_ ⟶ _≤_
+-pos-monoʳ-≤ n {_}         (-≤- o≤m) = ⊖-monoʳ-≥-≤ n (s≤s o≤m)
+-pos-monoʳ-≤ n { -[1+ m ]} -≤+       = ≤-trans (m⊖n≤m n (suc m)) (+≤+ (ℕ.m≤m+n n _))
+-pos-monoʳ-≤ n {_}         (+≤+ m≤o) = +≤+ (ℕ.+-monoʳ-≤ n m≤o)
{-# WARNING_ON_USAGE +-pos-monoʳ-≤
"Warning: +-pos-monoʳ-≤ was deprecated in v2.0
Please use +-monoʳ-≤ instead."
#-}
+-neg-monoʳ-≤ : ∀ n → (_+_ (-[1+ n ])) Preserves _≤_ ⟶ _≤_
+-neg-monoʳ-≤ n {_} {_}   (-≤- n≤m) = -≤- (ℕ.+-monoʳ-≤ (suc n) n≤m)
+-neg-monoʳ-≤ n {_} {+ m} -≤+       = ≤-trans (-≤- (ℕ.m≤m+n (suc n) _)) (-1+m≤n⊖m (suc n) m)
+-neg-monoʳ-≤ n {_} {_}   (+≤+ m≤n) = ⊖-monoˡ-≤ (suc n) m≤n
{-# WARNING_ON_USAGE +-neg-monoʳ-≤
"Warning: +-neg-monoʳ-≤ was deprecated in v2.0
Please use +-monoʳ-≤ instead."
#-}
n≮n = i≮i
{-# WARNING_ON_USAGE n≮n
"Warning: n≮n was deprecated in v2.0
Please use i≮i instead."
#-}
∣n∣≡0⇒n≡0 = ∣i∣≡0⇒i≡0
{-# WARNING_ON_USAGE ∣n∣≡0⇒n≡0
"Warning: ∣n∣≡0⇒n≡0 was deprecated in v2.0
Please use ∣i∣≡0⇒i≡0 instead."
#-}
∣-n∣≡∣n∣ = ∣-i∣≡∣i∣
{-# WARNING_ON_USAGE ∣-n∣≡∣n∣
"Warning: ∣-n∣≡∣n∣ was deprecated in v2.0
Please use ∣-i∣≡∣i∣ instead."
#-}
0≤n⇒+∣n∣≡n = 0≤i⇒+∣i∣≡i
{-# WARNING_ON_USAGE 0≤n⇒+∣n∣≡n
"Warning: 0≤n⇒+∣n∣≡n was deprecated in v2.0
Please use 0≤i⇒+∣i∣≡i instead."
#-}
+∣n∣≡n⇒0≤n = +∣i∣≡i⇒0≤i
{-# WARNING_ON_USAGE +∣n∣≡n⇒0≤n
"Warning: +∣n∣≡n⇒0≤n was deprecated in v2.0
Please use +∣i∣≡i⇒0≤i instead."
#-}
+∣n∣≡n⊎+∣n∣≡-n = +∣i∣≡i⊎+∣i∣≡-i
{-# WARNING_ON_USAGE +∣n∣≡n⊎+∣n∣≡-n
"Warning: +∣n∣≡n⊎+∣n∣≡-n was deprecated in v2.0
Please use +∣i∣≡i⊎+∣i∣≡-i instead."
#-}
∣m+n∣≤∣m∣+∣n∣ = ∣i+j∣≤∣i∣+∣j∣
{-# WARNING_ON_USAGE ∣m+n∣≤∣m∣+∣n∣
"Warning: ∣m+n∣≤∣m∣+∣n∣ was deprecated in v2.0
Please use ∣i+j∣≤∣i∣+∣j∣ instead."
#-}
∣m-n∣≤∣m∣+∣n∣ = ∣i-j∣≤∣i∣+∣j∣
{-# WARNING_ON_USAGE ∣m-n∣≤∣m∣+∣n∣
"Warning: ∣m-n∣≤∣m∣+∣n∣ was deprecated in v2.0
Please use ∣i-j∣≤∣i∣+∣j∣ instead."
#-}
signₙ◃∣n∣≡n = signᵢ◃∣i∣≡i
{-# WARNING_ON_USAGE signₙ◃∣n∣≡n
"Warning: signₙ◃∣n∣≡n was deprecated in v2.0
Please use signᵢ◃∣i∣≡i instead."
#-}
◃-≡ = ◃-cong
{-# WARNING_ON_USAGE ◃-≡
"Warning: ◃-≡ was deprecated in v2.0
Please use ◃-cong instead."
#-}
∣m-n∣≡∣n-m∣ = ∣i-j∣≡∣j-i∣
{-# WARNING_ON_USAGE ∣m-n∣≡∣n-m∣
"Warning: ∣m-n∣≡∣n-m∣ was deprecated in v2.0
Please use ∣i-j∣≡∣j-i∣ instead."
#-}
m≡n⇒m-n≡0 = i≡j⇒i-j≡0
{-# WARNING_ON_USAGE m≡n⇒m-n≡0
"Warning: m≡n⇒m-n≡0 was deprecated in v2.0
Please use i≡j⇒i-j≡0 instead."
#-}
m-n≡0⇒m≡n = i-j≡0⇒i≡j
{-# WARNING_ON_USAGE m-n≡0⇒m≡n
"Warning: m-n≡0⇒m≡n was deprecated in v2.0
Please use i-j≡0⇒i≡j instead."
#-}
≤-steps = i≤j⇒i≤k+j
{-# WARNING_ON_USAGE ≤-steps
"Warning: ≤-steps was deprecated in v2.0
Please use i≤j⇒i≤k+j instead."
#-}
≤-steps-neg = i≤j⇒i-k≤j
{-# WARNING_ON_USAGE ≤-steps-neg
"Warning: ≤-steps-neg was deprecated in v2.0
Please use i≤j⇒i-k≤j instead."
#-}
≤-step = i≤j⇒i≤1+j
{-# WARNING_ON_USAGE ≤-step
"Warning: ≤-step was deprecated in v2.0
Please use i≤j⇒i≤1+j instead."
#-}
≤-step-neg = i≤j⇒pred[i]≤j
{-# WARNING_ON_USAGE ≤-step-neg
"Warning: ≤-step-neg was deprecated in v2.0
Please use i≤j⇒pred[i]≤j instead."
#-}
m≤n⇒m-n≤0 = i≤j⇒i-j≤0
{-# WARNING_ON_USAGE m≤n⇒m-n≤0
"Warning: m≤n⇒m-n≤0 was deprecated in v2.0
Please use i≤j⇒i-j≤0 instead."
#-}
m-n≤0⇒m≤n = i-j≤0⇒i≤j
{-# WARNING_ON_USAGE m-n≤0⇒m≤n
"Warning: m-n≤0⇒m≤n was deprecated in v2.0
Please use i-j≤0⇒i≤j instead."
#-}
m≤n⇒0≤n-m = i≤j⇒0≤j-i
{-# WARNING_ON_USAGE m≤n⇒0≤n-m
"Warning: m≤n⇒0≤n-m was deprecated in v2.0
Please use i≤j⇒0≤j-i instead."
#-}
0≤n-m⇒m≤n = 0≤i-j⇒j≤i
{-# WARNING_ON_USAGE 0≤n-m⇒m≤n
"Warning: 0≤n-m⇒m≤n was deprecated in v2.0
Please use 0≤i-j⇒j≤i instead."
#-}
n≤1+n = i≤suc[i]
{-# WARNING_ON_USAGE n≤1+n
"Warning: n≤1+n was deprecated in v2.0
Please use i≤suc[i] instead."
#-}
n≢1+n = i≢suc[i]
{-# WARNING_ON_USAGE n≢1+n
"Warning: n≢1+n was deprecated in v2.0
Please use i≢suc[i] instead."
#-}
m≤pred[n]⇒m<n = i≤pred[j]⇒i<j
{-# WARNING_ON_USAGE m≤pred[n]⇒m<n
"Warning: m≤pred[n]⇒m<n was deprecated in v2.0
Please use i≤pred[j]⇒i<j instead."
#-}
m<n⇒m≤pred[n] = i<j⇒i≤pred[j]
{-# WARNING_ON_USAGE m<n⇒m≤pred[n]
"Warning: m<n⇒m≤pred[n] was deprecated in v2.0
Please use i<j⇒i≤pred[j] instead."
#-}
-1*n≡-n = -1*i≡-i
{-# WARNING_ON_USAGE -1*n≡-n
"Warning: -1*n≡-n was deprecated in v2.0
Please use -1*i≡-i instead."
#-}
m*n≡0⇒m≡0∨n≡0 = i*j≡0⇒i≡0∨j≡0
{-# WARNING_ON_USAGE m*n≡0⇒m≡0∨n≡0
"Warning: m*n≡0⇒m≡0∨n≡0 was deprecated in v2.0
Please use i*j≡0⇒i≡0∨j≡0 instead."
#-}
∣m*n∣≡∣m∣*∣n∣ = ∣i*j∣≡∣i∣*∣j∣
{-# WARNING_ON_USAGE ∣m*n∣≡∣m∣*∣n∣
"Warning: ∣m*n∣≡∣m∣*∣n∣ was deprecated in v2.0
Please use ∣i*j∣≡∣i∣*∣j∣ instead."
#-}
n≤m+n : ∀ n → i ≤ + n + i
n≤m+n {i} n = i≤j+i i (+ n)
{-# WARNING_ON_USAGE n≤m+n
"Warning: n≤m+n was deprecated in v2.0
Please use i≤j+i instead. Note the change of form of the explicit arguments."
#-}
m≤m+n : ∀ n → i ≤ i + + n
m≤m+n {i} n = i≤i+j i (+ n)
{-# WARNING_ON_USAGE m≤m+n
"Warning: m≤m+n was deprecated in v2.0
Please use i≤i+j instead. Note the change of form of the explicit arguments."
#-}
m-n≤m : ∀ i n → i - + n ≤ i
m-n≤m i n = i-j≤i i (+ n)
{-# WARNING_ON_USAGE m-n≤m
"Warning: m-n≤m was deprecated in v2.0
Please use i-j≤i instead. Note the change of form of the explicit arguments."
#-}
*-monoʳ-≤-pos : ∀ n → (_* + suc n) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-pos n = *-monoʳ-≤-nonNeg +[1+ n ]
{-# WARNING_ON_USAGE *-monoʳ-≤-pos
"Warning: *-monoʳ-≤-pos was deprecated in v2.0
Please use *-monoʳ-≤-nonNeg instead."
#-}
*-monoˡ-≤-pos : ∀ n → (+ suc n *_) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-pos n = *-monoˡ-≤-nonNeg +[1+ n ]
{-# WARNING_ON_USAGE *-monoˡ-≤-pos
"Warning: *-monoˡ-≤-pos was deprecated in v2.0
Please use *-monoˡ-≤-nonNeg instead."
#-}
*-monoˡ-≤-neg : ∀ m → (-[1+ m ] *_) Preserves _≤_ ⟶ _≥_
*-monoˡ-≤-neg m = *-monoˡ-≤-nonPos -[1+ m ]
{-# WARNING_ON_USAGE *-monoˡ-≤-neg
"Warning: *-monoˡ-≤-neg was deprecated in v2.0
Please use *-monoˡ-≤-nonPos instead."
#-}
*-monoʳ-≤-neg : ∀ m → (_* -[1+ m ]) Preserves _≤_ ⟶ _≥_
*-monoʳ-≤-neg m = *-monoʳ-≤-nonPos -[1+ m ]
{-# WARNING_ON_USAGE *-monoʳ-≤-neg
"Warning: *-monoʳ-≤-neg was deprecated in v2.0
Please use *-monoʳ-≤-nonPos instead."
#-}
pos-+-commute : ℕtoℤ.Homomorphic₂ +_ ℕ._+_ _+_
pos-+-commute = pos-+
{-# WARNING_ON_USAGE pos-+-commute
"Warning: pos-+-commute was deprecated in v2.0
Please use pos-+ instead."
#-}
abs-*-commute : ℤtoℕ.Homomorphic₂ ∣_∣ _*_ ℕ._*_
abs-*-commute = abs-*
{-# WARNING_ON_USAGE abs-*-commute
"Warning: abs-*-commute was deprecated in v2.0
Please use abs-* instead."
#-}
pos-distrib-* : ∀ m n → (+ m) * (+ n) ≡ + (m ℕ.* n)
pos-distrib-* m n = sym (pos-* m n)
{-# WARNING_ON_USAGE pos-distrib-*
"Warning: pos-distrib-* was deprecated in v2.0
Please use pos-* instead."
#-}
+-isAbelianGroup = +-0-isAbelianGroup
{-# WARNING_ON_USAGE +-isAbelianGroup
"Warning: +-isAbelianGroup was deprecated in v2.0
Please use +-0-isAbelianGroup instead."
#-}
{- issue1844/issue1755: raw bundles have moved to `Data.X.Base` -}
open Data.Integer.Base public
  using (*-rawMagma; *-1-rawMonoid)
