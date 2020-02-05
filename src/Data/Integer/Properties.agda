------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated names
{-# OPTIONS --warn=noUserWarning #-}

module Data.Integer.Properties where

open import Algebra.Bundles
import Algebra.Morphism as Morphism
import Algebra.Properties.AbelianGroup
open import Data.Integer.Base renaming (suc to sucℤ)
open import Data.Nat as ℕ
  using (ℕ; suc; zero; _∸_; s≤s; z≤n)
  hiding (module ℕ)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Solver
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Data.Sign as Sign using () renaming (_*_ to _𝕊*_)
import Data.Sign.Properties as 𝕊ₚ
open import Function using (_∘_; _$_)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Nullary.Decidable as Dec

open import Algebra.Definitions {A = ℤ} _≡_
open import Algebra.FunctionProperties.Consequences.Propositional
open import Algebra.Structures {A = ℤ} _≡_
module ℤtoℕ = Morphism.Definitions ℤ ℕ _≡_
module ℕtoℤ = Morphism.Definitions ℕ ℤ _≡_
open +-*-Solver

------------------------------------------------------------------------
-- Equality
------------------------------------------------------------------------

+-injective : ∀ {m n} → + m ≡ + n → m ≡ n
+-injective refl = refl

-[1+-injective : ∀ {m n} → -[1+ m ] ≡ -[1+ n ] → m ≡ n
-[1+-injective refl = refl

+[1+-injective : ∀ {m n} → +[1+ m ] ≡ +[1+ n ] → m ≡ n
+[1+-injective refl = refl

infix 4 _≟_
_≟_ : Decidable {A = ℤ} _≡_
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

drop‿+≤+ : ∀ {m n} → + m ≤ + n → m ℕ.≤ n
drop‿+≤+ (+≤+ m≤n) = m≤n

drop‿-≤- : ∀ {m n} → -[1+ m ] ≤ -[1+ n ] → n ℕ.≤ m
drop‿-≤- (-≤- n≤m) = n≤m

------------------------------------------------------------------------
-- Relational properties

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
≤-antisym (-≤- n≤m) (-≤- m≤n) = cong -[1+_] $ ℕₚ.≤-antisym m≤n n≤m
≤-antisym (+≤+ m≤n) (+≤+ n≤m) = cong (+_)   $ ℕₚ.≤-antisym m≤n n≤m

≤-total : Total _≤_
≤-total (-[1+ m ]) (-[1+ n ]) = Sum.map -≤- -≤- (ℕₚ.≤-total n m)
≤-total (-[1+ m ]) (+    n  ) = inj₁ -≤+
≤-total (+    m  ) (-[1+ n ]) = inj₂ -≤+
≤-total (+    m  ) (+    n  ) = Sum.map +≤+ +≤+ (ℕₚ.≤-total m n)

infix  4 _≤?_
_≤?_ : Decidable _≤_
-[1+ m ] ≤? -[1+ n ] = Dec.map′ -≤- drop‿-≤- (n ℕ.≤? m)
-[1+ m ] ≤? +    n   = yes -≤+
+    m   ≤? -[1+ n ] = no λ ()
+    m   ≤? +    n   = Dec.map′ +≤+ drop‿+≤+ (m ℕ.≤? n)

≤-irrelevant : Irrelevant _≤_
≤-irrelevant -≤+       -≤+         = refl
≤-irrelevant (-≤- n≤m₁) (-≤- n≤m₂) = cong -≤- (ℕₚ.≤-irrelevant n≤m₁ n≤m₂)
≤-irrelevant (+≤+ n≤m₁) (+≤+ n≤m₂) = cong +≤+ (ℕₚ.≤-irrelevant n≤m₁ n≤m₂)

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
-- Bundles

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
-- Properties _<_
------------------------------------------------------------------------

drop‿+<+ : ∀ {m n} → + m < + n → m ℕ.< n
drop‿+<+ (+<+ m<n) = m<n

drop‿-<- : ∀ {m n} → -[1+ m ] < -[1+ n ] → n ℕ.< m
drop‿-<- (-<- n<m) = n<m

+≮0 : ∀ {n} → + n ≮ +0
+≮0 (+<+ ())

+≮- : ∀ {m n} → + m ≮ -[1+ n ]
+≮- ()

------------------------------------------------------------------------
-- Relationship between other operators

<⇒≤ : ∀ {i j} → i < j → i ≤ j
<⇒≤ (-<- i<j) = -≤- (ℕₚ.<⇒≤ i<j)
<⇒≤ -<+       = -≤+
<⇒≤ (+<+ i<j) = +≤+ (ℕₚ.<⇒≤ i<j)

>⇒≰ : ∀ {i j} → i > j → i ≰ j
>⇒≰ (-<- n<m) = ℕₚ.<⇒≱ n<m ∘ drop‿-≤-
>⇒≰ (+<+ m<n) = ℕₚ.<⇒≱ m<n ∘ drop‿+≤+

≰⇒> : ∀ {i j} → i ≰ j → i > j
≰⇒> {+ n}       {+_ n₁}      i≰j = +<+ (ℕₚ.≰⇒> (i≰j ∘ +≤+))
≰⇒> {+ n}       { -[1+_] n₁} i≰j = -<+
≰⇒> { -[1+_] n} {+_ n₁}      i≰j = contradiction -≤+ i≰j
≰⇒> { -[1+_] n} { -[1+_] n₁} i≰j = -<- (ℕₚ.≰⇒> (i≰j ∘ -≤-))

------------------------------------------------------------------------
-- Relational properties

<-irrefl : Irreflexive _≡_ _<_
<-irrefl { -[1+ n ]} refl = ℕₚ.<-irrefl refl ∘ drop‿-<-
<-irrefl { +0}       refl (+<+ ())
<-irrefl { +[1+ n ]} refl = ℕₚ.<-irrefl refl ∘ drop‿+<+

<-asym : Asymmetric _<_
<-asym (-<- n<m) = ℕₚ.<-asym n<m ∘ drop‿-<-
<-asym (+<+ m<n) = ℕₚ.<-asym m<n ∘ drop‿+<+

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans (-≤- n≤m) (-<- o<n) = -<- (ℕₚ.<-transˡ o<n n≤m)
≤-<-trans (-≤- n≤m) -<+       = -<+
≤-<-trans -≤+       (+<+ m<o) = -<+
≤-<-trans (+≤+ m≤n) (+<+ n<o) = +<+ (ℕₚ.<-transʳ m≤n n<o)

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans (-<- n<m) (-≤- o≤n) = -<- (ℕₚ.<-transʳ o≤n n<m)
<-≤-trans (-<- n<m) -≤+       = -<+
<-≤-trans -<+       (+≤+ m≤n) = -<+
<-≤-trans (+<+ m<n) (+≤+ n≤o) = +<+ (ℕₚ.<-transˡ m<n n≤o)

<-trans : Transitive _<_
<-trans m<n n<p = ≤-<-trans (<⇒≤ m<n) n<p

<-cmp : Trichotomous _≡_ _<_
<-cmp +0       +0       = tri≈ +≮0 refl +≮0
<-cmp +0       +[1+ n ] = tri< (+<+ (s≤s z≤n)) (λ()) +≮0
<-cmp +[1+ n ] +0       = tri> +≮0 (λ()) (+<+ (s≤s z≤n))
<-cmp (+ m)    -[1+ n ] = tri> +≮- (λ()) -<+
<-cmp -[1+ m ] (+ n)    = tri< -<+ (λ()) +≮-
<-cmp -[1+ m ] -[1+ n ] with ℕₚ.<-cmp m n
... | tri< m<n m≢n n≯m = tri> (n≯m ∘ drop‿-<-) (m≢n ∘ -[1+-injective) (-<- m<n)
... | tri≈ m≮n m≡n n≯m = tri≈ (n≯m ∘ drop‿-<-) (cong -[1+_] m≡n) (m≮n ∘ drop‿-<-)
... | tri> m≮n m≢n n>m = tri< (-<- n>m) (m≢n ∘ -[1+-injective) (m≮n ∘ drop‿-<-)
<-cmp +[1+ m ] +[1+ n ] with ℕₚ.<-cmp m n
... | tri< m<n m≢n n≯m = tri< (+<+ (s≤s m<n))              (m≢n ∘ +[1+-injective) (n≯m ∘ ℕₚ.≤-pred ∘ drop‿+<+)
... | tri≈ m≮n m≡n n≯m = tri≈ (m≮n ∘ ℕₚ.≤-pred ∘ drop‿+<+) (cong (+_ ∘ suc) m≡n)  (n≯m ∘ ℕₚ.≤-pred ∘ drop‿+<+)
... | tri> m≮n m≢n n>m = tri> (m≮n ∘ ℕₚ.≤-pred ∘ drop‿+<+) (m≢n ∘ +[1+-injective) (+<+ (s≤s n>m))

infix 4 _<?_
_<?_ : Decidable _<_
-[1+ m ] <? -[1+ n ] = Dec.map′ -<- drop‿-<- (n ℕ.<? m)
-[1+ m ] <? + n      = yes -<+
+ m      <? -[1+ n ] = no λ()
+ m      <? + n      = Dec.map′ +<+ drop‿+<+ (m ℕ.<? n)

<-irrelevant : Irrelevant _<_
<-irrelevant (-<- n<m₁) (-<- n<m₂) = cong -<- (ℕₚ.<-irrelevant n<m₁ n<m₂)
<-irrelevant -<+       -<+         = refl
<-irrelevant (+<+ m<n₁) (+<+ m<n₂) = cong +<+ (ℕₚ.<-irrelevant m<n₁ m<n₂)

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

n≮n : ∀ {n} → n ≮ n
n≮n {n} = <-irrefl refl

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
-- Properties of -_
------------------------------------------------------------------------

neg-involutive : ∀ n → - - n ≡ n
neg-involutive -[1+ n ] = refl
neg-involutive +0       = refl
neg-involutive +[1+ n ] = refl

neg-injective : ∀ {m n} → - m ≡ - n → m ≡ n
neg-injective {m} {n} -m≡-n = begin
  m     ≡⟨ sym (neg-involutive m) ⟩
  - - m ≡⟨ cong -_ -m≡-n ⟩
  - - n ≡⟨ neg-involutive n ⟩
  n     ∎ where open ≡-Reasoning

neg-≤-pos : ∀ {m n} → - (+ m) ≤ + n
neg-≤-pos {zero}  = +≤+ z≤n
neg-≤-pos {suc m} = -≤+

neg-mono-<-> : -_ Preserves _<_ ⟶ _>_
neg-mono-<-> { -[1+ _ ]} { -[1+ _ ]} (-<- n<m) = +<+ (s≤s n<m)
neg-mono-<-> { -[1+ _ ]} { +0}       -<+       = +<+ (s≤s z≤n)
neg-mono-<-> { -[1+ _ ]} { +[1+ n ]} -<+       = -<+
neg-mono-<-> { +0}       { +[1+ n ]} (+<+ _)   = -<+
neg-mono-<-> { +[1+ m ]} { +[1+ n ]} (+<+ m<n) = -<- (ℕₚ.≤-pred m<n)

------------------------------------------------------------------------
-- Properties of ∣_∣
------------------------------------------------------------------------

∣n∣≡0⇒n≡0 : ∀ {n} → ∣ n ∣ ≡ 0 → n ≡ + 0
∣n∣≡0⇒n≡0 {+0} refl = refl

∣-n∣≡∣n∣ : ∀ n → ∣ - n ∣ ≡ ∣ n ∣
∣-n∣≡∣n∣ -[1+ n ] = refl
∣-n∣≡∣n∣ +0       = refl
∣-n∣≡∣n∣ +[1+ n ] = refl

0≤n⇒+∣n∣≡n : ∀ {n} → + 0 ≤ n → + ∣ n ∣ ≡ n
0≤n⇒+∣n∣≡n (+≤+ 0≤n) = refl

+∣n∣≡n⇒0≤n : ∀ {n} → + ∣ n ∣ ≡ n → + 0 ≤ n
+∣n∣≡n⇒0≤n {+ n} _ = +≤+ z≤n

------------------------------------------------------------------------
-- Properties of sign and _◃_

◃-inverse : ∀ i → sign i ◃ ∣ i ∣ ≡ i
◃-inverse -[1+ n ] = refl
◃-inverse +0       = refl
◃-inverse +[1+ n ] = refl

◃-cong : ∀ {i j} → sign i ≡ sign j → ∣ i ∣ ≡ ∣ j ∣ → i ≡ j
◃-cong {i} {j} sign-≡ abs-≡ = begin
  i               ≡⟨ sym $ ◃-inverse i ⟩
  sign i ◃ ∣ i ∣  ≡⟨ cong₂ _◃_ sign-≡ abs-≡ ⟩
  sign j ◃ ∣ j ∣  ≡⟨ ◃-inverse j ⟩
  j               ∎ where open ≡-Reasoning

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
signₙ◃∣n∣≡n (+ n)    = +◃n≡+n n
signₙ◃∣n∣≡n -[1+ n ] = refl

sign-cong : ∀ {s₁ s₂ n₁ n₂} →
            s₁ ◃ suc n₁ ≡ s₂ ◃ suc n₂ → s₁ ≡ s₂
sign-cong {s₁} {s₂} {n₁} {n₂} eq = begin
  s₁                  ≡⟨ sym $ sign-◃ s₁ n₁ ⟩
  sign (s₁ ◃ suc n₁)  ≡⟨ cong sign eq ⟩
  sign (s₂ ◃ suc n₂)  ≡⟨ sign-◃ s₂ n₂ ⟩
  s₂                  ∎ where open ≡-Reasoning

abs-cong : ∀ {s₁ s₂ n₁ n₂} → s₁ ◃ n₁ ≡ s₂ ◃ n₂ → n₁ ≡ n₂
abs-cong {s₁} {s₂} {n₁} {n₂} eq = begin
  n₁           ≡⟨ sym $ abs-◃ s₁ n₁ ⟩
  ∣ s₁ ◃ n₁ ∣  ≡⟨ cong ∣_∣ eq ⟩
  ∣ s₂ ◃ n₂ ∣  ≡⟨ abs-◃ s₂ n₂ ⟩
  n₂           ∎ where open ≡-Reasoning

∣s◃m∣*∣t◃n∣≡m*n : ∀ s t m n → ∣ s ◃ m ∣ ℕ.* ∣ t ◃ n ∣ ≡ m ℕ.* n
∣s◃m∣*∣t◃n∣≡m*n s t m n = cong₂ ℕ._*_ (abs-◃ s m) (abs-◃ t n)

◃-≡ : ∀ {m n} → sign m ≡ sign n → ∣ m ∣ ≡ ∣ n ∣ → m ≡ n
◃-≡ {+ m}       {+ n }      ≡-sign refl = refl
◃-≡ { -[1+ m ]} { -[1+ n ]} ≡-sign refl = refl

+◃-mono-< : ∀ {m n} → m ℕ.< n → Sign.+ ◃ m < Sign.+ ◃ n
+◃-mono-< {zero}  {suc n} m<n = +<+ m<n
+◃-mono-< {suc m} {suc n} m<n = +<+ m<n

+◃-cancel-< : ∀ {m n} → Sign.+ ◃ m < Sign.+ ◃ n → m ℕ.< n
+◃-cancel-< {zero}  {zero}  (+<+ ())
+◃-cancel-< {suc m} {zero}  (+<+ ())
+◃-cancel-< {zero}  {suc n} (+<+ m<n) = m<n
+◃-cancel-< {suc m} {suc n} (+<+ m<n) = m<n

neg◃-cancel-< : ∀ {m n} → Sign.- ◃ m < Sign.- ◃ n → n ℕ.< m
neg◃-cancel-< {zero}  {suc n} ()
neg◃-cancel-< {zero}  {zero}  (+<+ ())
neg◃-cancel-< {suc m} {zero}  -<+       = s≤s z≤n
neg◃-cancel-< {suc m} {suc n} (-<- n<m) = s≤s n<m

-◃<+◃ : ∀ m n → Sign.- ◃ (suc m) < Sign.+ ◃ n
-◃<+◃ m zero    = -<+
-◃<+◃ m (suc n) = -<+

+◃≮-◃ : ∀ {m n} → Sign.+ ◃ m ≮ Sign.- ◃ n
+◃≮-◃ {zero}  {zero} (+<+ ())
+◃≮-◃ {suc m} {zero} (+<+ ())

------------------------------------------------------------------------
-- Properties of _⊖_
------------------------------------------------------------------------

n⊖n≡0 : ∀ n → n ⊖ n ≡ + 0
n⊖n≡0 zero    = refl
n⊖n≡0 (suc n) = n⊖n≡0 n

⊖-swap : ∀ a b → a ⊖ b ≡ - (b ⊖ a)
⊖-swap zero    zero    = refl
⊖-swap (suc _) zero    = refl
⊖-swap zero    (suc _) = refl
⊖-swap (suc a) (suc b) = ⊖-swap a b

⊖-≥ : ∀ {m n} → m ℕ.≥ n → m ⊖ n ≡ + (m ∸ n)
⊖-≥ z≤n         = refl
⊖-≥ (ℕ.s≤s n≤m) = ⊖-≥ n≤m

⊖-< : ∀ {m n} → m ℕ.< n → m ⊖ n ≡ - + (n ∸ m)
⊖-< {zero}  (ℕ.s≤s z≤n) = refl
⊖-< {suc m} (ℕ.s≤s m<n) = ⊖-< m<n

⊖-≰ : ∀ {m n} → n ℕ.≰ m → m ⊖ n ≡ - + (n ∸ m)
⊖-≰ = ⊖-< ∘ ℕₚ.≰⇒>

∣⊖∣-< : ∀ {m n} → m ℕ.< n → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-< {zero}  (ℕ.s≤s z≤n) = refl
∣⊖∣-< {suc n} (ℕ.s≤s m<n) = ∣⊖∣-< m<n

∣⊖∣-≰ : ∀ {m n} → n ℕ.≰ m → ∣ m ⊖ n ∣ ≡ n ∸ m
∣⊖∣-≰ = ∣⊖∣-< ∘ ℕₚ.≰⇒>

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

+-cancelˡ-⊖ : ∀ a b c → (a ℕ.+ b) ⊖ (a ℕ.+ c) ≡ b ⊖ c
+-cancelˡ-⊖ zero    b c = refl
+-cancelˡ-⊖ (suc a) b c = +-cancelˡ-⊖ a b c

m⊖n≤m : ∀ m n → m ⊖ n ≤ + m
m⊖n≤m m       zero    = ≤-refl
m⊖n≤m zero    (suc n) = -≤+
m⊖n≤m (suc m) (suc n) = ≤-trans (m⊖n≤m m n) (+≤+ (ℕₚ.n≤1+n m))

m⊖n<1+m : ∀ m n → m ⊖ n < +[1+ m ]
m⊖n<1+m m       zero    = +<+ ℕₚ.≤-refl
m⊖n<1+m zero    (suc n) = -<+
m⊖n<1+m (suc m) (suc n) = <-trans (m⊖n<1+m m n) (+<+ ℕₚ.≤-refl)

m⊖1+n<m : ∀ m n → m ⊖ suc n < + m
m⊖1+n<m zero    n = -<+
m⊖1+n<m (suc m) n = m⊖n<1+m m n

-1+m<n⊖m : ∀ m n → -[1+ m ] < n ⊖ m
-1+m<n⊖m zero    n       = -<+
-1+m<n⊖m (suc m) zero    = -<- ℕₚ.≤-refl
-1+m<n⊖m (suc m) (suc n) = <-trans (-<- ℕₚ.≤-refl) (-1+m<n⊖m m n)

-[1+m]≤n⊖m+1 : ∀ m n → -[1+ m ] ≤ n ⊖ suc m
-[1+m]≤n⊖m+1 m zero    = ≤-refl
-[1+m]≤n⊖m+1 m (suc n) = <⇒≤ (-1+m<n⊖m m n)

-1+m≤n⊖m : ∀ m n → -[1+ m ] ≤ n ⊖ m
-1+m≤n⊖m m n = <⇒≤ (-1+m<n⊖m m n)

0⊖m≤+ : ∀ m {n} → 0 ⊖ m ≤ + n
0⊖m≤+ zero    = +≤+ z≤n
0⊖m≤+ (suc m) = -≤+

sign-⊖-< : ∀ {m n} → m ℕ.< n → sign (m ⊖ n) ≡ Sign.-
sign-⊖-< {zero}  (ℕ.s≤s z≤n) = refl
sign-⊖-< {suc n} (ℕ.s≤s m<n) = sign-⊖-< m<n

sign-⊖-≰ : ∀ {m n} → n ℕ.≰ m → sign (m ⊖ n) ≡ Sign.-
sign-⊖-≰ = sign-⊖-< ∘ ℕₚ.≰⇒>

⊖-monoʳ-≥-≤ : ∀ p → (p ⊖_) Preserves ℕ._≥_ ⟶ _≤_
⊖-monoʳ-≥-≤ zero    (z≤n {n})     = 0⊖m≤+ n
⊖-monoʳ-≥-≤ zero    (s≤s m≤n)     = -≤- m≤n
⊖-monoʳ-≥-≤ (suc p) (z≤n {zero})  = ≤-refl
⊖-monoʳ-≥-≤ (suc p) (z≤n {suc n}) = ≤-trans (⊖-monoʳ-≥-≤ p (z≤n {n})) (+≤+ (ℕₚ.n≤1+n p))
⊖-monoʳ-≥-≤ (suc p) (s≤s m≤n)     = ⊖-monoʳ-≥-≤ p m≤n

⊖-monoˡ-≤ : ∀ p → (_⊖ p) Preserves ℕ._≤_ ⟶ _≤_
⊖-monoˡ-≤ zero    m≤n             = +≤+ m≤n
⊖-monoˡ-≤ (suc p) (z≤n {0})       = ≤-refl
⊖-monoˡ-≤ (suc p) (z≤n {(suc m)}) = ≤-trans (⊖-monoʳ-≥-≤ 0 (ℕₚ.n≤1+n p)) (⊖-monoˡ-≤ p z≤n)
⊖-monoˡ-≤ (suc p) (s≤s m≤n)       = ⊖-monoˡ-≤ p m≤n

⊖-monoʳ->-< : ∀ p → (p ⊖_) Preserves ℕ._>_ ⟶ _<_
⊖-monoʳ->-< zero    {_}     (s≤s z≤n)       = -<+
⊖-monoʳ->-< zero    {_}     (s≤s (s≤s m≤n)) = -<- (s≤s m≤n)
⊖-monoʳ->-< (suc p) {suc m} (s≤s z≤n)       = m⊖n<1+m p m
⊖-monoʳ->-< (suc p) {_}     (s≤s (s≤s m≤n)) = ⊖-monoʳ->-< p (s≤s m≤n)

⊖-monoˡ-< : ∀ p → (_⊖ p) Preserves ℕ._<_ ⟶ _<_
⊖-monoˡ-< zero    m<n             = +<+ m<n
⊖-monoˡ-< (suc p) (s≤s z≤n)       = -1+m<n⊖m p _
⊖-monoˡ-< (suc p) (s≤s (s≤s m<n)) = ⊖-monoˡ-< p (s≤s m<n)

------------------------------------------------------------------------
-- Properties of _+_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties of _+_

+-comm : Commutative _+_
+-comm -[1+ a ] -[1+ b ] = cong (-[1+_] ∘ suc) (ℕₚ.+-comm a b)
+-comm (+   a ) (+   b ) = cong +_ (ℕₚ.+-comm a b)
+-comm -[1+ _ ] (+   _ ) = refl
+-comm (+   _ ) -[1+ _ ] = refl

+-identityˡ : LeftIdentity +0 _+_
+-identityˡ -[1+ _ ] = refl
+-identityˡ (+   _ ) = refl

+-identityʳ : RightIdentity +0 _+_
+-identityʳ = comm+idˡ⇒idʳ +-comm +-identityˡ

+-identity : Identity +0 _+_
+-identity = +-identityˡ , +-identityʳ

distribˡ-⊖-+-pos : ∀ a b c → b ⊖ c + + a ≡ b ℕ.+ a ⊖ c
distribˡ-⊖-+-pos _ zero    zero    = refl
distribˡ-⊖-+-pos _ zero    (suc _) = refl
distribˡ-⊖-+-pos _ (suc _) zero    = refl
distribˡ-⊖-+-pos a (suc b) (suc c) = distribˡ-⊖-+-pos a b c

distribˡ-⊖-+-neg : ∀ a b c → b ⊖ c + -[1+ a ] ≡ b ⊖ (suc c ℕ.+ a)
distribˡ-⊖-+-neg _ zero    zero    = refl
distribˡ-⊖-+-neg _ zero    (suc _) = refl
distribˡ-⊖-+-neg _ (suc _) zero    = refl
distribˡ-⊖-+-neg a (suc b) (suc c) = distribˡ-⊖-+-neg a b c

distribʳ-⊖-+-pos : ∀ a b c → + a + (b ⊖ c) ≡ a ℕ.+ b ⊖ c
distribʳ-⊖-+-pos a b c = begin
  + a + (b ⊖ c) ≡⟨ +-comm (+ a) (b ⊖ c) ⟩
  (b ⊖ c) + + a ≡⟨ distribˡ-⊖-+-pos a b c ⟩
  b ℕ.+ a ⊖ c   ≡⟨ cong (_⊖ c) (ℕₚ.+-comm b a) ⟩
  a ℕ.+ b ⊖ c   ∎ where open ≡-Reasoning

distribʳ-⊖-+-neg : ∀ a b c → -[1+ a ] + (b ⊖ c) ≡ b ⊖ (suc a ℕ.+ c)
distribʳ-⊖-+-neg a b c = begin
  -[1+ a ] + (b ⊖ c) ≡⟨ +-comm -[1+ a ] (b ⊖ c) ⟩
  (b ⊖ c) + -[1+ a ] ≡⟨ distribˡ-⊖-+-neg a b c ⟩
  b ⊖ suc (c ℕ.+ a)  ≡⟨ cong (λ x → b ⊖ suc x) (ℕₚ.+-comm c a) ⟩
  b ⊖ suc (a ℕ.+ c)  ∎ where open ≡-Reasoning

+-assoc : Associative _+_
+-assoc +0 y z rewrite +-identityˡ      y  | +-identityˡ (y + z) = refl
+-assoc x +0 z rewrite +-identityʳ  x      | +-identityˡ      z  = refl
+-assoc x y +0 rewrite +-identityʳ (x + y) | +-identityʳ  y      = refl
+-assoc -[1+ a ] -[1+ b ] +[1+ c ] = sym (distribʳ-⊖-+-neg a c b)
+-assoc -[1+ a ] +[1+ b ] +[1+ c ] = distribˡ-⊖-+-pos (suc c) b a
+-assoc +[1+ a ] -[1+ b ] -[1+ c ] = distribˡ-⊖-+-neg c a b
+-assoc +[1+ a ] -[1+ b ] +[1+ c ]
  rewrite distribˡ-⊖-+-pos (suc c) a b
        | distribʳ-⊖-+-pos (suc a) c b
        | sym (ℕₚ.+-assoc a 1 c)
        | ℕₚ.+-comm a 1
        = refl
+-assoc +[1+ a ] +[1+ b ] -[1+ c ]
  rewrite distribʳ-⊖-+-pos (suc a) b c
        | sym (ℕₚ.+-assoc a 1 b)
        | ℕₚ.+-comm a 1
        = refl
+-assoc -[1+ a ] -[1+ b ] -[1+ c ]
  rewrite sym (ℕₚ.+-assoc a 1 (b ℕ.+ c))
        | ℕₚ.+-comm a 1
        | ℕₚ.+-assoc a b c
        = refl
+-assoc -[1+ a ] +[1+ b ] -[1+ c ]
  rewrite distribʳ-⊖-+-neg a b c
        | distribˡ-⊖-+-neg c b a
        = refl
+-assoc +[1+ a ] +[1+ b ] +[1+ c ]
  rewrite ℕₚ.+-assoc (suc a) (suc b) (suc c)
        = refl

+-inverseˡ : LeftInverse +0 -_ _+_
+-inverseˡ -[1+ n ] = n⊖n≡0 n
+-inverseˡ +0       = refl
+-inverseˡ +[1+ n ] = n⊖n≡0 n

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

+-isAbelianGroup : IsAbelianGroup _+_ +0 (-_)
+-isAbelianGroup = record
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
  { isAbelianGroup = +-isAbelianGroup
  }

------------------------------------------------------------------------
-- Properties of _+_ and +_/-_.

pos-+-commute : ℕtoℤ.Homomorphic₂ +_ ℕ._+_ _+_
pos-+-commute zero    n = refl
pos-+-commute (suc m) n = cong sucℤ (pos-+-commute m n)

neg-distrib-+ : ∀ m n → - (m + n) ≡ (- m) + (- n)
neg-distrib-+ +0        +0        = refl
neg-distrib-+ +0        +[1+ n ]  = refl
neg-distrib-+ +[1+ m ]  +0        = cong -[1+_] (ℕₚ.+-identityʳ m)
neg-distrib-+ +[1+ m ]  +[1+ n ]  = cong -[1+_] (ℕₚ.+-suc m n)
neg-distrib-+ -[1+ m ]  -[1+ n ]  = cong (λ v → + suc v) (sym (ℕₚ.+-suc m n))
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

+-pos-monoʳ-≤ : ∀ n → (_+_ (+ n)) Preserves _≤_ ⟶ _≤_
+-pos-monoʳ-≤ n {_}         (-≤- o≤m) = ⊖-monoʳ-≥-≤ n (s≤s o≤m)
+-pos-monoʳ-≤ n { -[1+ m ]} -≤+       = ≤-trans (m⊖n≤m n (suc m)) (+≤+ (ℕₚ.m≤m+n n _))
+-pos-monoʳ-≤ n {_}         (+≤+ m≤o) = +≤+ (ℕₚ.+-monoʳ-≤ n m≤o)

+-neg-monoʳ-≤ : ∀ n → (_+_ (-[1+ n ])) Preserves _≤_ ⟶ _≤_
+-neg-monoʳ-≤ n {_} {_}   (-≤- n≤m) = -≤- (ℕₚ.+-monoʳ-≤ (suc n) n≤m)
+-neg-monoʳ-≤ n {_} {+ m} -≤+       = ≤-trans (-≤- (ℕₚ.m≤m+n (suc n) _)) (-1+m≤n⊖m (suc n) m)
+-neg-monoʳ-≤ n {_} {_}   (+≤+ m≤n) = ⊖-monoˡ-≤ (suc n) m≤n

+-monoʳ-≤ : ∀ n → (_+_ n) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ (+ n)    = +-pos-monoʳ-≤ n
+-monoʳ-≤ -[1+ n ] = +-neg-monoʳ-≤ n

+-monoˡ-≤ : ∀ n → (_+ n) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ n {i} {j} i≤j
  rewrite +-comm i n
        | +-comm j n
        = +-monoʳ-≤ n i≤j

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {m} {n} {i} {j} m≤n i≤j = begin
  m + i ≤⟨ +-monoˡ-≤ i m≤n ⟩
  n + i ≤⟨ +-monoʳ-≤ n i≤j ⟩
  n + j ∎
  where open ≤-Reasoning

≤-steps : ∀ {m n} p → m ≤ n → m ≤ + p + n
≤-steps p m≤n = subst (_≤ _) (+-identityˡ _) (+-mono-≤ (+≤+ z≤n) m≤n)

m≤m+n : ∀ {m} n → m ≤ m + + n
m≤m+n {m} n = begin
  m       ≡⟨ sym (+-identityʳ m) ⟩
  m + + 0 ≤⟨ +-monoʳ-≤ m (+≤+ z≤n) ⟩
  m + + n ∎
  where open ≤-Reasoning

n≤m+n : ∀ m {n} → n ≤ + m + n
n≤m+n m {n} rewrite +-comm (+ m) n = m≤m+n m

------------------------------------------------------------------------
-- Properties of _+_ and _<_

+-monoʳ-< : ∀ n → (_+_ n) Preserves _<_ ⟶ _<_
+-monoʳ-< (+ n)    {_} {_}   (-<- o<m) = ⊖-monoʳ->-< n (s≤s o<m)
+-monoʳ-< (+ n)    {_} {_}   -<+       = <-≤-trans (m⊖1+n<m n _) (+≤+ (ℕₚ.m≤m+n n _))
+-monoʳ-< (+ n)    {_} {_}   (+<+ m<o) = +<+ (ℕₚ.+-monoʳ-< n m<o)
+-monoʳ-< -[1+ n ] {_} {_}   (-<- o<m) = -<- (ℕₚ.+-monoʳ-< (suc n) o<m)
+-monoʳ-< -[1+ n ] {_} {+ o} -<+       = <-≤-trans (-<- (ℕₚ.m≤m+n (suc n) _)) (-[1+m]≤n⊖m+1 n o)
+-monoʳ-< -[1+ n ] {_} {_}   (+<+ m<o) = ⊖-monoˡ-< (suc n) m<o

+-monoˡ-< : ∀ n → (_+ n) Preserves _<_ ⟶ _<_
+-monoˡ-< n {i} {j} i<j
  rewrite +-comm i n
        | +-comm j n
        = +-monoʳ-< n i<j

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< {m} {n} {i} {j} m<n i<j = begin-strict
  m + i <⟨ +-monoˡ-< i m<n ⟩
  n + i <⟨ +-monoʳ-< n i<j ⟩
  n + j ∎
  where open ≤-Reasoning

+-mono-≤-< : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {m} {n} {i} m≤n i<j = ≤-<-trans (+-monoˡ-≤ i m≤n) (+-monoʳ-< n i<j)

+-mono-<-≤ : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {m} {n} {i} m<n i≤j = <-≤-trans (+-monoˡ-< i m<n) (+-monoʳ-≤ n i≤j)

------------------------------------------------------------------------
-- Properties of _-_
------------------------------------------------------------------------

neg-minus-pos : ∀ x y → -[1+ x ] - (+ y) ≡ -[1+ (y ℕ.+ x) ]
neg-minus-pos x       zero    = refl
neg-minus-pos zero    (suc y) = cong (-[1+_] ∘ suc) (sym (ℕₚ.+-identityʳ y))
neg-minus-pos (suc x) (suc y) = cong (-[1+_] ∘ suc) (ℕₚ.+-comm (suc x) y)

+-minus-telescope : ∀ x y z → (x - y) + (y - z) ≡ x - z
+-minus-telescope x y z = begin
  (x - y) + (y - z)   ≡⟨ +-assoc x (- y) (y - z) ⟩
  x + (- y + (y - z)) ≡⟨ cong (λ v → x + v) (sym (+-assoc (- y) y _)) ⟩
  x + ((- y + y) - z) ≡⟨ sym (+-assoc x (- y + y) (- z)) ⟩
  x + (- y + y) - z   ≡⟨ cong (λ a → x + a - z) (+-inverseˡ y) ⟩
  x + +0 - z          ≡⟨ cong (_- z) (+-identityʳ x) ⟩
  x - z               ∎ where open ≡-Reasoning

[+m]-[+n]≡m⊖n : ∀ x y → (+ x) - (+ y) ≡ x ⊖ y
[+m]-[+n]≡m⊖n zero    zero    = refl
[+m]-[+n]≡m⊖n zero    (suc y) = refl
[+m]-[+n]≡m⊖n (suc x) zero    = cong (+_ ∘ suc) (ℕₚ.+-identityʳ x)
[+m]-[+n]≡m⊖n (suc x) (suc y) = refl

∣m-n∣≡∣n-m∣ : (x y : ℤ) → ∣ x - y ∣ ≡ ∣ y - x ∣
∣m-n∣≡∣n-m∣ -[1+ x ] -[1+ y ] = ∣m⊖n∣≡∣n⊖m∣ y x
∣m-n∣≡∣n-m∣ -[1+ x ] (+ y)    = begin
  ∣ -[1+ x ] - (+ y) ∣   ≡⟨ cong ∣_∣ (neg-minus-pos x y) ⟩
  suc (y ℕ.+ x)          ≡⟨ sym (ℕₚ.+-suc y x) ⟩
  y ℕ.+ suc x            ∎ where open ≡-Reasoning
∣m-n∣≡∣n-m∣ (+ x)    -[1+ y ] = begin
  x ℕ.+ suc y            ≡⟨ ℕₚ.+-suc x y ⟩
  suc (x ℕ.+ y)          ≡⟨ cong ∣_∣ (sym (neg-minus-pos y x)) ⟩
  ∣ -[1+ y ] + - (+ x) ∣ ∎ where open ≡-Reasoning
∣m-n∣≡∣n-m∣ (+ x)     (+ y) = begin
  ∣ (+ x) - (+ y) ∣ ≡⟨ cong ∣_∣ ([+m]-[+n]≡m⊖n x y) ⟩
  ∣ x ⊖ y ∣         ≡⟨ ∣m⊖n∣≡∣n⊖m∣ x y ⟩
  ∣ y ⊖ x ∣         ≡⟨ cong ∣_∣ (sym ([+m]-[+n]≡m⊖n y x)) ⟩
  ∣ (+ y) - (+ x) ∣ ∎ where open ≡-Reasoning

m≡n⇒m-n≡0 : ∀ m n → m ≡ n → m - n ≡ + 0
m≡n⇒m-n≡0 m m refl = +-inverseʳ m

m-n≡0⇒m≡n : ∀ m n → m - n ≡ + 0 → m ≡ n
m-n≡0⇒m≡n m n m-n≡0 = begin
  m             ≡⟨ sym (+-identityʳ m) ⟩
  m + + 0       ≡⟨ cong (_+_ m) (sym (+-inverseˡ n)) ⟩
  m + (- n + n) ≡⟨ sym (+-assoc m (- n) n) ⟩
  (m - n) + n   ≡⟨ cong (_+ n) m-n≡0 ⟩
  + 0 + n       ≡⟨ +-identityˡ n ⟩
  n             ∎ where open ≡-Reasoning

≤-steps-neg : ∀ {m n} p → m ≤ n → m - + p ≤ n
≤-steps-neg {m}         zero    m≤n rewrite +-identityʳ m = m≤n
≤-steps-neg {+ m}       (suc p) m≤n = ≤-trans (m⊖n≤m m (suc p)) m≤n
≤-steps-neg { -[1+ n ]} (suc p) m≤n = ≤-trans (-≤- (ℕₚ.≤-trans (ℕₚ.m≤m+n n p) (ℕₚ.n≤1+n _))) m≤n

neg-mono-≤-≥ : -_ Preserves _≤_ ⟶ _≥_
neg-mono-≤-≥ -≤+             = neg-≤-pos
neg-mono-≤-≥ (-≤- n≤m)       = +≤+ (s≤s n≤m)
neg-mono-≤-≥ (+≤+ z≤n)       = neg-≤-pos
neg-mono-≤-≥ (+≤+ (s≤s m≤n)) = -≤- m≤n

m-n≤m : ∀ m n → m - + n ≤ m
m-n≤m m n = ≤-steps-neg n ≤-refl

m≤n⇒m-n≤0 : ∀ {m n} → m ≤ n → m - n ≤ + 0
m≤n⇒m-n≤0 (-≤+ {n = n})         = ≤-steps-neg n -≤+
m≤n⇒m-n≤0 (-≤- {n = n} n≤m)     = ≤-trans (⊖-monoʳ-≥-≤ n n≤m) (≤-reflexive (n⊖n≡0 n))
m≤n⇒m-n≤0 {n = + 0}     (+≤+ z≤n) = +≤+ z≤n
m≤n⇒m-n≤0 {n = + suc n} (+≤+ z≤n) = -≤+
m≤n⇒m-n≤0 (+≤+ (s≤s {m} m≤n))   = ≤-trans (⊖-monoʳ-≥-≤ m m≤n) (≤-reflexive (n⊖n≡0 m))

m-n≤0⇒m≤n : ∀ {m n} → m - n ≤ + 0 → m ≤ n
m-n≤0⇒m≤n {m} {n} m-n≤0 = begin
  m             ≡⟨ sym (+-identityʳ m) ⟩
  m + + 0       ≡⟨ cong (_+_ m) (sym (+-inverseˡ n)) ⟩
  m + (- n + n) ≡⟨ sym (+-assoc m (- n) n) ⟩
  (m - n) + n   ≤⟨ +-monoˡ-≤ n m-n≤0 ⟩
  + 0 + n       ≡⟨ +-identityˡ n ⟩
  n             ∎
  where open ≤-Reasoning

m≤n⇒0≤n-m : ∀ {m n} → m ≤ n → + 0 ≤ n - m
m≤n⇒0≤n-m {m} {n} m≤n = begin
  + 0   ≡⟨ sym (+-inverseʳ m) ⟩
  m - m ≤⟨ +-monoˡ-≤ (- m) m≤n ⟩
  n - m ∎
  where open ≤-Reasoning

0≤n-m⇒m≤n : ∀ {m n} → + 0 ≤ n - m → m ≤ n
0≤n-m⇒m≤n {m} {n} 0≤n-m = begin
  m             ≡⟨ sym (+-identityˡ m) ⟩
  + 0 + m       ≤⟨ +-monoˡ-≤ m 0≤n-m ⟩
  n - m + m     ≡⟨ +-assoc n (- m) m ⟩
  n + (- m + m) ≡⟨ cong (_+_ n) (+-inverseˡ m) ⟩
  n + + 0       ≡⟨ +-identityʳ n ⟩
  n             ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of suc
------------------------------------------------------------------------

≤-step : ∀ {n m} → n ≤ m → n ≤ sucℤ m
≤-step = ≤-steps 1

n≤1+n : ∀ n → n ≤ sucℤ n
n≤1+n n = ≤-steps 1 ≤-refl

suc-+ : ∀ m n → + suc m + n ≡ sucℤ (+ m + n)
suc-+ m (+ n)      = refl
suc-+ m (-[1+ n ]) = sym (distribʳ-⊖-+-pos 1 m (suc n))

n≢1+n : ∀ {n} → n ≢ sucℤ n
n≢1+n {+ _}           ()
n≢1+n { -[1+ 0 ]}     ()
n≢1+n { -[1+ suc n ]} ()

1-[1+n]≡-n : ∀ n → sucℤ -[1+ n ] ≡ - (+ n)
1-[1+n]≡-n zero    = refl
1-[1+n]≡-n (suc n) = refl

suc-mono : sucℤ Preserves _≤_ ⟶ _≤_
suc-mono (-≤+ {m}) = 0⊖m≤+ m
suc-mono (-≤- n≤m) = ⊖-monoʳ-≥-≤ zero n≤m
suc-mono (+≤+ m≤n) = +≤+ (s≤s m≤n)

m+1≤n⇒m<n : ∀ {m n} → sucℤ m ≤ n → m < n
m+1≤n⇒m<n {+ m}           {+ _}       (+≤+ m≤n) = +<+ m≤n
m+1≤n⇒m<n { -[1+ 0 ]}     {+ n}       p         = -<+
m+1≤n⇒m<n { -[1+ suc m ]} {+ n}       -≤+       = -<+
m+1≤n⇒m<n { -[1+ suc m ]} { -[1+ n ]} (-≤- n≤m) = -<- (ℕ.s≤s n≤m)

m<n⇒m+1≤n : ∀ {m n} → m < n → sucℤ m ≤ n
m<n⇒m+1≤n {+ _}           {+ _}       (+<+ m<n) = +≤+ m<n
m<n⇒m+1≤n { -[1+ 0 ]}     {+ _}       -<+       = +≤+ z≤n
m<n⇒m+1≤n { -[1+ suc m ]} { -[1+ _ ]} (-<- n<m) = -≤- (ℕ.≤-pred n<m)
m<n⇒m+1≤n { -[1+ suc m ]} {+ _}       -<+       = -≤+

------------------------------------------------------------------------
-- Properties of pred
------------------------------------------------------------------------

suc-pred : ∀ m → sucℤ (pred m) ≡ m
suc-pred m = begin
  sucℤ (pred m) ≡⟨ sym (+-assoc (+ 1) (- + 1) m) ⟩
  + 0 + m       ≡⟨ +-identityˡ m ⟩
  m             ∎ where open ≡-Reasoning

pred-suc : ∀ m → pred (sucℤ m) ≡ m
pred-suc m = begin
  pred (sucℤ m) ≡⟨ sym (+-assoc (- + 1) (+ 1) m) ⟩
  + 0 + m       ≡⟨ +-identityˡ m ⟩
  m             ∎ where open ≡-Reasoning

+-pred : ∀ m n → m + pred n ≡ pred (m + n)
+-pred m n = begin
  m + (-[1+ 0 ] + n) ≡⟨ sym (+-assoc m -[1+ 0 ] n) ⟩
  m + -[1+ 0 ] + n   ≡⟨ cong (_+ n) (+-comm m -[1+ 0 ]) ⟩
  -[1+ 0 ] + m + n   ≡⟨ +-assoc -[1+ 0 ] m n ⟩
  -[1+ 0 ] + (m + n) ∎ where open ≡-Reasoning

pred-+ : ∀ m n → pred m + n ≡ pred (m + n)
pred-+ m n = begin
  pred m + n   ≡⟨ +-comm (pred m) n ⟩
  n + pred m   ≡⟨ +-pred n m ⟩
  pred (n + m) ≡⟨ cong pred (+-comm n m) ⟩
  pred (m + n) ∎ where open ≡-Reasoning

neg-suc : ∀ m → - + suc m ≡ pred (- + m)
neg-suc zero    = refl
neg-suc (suc m) = refl

minus-suc : ∀ m n → m - + suc n ≡ pred (m - + n)
minus-suc m n = begin
  m + - + suc n      ≡⟨ cong (_+_ m) (neg-suc n) ⟩
  m + pred (- (+ n)) ≡⟨ +-pred m (- + n) ⟩
  pred (m - + n)     ∎ where open ≡-Reasoning

m≤pred[n]⇒m<n : ∀ {m n} → m ≤ pred n → m < n
m≤pred[n]⇒m<n {m} { + n}      m≤predn = ≤-<-trans m≤predn (m⊖1+n<m n 0)
m≤pred[n]⇒m<n {m} { -[1+ n ]} m≤predn = ≤-<-trans m≤predn (-<- ℕₚ.≤-refl)

m<n⇒m≤pred[n] : ∀ {m n} → m < n → m ≤ pred n
m<n⇒m≤pred[n] {_} { +0}       -<+       = -≤- z≤n
m<n⇒m≤pred[n] {_} { +[1+ n ]} -<+       = -≤+
m<n⇒m≤pred[n] {_} { +[1+ n ]} (+<+ m<n) = +≤+ (ℕₚ.≤-pred m<n)
m<n⇒m≤pred[n] {_} { -[1+ n ]} (-<- n<m) = -≤- n<m

≤-step-neg : ∀ {m n} → m ≤ n → pred m ≤ n
≤-step-neg -≤+               = -≤+
≤-step-neg (-≤- n≤m)         = -≤- (ℕₚ.≤-step n≤m)
≤-step-neg (+≤+ z≤n)         = -≤+
≤-step-neg (+≤+ (s≤s m≤n)) = +≤+ (ℕₚ.≤-step m≤n)

pred-mono : pred Preserves _≤_ ⟶ _≤_
pred-mono (-≤+ {n = 0})     = -≤- z≤n
pred-mono (-≤+ {n = suc n}) = -≤+
pred-mono (-≤- n≤m)         = -≤- (s≤s n≤m)
pred-mono (+≤+ m≤n)         = ⊖-monoˡ-≤ 1 m≤n

------------------------------------------------------------------------
-- Properties of _*_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties

*-comm : Commutative _*_
*-comm -[1+ a ] -[1+ b ] rewrite ℕₚ.*-comm (suc a) (suc b) = refl
*-comm -[1+ a ] (+   b ) rewrite ℕₚ.*-comm (suc a) b       = refl
*-comm (+   a ) -[1+ b ] rewrite ℕₚ.*-comm a       (suc b) = refl
*-comm (+   a ) (+   b ) rewrite ℕₚ.*-comm a       b       = refl

*-identityˡ : LeftIdentity (+ 1) _*_
*-identityˡ -[1+ n ] rewrite ℕₚ.+-identityʳ n = refl
*-identityˡ +0    = refl
*-identityˡ +[1+ n ] rewrite ℕₚ.+-identityʳ n = refl

*-identityʳ : RightIdentity (+ 1) _*_
*-identityʳ = comm+idˡ⇒idʳ *-comm *-identityˡ

*-identity : Identity (+ 1) _*_
*-identity = *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero +0 _*_
*-zeroˡ n = refl

*-zeroʳ : RightZero +0 _*_
*-zeroʳ = comm+zeˡ⇒zeʳ *-comm *-zeroˡ

*-zero : Zero +0 _*_
*-zero = *-zeroˡ , *-zeroʳ

private
  lemma : ∀ a b c → c ℕ.+ (b ℕ.+ a ℕ.* suc b) ℕ.* suc c
                  ≡ c ℕ.+ b ℕ.* suc c ℕ.+ a ℕ.* suc (c ℕ.+ b ℕ.* suc c)
  lemma =
    solve 3 (λ a b c → c :+ (b :+ a :* (con 1 :+ b)) :* (con 1 :+ c)
                    := c :+ b :* (con 1 :+ c) :+
                       a :* (con 1 :+ (c :+ b :* (con 1 :+ c))))
            refl

*-assoc : Associative _*_
*-assoc +0 _ _ = refl
*-assoc x +0 z rewrite ℕₚ.*-zeroʳ ∣ x ∣ = refl
*-assoc x y +0 rewrite
    ℕₚ.*-zeroʳ ∣ y ∣
  | ℕₚ.*-zeroʳ ∣ x ∣
  | ℕₚ.*-zeroʳ ∣ sign x 𝕊* sign y ◃ ∣ x ∣ ℕ.* ∣ y ∣ ∣
  = refl
*-assoc -[1+ a ] -[1+ b ] +[1+ c ] = cong (+_ ∘ suc) (lemma a b c)
*-assoc -[1+ a ] +[1+ b ] -[1+ c ] = cong (+_ ∘ suc) (lemma a b c)
*-assoc +[1+ a ] +[1+ b ] +[1+ c ] = cong (+_ ∘ suc) (lemma a b c)
*-assoc +[1+ a ] -[1+ b ] -[1+ c ] = cong (+_ ∘ suc) (lemma a b c)
*-assoc -[1+ a ] -[1+ b ] -[1+ c ] = cong -[1+_] (lemma a b c)
*-assoc -[1+ a ] +[1+ b ] +[1+ c ] = cong -[1+_] (lemma a b c)
*-assoc +[1+ a ] -[1+ b ] +[1+ c ] = cong -[1+_] (lemma a b c)
*-assoc +[1+ a ] +[1+ b ] -[1+ c ] = cong -[1+_] (lemma a b c)

private

  -- lemma used to prove distributivity.
  distrib-lemma :
    ∀ a b c → (c ⊖ b) * -[1+ a ] ≡ a ℕ.+ b ℕ.* suc a ⊖ (a ℕ.+ c ℕ.* suc a)
  distrib-lemma a b c
    rewrite +-cancelˡ-⊖ a (b ℕ.* suc a) (c ℕ.* suc a)
          | ⊖-swap (b ℕ.* suc a) (c ℕ.* suc a)
    with b ℕ.≤? c
  ... | yes b≤c
    rewrite ⊖-≥ b≤c
          | ⊖-≥ (ℕₚ.*-mono-≤ b≤c (ℕₚ.≤-refl {x = suc a}))
          | -◃n≡-n ((c ∸ b) ℕ.* suc a)
          | ℕₚ.*-distribʳ-∸ (suc a) c b
          = refl
  ... | no b≰c
    rewrite sign-⊖-≰ b≰c
          | ∣⊖∣-≰ b≰c
          | +◃n≡+n ((b ∸ c) ℕ.* suc a)
          | ⊖-≰ (b≰c ∘ ℕₚ.*-cancelʳ-≤ b c a)
          | neg-involutive (+ (b ℕ.* suc a ∸ c ℕ.* suc a))
          | ℕₚ.*-distribʳ-∸ (suc a) b c
          = refl

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ +0 y z
  rewrite ℕₚ.*-zeroʳ ∣ y ∣
        | ℕₚ.*-zeroʳ ∣ z ∣
        | ℕₚ.*-zeroʳ ∣ y + z ∣
        = refl
*-distribʳ-+ x +0 z
  rewrite +-identityˡ z
        | +-identityˡ (sign z 𝕊* sign x ◃ ∣ z ∣ ℕ.* ∣ x ∣)
        = refl
*-distribʳ-+ x y +0
  rewrite +-identityʳ y
        | +-identityʳ (sign y 𝕊* sign x ◃ ∣ y ∣ ℕ.* ∣ x ∣)
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
*-distribʳ-+ (+ suc a) -[1+ b ] (+ suc c) with b ℕ.≤? c
... | yes b≤c
  rewrite +-cancelˡ-⊖ a (c ℕ.* suc a) (b ℕ.* suc a)
        | ⊖-≥ b≤c
        | +-comm (- (+ (a ℕ.+ b ℕ.* suc a))) (+ (a ℕ.+ c ℕ.* suc a))
        | ⊖-≥ (ℕₚ.*-mono-≤ b≤c (ℕₚ.≤-refl {x = suc a}))
        | ℕₚ.*-distribʳ-∸ (suc a) c b
        | +◃n≡+n (c ℕ.* suc a ∸ b ℕ.* suc a)
        = refl
... | no b≰c
  rewrite +-cancelˡ-⊖ a (c ℕ.* suc a) (b ℕ.* suc a)
        | sign-⊖-≰ b≰c
        | ∣⊖∣-≰ b≰c
        | -◃n≡-n ((b ∸ c) ℕ.* suc a)
        | ⊖-≰ (b≰c ∘ ℕₚ.*-cancelʳ-≤ b c a)
        | ℕₚ.*-distribʳ-∸ (suc a) b c
        = refl
*-distribʳ-+ (+ suc c) (+ suc a) -[1+ b ] with b ℕ.≤? a
... | yes b≤a
  rewrite +-cancelˡ-⊖ c (a ℕ.* suc c) (b ℕ.* suc c)
        | ⊖-≥ b≤a
        | ⊖-≥ (ℕₚ.*-mono-≤ b≤a (ℕₚ.≤-refl {x = suc c}))
        | +◃n≡+n ((a ∸ b) ℕ.* suc c)
        | ℕₚ.*-distribʳ-∸ (suc c) a b
        = refl
... | no b≰a
  rewrite +-cancelˡ-⊖ c (a ℕ.* suc c) (b ℕ.* suc c)
        | sign-⊖-≰ b≰a
        | ∣⊖∣-≰ b≰a
        | ⊖-≰ (b≰a ∘ ℕₚ.*-cancelʳ-≤ b a c)
        | -◃n≡-n ((b ∸ a) ℕ.* suc c)
        | ℕₚ.*-distribʳ-∸ (suc c) b a
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

*-1-isMonoid : IsMonoid _*_ (+ 1)
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ (+ 1)
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = *-comm
  }

+-*-isSemiring : IsSemiring _+_ _*_ +0 (+ 1)
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-0-isCommutativeMonoid
    ; *-isMonoid = *-1-isMonoid
    ; distrib = *-distrib-+
    }
  ; zero = *-zero
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ +0 (+ 1)
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm = *-comm
  }

+-*-isRing : IsRing _+_ _*_ -_ +0 (+ 1)
+-*-isRing = record
  { +-isAbelianGroup = +-isAbelianGroup
  ; *-isMonoid       = *-1-isMonoid
  ; distrib          = *-distrib-+
  ; zero             = *-zero
  }

+-*-isCommutativeRing : IsCommutativeRing _+_ _*_ -_ +0 (+ 1)
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

abs-*-commute : ℤtoℕ.Homomorphic₂ ∣_∣ _*_ ℕ._*_
abs-*-commute i j = abs-◃ _ _

*-cancelʳ-≡ : ∀ i j k → k ≢ + 0 → i * k ≡ j * k → i ≡ j
*-cancelʳ-≡ i j k            ≢0 eq with signAbs k
*-cancelʳ-≡ i j .+0       ≢0 eq | s ◂ zero  = contradiction refl ≢0
*-cancelʳ-≡ i j .(s ◃ suc n) ≢0 eq | s ◂ suc n
  with ∣ s ◃ suc n ∣ | abs-◃ s (suc n) | sign (s ◃ suc n) | sign-◃ s n
...  | .(suc n)      | refl            | .s               | refl =
  ◃-cong (sign-i≡sign-j i j eq) $
         ℕₚ.*-cancelʳ-≡ ∣ i ∣ ∣ j ∣ $ abs-cong eq
  where
  sign-i≡sign-j : ∀ i j →
                  (sign i 𝕊* s) ◃ (∣ i ∣ ℕ.* suc n) ≡
                  (sign j 𝕊* s) ◃ (∣ j ∣ ℕ.* suc n) →
                  sign i ≡ sign j
  sign-i≡sign-j i              j              eq with signAbs i | signAbs j
  sign-i≡sign-j .+0         .+0         eq | s₁ ◂ zero   | s₂ ◂ zero   = refl
  sign-i≡sign-j .+0         .(s₂ ◃ suc n₂) eq | s₁ ◂ zero   | s₂ ◂ suc n₂
    with ∣ s₂ ◃ suc n₂ ∣ | abs-◃ s₂ (suc n₂)
  ... | .(suc n₂) | refl
    with abs-cong {s₁} {sign (s₂ ◃ suc n₂) 𝕊* s} {0} {suc n₂ ℕ.* suc n} eq
  ...   | ()
  sign-i≡sign-j .(s₁ ◃ suc n₁) .+0         eq | s₁ ◂ suc n₁ | s₂ ◂ zero
    with ∣ s₁ ◃ suc n₁ ∣ | abs-◃ s₁ (suc n₁)
  ... | .(suc n₁) | refl
    with abs-cong {sign (s₁ ◃ suc n₁) 𝕊* s} {s₁} {suc n₁ ℕ.* suc n} {0} eq
  ...   | ()
  sign-i≡sign-j .(s₁ ◃ suc n₁) .(s₂ ◃ suc n₂) eq | s₁ ◂ suc n₁ | s₂ ◂ suc n₂
    with ∣ s₁ ◃ suc n₁ ∣ | abs-◃ s₁ (suc n₁)
       | sign (s₁ ◃ suc n₁) | sign-◃ s₁ n₁
       | ∣ s₂ ◃ suc n₂ ∣ | abs-◃ s₂ (suc n₂)
       | sign (s₂ ◃ suc n₂) | sign-◃ s₂ n₂
  ... | .(suc n₁) | refl | .s₁ | refl | .(suc n₂) | refl | .s₂ | refl =
    𝕊ₚ.*-cancelʳ-≡ s₁ s₂ (sign-cong eq)

*-cancelˡ-≡ : ∀ i j k → i ≢ + 0 → i * j ≡ i * k → j ≡ k
*-cancelˡ-≡ i j k
  rewrite *-comm i j
        | *-comm i k
        = *-cancelʳ-≡ j k i

suc-* : ∀ m n → sucℤ m * n ≡ n + m * n
suc-* m n = begin
  sucℤ m * n      ≡⟨ *-distribʳ-+ n (+ 1) m ⟩
  + 1 * n + m * n ≡⟨ cong (_+ m * n) (*-identityˡ n) ⟩
  n + m * n       ∎
  where open ≡-Reasoning

*-suc : ∀ m n → m * sucℤ n ≡ m + m * n
*-suc m n = begin
  m * sucℤ n ≡⟨ *-comm m _ ⟩
  sucℤ n * m ≡⟨ suc-* n m ⟩
  m + n * m  ≡⟨ cong (λ v → m + v) (*-comm n m) ⟩
  m + m * n  ∎
  where open ≡-Reasoning

-1*n≡-n : ∀ n → -[1+ 0 ] * n ≡ - n
-1*n≡-n -[1+ n ] = cong (λ v → + suc v) (ℕₚ.+-identityʳ n)
-1*n≡-n +0       = refl
-1*n≡-n +[1+ n ] = cong -[1+_] (ℕₚ.+-identityʳ n)

------------------------------------------------------------------------
-- Properties of _*_ and +_/-_

pos-distrib-* : ∀ x y → (+ x) * (+ y) ≡ + (x ℕ.* y)
pos-distrib-* zero    y       = refl
pos-distrib-* (suc x) zero    = pos-distrib-* x zero
pos-distrib-* (suc x) (suc y) = refl

neg-distribˡ-* : ∀ x y → - (x * y) ≡ (- x) * y
neg-distribˡ-* x y = begin
  - (x * y)          ≡⟨ sym (-1*n≡-n (x * y)) ⟩
  -[1+ 0 ] * (x * y) ≡⟨ sym (*-assoc -[1+ 0 ] x y) ⟩
  -[1+ 0 ] * x * y   ≡⟨ cong (_* y) (-1*n≡-n x) ⟩
  - x * y            ∎ where open ≡-Reasoning

neg-distribʳ-* : ∀ x y → - (x * y) ≡ x * (- y)
neg-distribʳ-* x y = begin
  - (x * y) ≡⟨ cong -_ (*-comm x y) ⟩
  - (y * x) ≡⟨ neg-distribˡ-* y x ⟩
  - y * x   ≡⟨ *-comm (- y) x ⟩
  x * (- y) ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- Properties of _*_ and _◃_

◃-distrib-* :  ∀ s t m n → (s 𝕊* t) ◃ (m ℕ.* n) ≡ (s ◃ m) * (t ◃ n)
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

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

*-cancelʳ-≤-pos : ∀ m n o → m * + suc o ≤ n * + suc o → m ≤ n
*-cancelʳ-≤-pos (-[1+ m ]) (-[1+ n ]) o (-≤- n≤m) =
  -≤- (ℕₚ.≤-pred (ℕₚ.*-cancelʳ-≤ (suc n) (suc m) o (s≤s n≤m)))
*-cancelʳ-≤-pos -[1+ _ ]   (+ _)      _ _         = -≤+
*-cancelʳ-≤-pos +0      +0      _ _         = +≤+ z≤n
*-cancelʳ-≤-pos +0      (+ suc _)  _ _         = +≤+ z≤n
*-cancelʳ-≤-pos (+ suc _)  +0      _ (+≤+ ())
*-cancelʳ-≤-pos (+ suc m)  (+ suc n)  o (+≤+ m≤n) =
  +≤+ (ℕₚ.*-cancelʳ-≤ (suc m) (suc n) o m≤n)

*-cancelˡ-≤-pos : ∀ m n o → + suc m * n ≤ + suc m * o → n ≤ o
*-cancelˡ-≤-pos m n o
  rewrite *-comm (+ suc m) n
        | *-comm (+ suc m) o
        = *-cancelʳ-≤-pos n o m

*-monoʳ-≤-pos : ∀ n → (_* + suc n) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-pos _ (-≤+             {n = 0})         = -≤+
*-monoʳ-≤-pos _ (-≤+             {n = suc _})     = -≤+
*-monoʳ-≤-pos x (-≤-                         n≤m) =
  -≤- (ℕₚ.≤-pred (ℕₚ.*-mono-≤ (s≤s n≤m) (ℕₚ.≤-refl {x = suc x})))
*-monoʳ-≤-pos k {+ 0} {+ 0}     (+≤+ m≤n) = +≤+ m≤n
*-monoʳ-≤-pos k {+ 0} {+ suc _} (+≤+ m≤n) = +≤+ z≤n
*-monoʳ-≤-pos x (+≤+ {m = suc _} {n = suc _} m≤n) =
  +≤+ ((ℕₚ.*-mono-≤ m≤n (ℕₚ.≤-refl {x = suc x})))

*-monoʳ-≤-non-neg : ∀ n → (_* + n) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤-non-neg (suc n) = *-monoʳ-≤-pos n
*-monoʳ-≤-non-neg zero {i} {j} i≤j
  rewrite *-zeroʳ i
        | *-zeroʳ j
        = +≤+ z≤n

*-monoˡ-≤-non-neg : ∀ n → (+ n *_) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-non-neg n {i} {j} i≤j
  rewrite *-comm (+ n) i
        | *-comm (+ n) j
        = *-monoʳ-≤-non-neg n i≤j

*-monoˡ-≤-pos : ∀ n → (+ suc n *_) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤-pos n = *-monoˡ-≤-non-neg (suc n)

------------------------------------------------------------------------
-- Properties of _*_ and _≤_

*-monoˡ-<-pos : ∀ n → (+[1+ n ] *_) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos n {+ m}       {+ o}       (+<+ m<o) = +◃-mono-< (ℕₚ.+-mono-<-≤ m<o (ℕₚ.*-monoʳ-≤ n (ℕₚ.<⇒≤ m<o)))
*-monoˡ-<-pos n { -[1+ m ]} {+ o}       leq       = -◃<+◃ _ (suc n ℕ.* o)
*-monoˡ-<-pos n { -[1+ m ]} { -[1+ o ]} (-<- o<m) = -<- (ℕₚ.+-mono-<-≤ o<m (ℕₚ.*-monoʳ-≤ n (ℕₚ.<⇒≤ (s≤s o<m))))

*-monoʳ-<-pos : ∀ n → (_* +[1+ n ]) Preserves _<_ ⟶ _<_
*-monoʳ-<-pos n {m} {o} rewrite *-comm m +[1+ n ] | *-comm o +[1+ n ]
  = *-monoˡ-<-pos n

*-cancelˡ-<-non-neg : ∀ n {i j} → + n * i < + n * j → i < j
*-cancelˡ-<-non-neg n {+ i}       {+ j}       leq = +<+ (ℕₚ.*-cancelˡ-< n (+◃-cancel-< leq))
*-cancelˡ-<-non-neg n {+ i}       { -[1+ j ]} leq = contradiction leq +◃≮-◃
*-cancelˡ-<-non-neg n { -[1+ i ]} {+ j}       leq = -<+
*-cancelˡ-<-non-neg n { -[1+ i ]} { -[1+ j ]} leq = -<- (ℕₚ.≤-pred (ℕₚ.*-cancelˡ-< n (neg◃-cancel-< leq)))

*-cancelʳ-<-non-neg : ∀ {i j} n → i * + n < j * + n → i < j
*-cancelʳ-<-non-neg {i} {j} n rewrite *-comm i (+ n) | *-comm j (+ n)
  = *-cancelˡ-<-non-neg n

------------------------------------------------------------------------
-- Properties of _⊓_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties

⊓-comm : Commutative _⊓_
⊓-comm -[1+ m ] -[1+ n ] = cong -[1+_] (ℕₚ.⊔-comm m n)
⊓-comm -[1+ m ] (+ n)    = refl
⊓-comm (+ m)    -[1+ n ] = refl
⊓-comm (+ m)    (+ n)    = cong +_ (ℕₚ.⊓-comm m n)

⊓-assoc : Associative _⊓_
⊓-assoc -[1+ m ] -[1+ n ] -[1+ p ] = cong -[1+_] (ℕₚ.⊔-assoc m n p)
⊓-assoc -[1+ m ] -[1+ n ] (+ p)    = refl
⊓-assoc -[1+ m ] (+ n)    -[1+ p ] = refl
⊓-assoc -[1+ m ] (+ n)    (+ p)    = refl
⊓-assoc (+ m)    -[1+ n ] -[1+ p ] = refl
⊓-assoc (+ m)    -[1+ n ] (+ p)    = refl
⊓-assoc (+ m)    (+ n)    -[1+ p ] = refl
⊓-assoc (+ m)    (+ n)    (+ p)    = cong +_ (ℕₚ.⊓-assoc m n p)

⊓-idem : Idempotent _⊓_
⊓-idem (+ m)    = cong +_ (ℕₚ.⊓-idem m)
⊓-idem -[1+ m ] = cong -[1+_] (ℕₚ.⊔-idem m)

⊓-sel : Selective _⊓_
⊓-sel -[1+ m ] -[1+ n ] = Sum.map (cong -[1+_]) (cong -[1+_]) $ ℕₚ.⊔-sel m n
⊓-sel -[1+ m ] (+ n)    = inj₁ refl
⊓-sel (+ m)    -[1+ n ] = inj₂ refl
⊓-sel (+ m)    (+ n)    = Sum.map (cong ℤ.pos) (cong ℤ.pos) $ ℕₚ.⊓-sel m n

------------------------------------------------------------------------
-- Other properties

m≤n⇒m⊓n≡m : ∀ {m n} → m ≤ n → m ⊓ n ≡ m
m≤n⇒m⊓n≡m -≤+       = refl
m≤n⇒m⊓n≡m (-≤- n≤m) = cong -[1+_] (ℕₚ.m≤n⇒n⊔m≡n n≤m)
m≤n⇒m⊓n≡m (+≤+ m≤n) = cong +_ (ℕₚ.m≤n⇒m⊓n≡m m≤n)

m⊓n≡m⇒m≤n : ∀ {m n} → m ⊓ n ≡ m → m ≤ n
m⊓n≡m⇒m≤n { -[1+ m ]} { -[1+ n ]} eq = -≤- (ℕₚ.n⊔m≡n⇒m≤n (-[1+-injective eq))
m⊓n≡m⇒m≤n { -[1+ m ]} {+ n}       eq = -≤+
m⊓n≡m⇒m≤n {+ m}       {+ n}       eq = +≤+ (ℕₚ.m⊓n≡m⇒m≤n (+-injective eq))

m≥n⇒m⊓n≡n : ∀ {m n} → m ≥ n → m ⊓ n ≡ n
m≥n⇒m⊓n≡n {m} {n} pr rewrite ⊓-comm m n = m≤n⇒m⊓n≡m pr

m⊓n≡n⇒m≥n : ∀ {m n} → m ⊓ n ≡ n → m ≥ n
m⊓n≡n⇒m≥n {m} {n} eq rewrite ⊓-comm m n = m⊓n≡m⇒m≤n eq

m⊓n≤n : ∀ m n → m ⊓ n ≤ n
m⊓n≤n -[1+ m ] -[1+ n ] = -≤- (ℕₚ.n≤m⊔n m n)
m⊓n≤n -[1+ m ] (+ n)    = -≤+
m⊓n≤n (+ m)    -[1+ n ] = -≤- ℕₚ.≤-refl
m⊓n≤n (+ m)    (+ n)    = +≤+ (ℕₚ.m⊓n≤n m n)

m⊓n≤m : ∀ m n → m ⊓ n ≤ m
m⊓n≤m m n rewrite ⊓-comm m n = m⊓n≤n n m

------------------------------------------------------------------------
-- Properties _⊔_
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Algebraic properties

⊔-assoc : Associative _⊔_
⊔-assoc -[1+ m ] -[1+ n ] -[1+ p ] = cong -[1+_] (ℕₚ.⊓-assoc m n p)
⊔-assoc -[1+ m ] -[1+ n ] (+ p)    = refl
⊔-assoc -[1+ m ] (+ n)    -[1+ p ] = refl
⊔-assoc -[1+ m ] (+ n)    (+ p)    = refl
⊔-assoc (+ m)    -[1+ n ] -[1+ p ] = refl
⊔-assoc (+ m)    -[1+ n ] (+ p)    = refl
⊔-assoc (+ m)    (+ n)    -[1+ p ] = refl
⊔-assoc (+ m)    (+ n)    (+ p)    = cong +_ (ℕₚ.⊔-assoc m n p)

⊔-comm : Commutative _⊔_
⊔-comm -[1+ m ] -[1+ n ] = cong -[1+_] (ℕₚ.⊓-comm m n)
⊔-comm -[1+ m ] (+ n)    = refl
⊔-comm (+ m)    -[1+ n ] = refl
⊔-comm (+ m)    (+ n)    = cong +_ (ℕₚ.⊔-comm m n)

⊔-idem : Idempotent _⊔_
⊔-idem (+ m)    = cong +_ (ℕₚ.⊔-idem m)
⊔-idem -[1+ m ] = cong -[1+_] (ℕₚ.⊓-idem m)

⊔-sel : Selective _⊔_
⊔-sel -[1+ m ] -[1+ n ] = Sum.map (cong -[1+_]) (cong -[1+_]) $ ℕₚ.⊓-sel m n
⊔-sel -[1+ m ] (+ n)    = inj₂ refl
⊔-sel (+ m)    -[1+ n ] = inj₁ refl
⊔-sel (+ m)    (+ n)    = Sum.map (cong ℤ.pos) (cong ℤ.pos) $ ℕₚ.⊔-sel m n

------------------------------------------------------------------------
-- Other properties

m≤n⇒m⊔n≡n : ∀ {m n} → m ≤ n → m ⊔ n ≡ n
m≤n⇒m⊔n≡n -≤+       = refl
m≤n⇒m⊔n≡n (-≤- n≤m) = cong -[1+_] (ℕₚ.m≤n⇒n⊓m≡m n≤m)
m≤n⇒m⊔n≡n (+≤+ m≤n) = cong +_ (ℕₚ.m≤n⇒m⊔n≡n m≤n)

m⊔n≡n⇒m≤n : ∀ {m n} → m ⊔ n ≡ n → m ≤ n
m⊔n≡n⇒m≤n { -[1+ m ]} { -[1+ n ]} eq = -≤- (ℕₚ.m⊓n≡n⇒n≤m (-[1+-injective eq))
m⊔n≡n⇒m≤n { -[1+ m ]} {+ n}       eq = -≤+
m⊔n≡n⇒m≤n {+ m}       {+ n}       eq = +≤+ (ℕₚ.n⊔m≡m⇒n≤m (+-injective eq))

m≥n⇒m⊔n≡m : ∀ {m n} → m ≥ n → m ⊔ n ≡ m
m≥n⇒m⊔n≡m {m} {n} pr rewrite ⊔-comm m n = m≤n⇒m⊔n≡n pr

m⊔n≡m⇒m≥n : ∀ {m n} → m ⊔ n ≡ m → m ≥ n
m⊔n≡m⇒m≥n {m} {n} eq rewrite ⊔-comm m n = m⊔n≡n⇒m≤n eq

m≤m⊔n : ∀ m n → m ≤ m ⊔ n
m≤m⊔n -[1+ m ] -[1+ n ] = -≤- (ℕₚ.m⊓n≤m m n)
m≤m⊔n -[1+ m ] (+ n)    = -≤+
m≤m⊔n (+ m)    -[1+ n ] = +≤+ ℕₚ.≤-refl
m≤m⊔n (+ m)    (+ n)    = +≤+ (ℕₚ.m≤m⊔n m n)

n≤m⊔n : ∀ m n → n ≤ m ⊔ n
n≤m⊔n m n rewrite ⊔-comm m n = m≤m⊔n n m

neg-distrib-⊔-⊓ : ∀ m n → - (m ⊔ n) ≡ - m ⊓ - n
neg-distrib-⊔-⊓ -[1+ m ] -[1+ n ] = refl
neg-distrib-⊔-⊓ -[1+ m ] +0       = refl
neg-distrib-⊔-⊓ -[1+ m ] +[1+ n ] = refl
neg-distrib-⊔-⊓ +0       -[1+ n ] = refl
neg-distrib-⊔-⊓ +0       +0       = refl
neg-distrib-⊔-⊓ +0       +[1+ n ] = refl
neg-distrib-⊔-⊓ +[1+ m ] -[1+ n ] = refl
neg-distrib-⊔-⊓ +[1+ m ] +0       = refl
neg-distrib-⊔-⊓ +[1+ m ] +[1+ n ] = refl

neg-distrib-⊓-⊔ : ∀ m n → - (m ⊓ n) ≡ - m ⊔ - n
neg-distrib-⊓-⊔ -[1+ m ] -[1+ n ] = refl
neg-distrib-⊓-⊔ -[1+ m ] +0       = refl
neg-distrib-⊓-⊔ -[1+ m ] +[1+ n ] = refl
neg-distrib-⊓-⊔ +0       -[1+ n ] = refl
neg-distrib-⊓-⊔ +0       +0       = refl
neg-distrib-⊓-⊔ +0       +[1+ n ] = refl
neg-distrib-⊓-⊔ +[1+ m ] -[1+ n ] = refl
neg-distrib-⊓-⊔ +[1+ m ] +0       = refl
neg-distrib-⊓-⊔ +[1+ m ] +[1+ n ] = refl


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

-- Version 1.0

≰→> = ≰⇒>
{-# WARNING_ON_USAGE ≰→>
"Warning: ≰→> was deprecated in v1.0.
Please use ≰⇒> instead."
#-}
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

-- Not all of the below have deprecation warnings attached as they are
-- reused by other deprecated results.

-<′+ : ∀ {m n} → -[1+ m ] <′ + n
-<′+ {0}     = +≤+ z≤n
-<′+ {suc _} = -≤+
{-# WARNING_ON_USAGE -<′+
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′-irrefl : Irreflexive _≡_ _<′_
<′-irrefl { + n}          refl (+≤+ 1+n≤n) = ℕₚ.<-irrefl refl 1+n≤n
<′-irrefl { -[1+ suc n ]} refl (-≤- 1+n≤n) = ℕₚ.<-irrefl refl 1+n≤n
{-# WARNING_ON_USAGE <′-irrefl
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
>′-irrefl : Irreflexive _≡_ _>′_
>′-irrefl = <′-irrefl ∘ sym
{-# WARNING_ON_USAGE >′-irrefl
"Warning: _>′_ was deprecated in v1.1.
Please use _>_ instead."
#-}
<′-asym : Asymmetric _<′_
<′-asym {+ n}           {+ m}           (+≤+ n<m) (+≤+ m<n) = ℕₚ.<-asym n<m m<n
<′-asym { -[1+ suc n ]} { -[1+ suc m ]} (-≤- n<m) (-≤- m<n) = ℕₚ.<-asym n<m m<n
{-# WARNING_ON_USAGE <′-asym
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
≤-<′-trans : Trans _≤_ _<′_ _<′_
≤-<′-trans { -[1+ m ]} {+ n} {+ p} -≤+ (+≤+ 1+n≤p) = -<′+ {m} {p}
≤-<′-trans {+ m} {+ n} {+ p} (+≤+ m≤n) (+≤+ 1+n≤p) = +≤+ (ℕₚ.≤-trans (ℕ.s≤s m≤n) 1+n≤p)
≤-<′-trans { -[1+ m ]} { -[1+ n ]} (-≤- n≤m) n<p = ≤-trans (⊖-monoʳ-≥-≤ 0 n≤m) n<p
{-# WARNING_ON_USAGE ≤-<′-trans
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′-≤-trans : Trans _<′_ _≤_ _<′_
<′-≤-trans = ≤-trans
{-# WARNING_ON_USAGE <′-≤-trans
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′⇒≤ : ∀ {m n} → m <′ n → m ≤ n
<′⇒≤ m<n =  ≤-trans (n≤1+n _) m<n
{-# WARNING_ON_USAGE <′⇒≤
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′-trans : Transitive _<′_
<′-trans {m} {n} {p} m<n n<p = ≤-<′-trans {m} {n} {p} (<′⇒≤ m<n) n<p
{-# WARNING_ON_USAGE <′-trans
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′-cmp : Trichotomous _≡_ _<′_
<′-cmp (+ m) (+ n) with ℕₚ.<-cmp m n
... | tri< m<n m≢n m≯n =
  tri< (+≤+ m<n)         (m≢n ∘ +-injective) (m≯n ∘ drop‿+≤+)
... | tri≈ m≮n m≡n m≯n =
  tri≈ (m≮n ∘ drop‿+≤+) (cong (+_) m≡n)     (m≯n ∘ drop‿+≤+)
... | tri> m≮n m≢n m>n =
  tri> (m≮n ∘ drop‿+≤+) (m≢n ∘ +-injective) (+≤+ m>n)
<′-cmp (+_ m)       -[1+ 0 ]     = tri> (λ())     (λ()) (+≤+ z≤n)
<′-cmp (+_ m)       -[1+ suc n ] = tri> (λ())     (λ()) -≤+
<′-cmp -[1+ 0 ]     (+ n)        = tri< (+≤+ z≤n) (λ()) (λ())
<′-cmp -[1+ suc m ] (+ n)        = tri< -≤+       (λ()) (λ())
<′-cmp -[1+ 0 ]     -[1+ 0 ]     = tri≈ (λ())     refl  (λ())
<′-cmp -[1+ 0 ]     -[1+ suc n ] = tri> (λ())     (λ()) (-≤- z≤n)
<′-cmp -[1+ suc m ] -[1+ 0 ]     = tri< (-≤- z≤n) (λ()) (λ())
<′-cmp -[1+ suc m ] -[1+ suc n ] with ℕₚ.<-cmp (suc m) (suc n)
... | tri< m<n m≢n m≯n =
  tri> (m≯n ∘ s≤s ∘ drop‿-≤-) (m≢n ∘ -[1+-injective) (-≤- (ℕₚ.≤-pred m<n))
... | tri≈ m≮n m≡n m≯n =
  tri≈ (m≯n ∘ ℕ.s≤s ∘ drop‿-≤-) (cong -[1+_] m≡n) (m≮n ∘ ℕ.s≤s ∘ drop‿-≤-)
... | tri> m≮n m≢n m>n =
  tri< (-≤- (ℕₚ.≤-pred m>n)) (m≢n ∘ -[1+-injective) (m≮n ∘ s≤s ∘ drop‿-≤-)
{-# WARNING_ON_USAGE <′-cmp
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′-isStrictPartialOrder : IsStrictPartialOrder _≡_ _<′_
<′-isStrictPartialOrder = record
  { isEquivalence = isEquivalence
  ; irrefl        = <′-irrefl
  ; trans         = λ {i} → <′-trans {i}
  ; <-resp-≈      = (λ {x} → subst (x <′_)) , subst (_<′ _)
  }
{-# WARNING_ON_USAGE <′-isStrictPartialOrder
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′-strictPartialOrder : StrictPartialOrder _ _ _
<′-strictPartialOrder = record
  { isStrictPartialOrder = <′-isStrictPartialOrder
  }
{-# WARNING_ON_USAGE <′-strictPartialOrder
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<′_
<′-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = λ {i} → <′-trans {i}
  ; compare       = <′-cmp
  }
{-# WARNING_ON_USAGE <′-isStrictTotalOrder
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′-strictTotalOrder : StrictTotalOrder _ _ _
<′-strictTotalOrder = record
  { isStrictTotalOrder = <′-isStrictTotalOrder
  }
{-# WARNING_ON_USAGE <′-strictTotalOrder
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
n≮′n : ∀ {n} → n ≮′ n
n≮′n {+ n}           (+≤+ n<n) =  contradiction n<n ℕₚ.1+n≰n
n≮′n { -[1+ suc n ]} (-≤- n<n) =  contradiction n<n ℕₚ.1+n≰n
{-# WARNING_ON_USAGE n≮′n
"Warning: n≮′n was deprecated in v1.1.
Please use n≮n instead."
#-}
>′⇒≰′ : ∀ {x y} → x >′ y → x ≰ y
>′⇒≰′ {y = y} x>y x≤y = contradiction (<′-≤-trans {i = y} x>y x≤y) n≮′n
{-# WARNING_ON_USAGE >′⇒≰′
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
≰⇒>′ : ∀ {x y} → x ≰ y → x >′ y
≰⇒>′ {+ m}           {+ n}           m≰n =  +≤+ (ℕₚ.≰⇒> (m≰n ∘ +≤+))
≰⇒>′ {+ m}           { -[1+ n ]}     _   =  -<′+ {n} {m}
≰⇒>′ { -[1+ m ]}     {+ _}           m≰n =  contradiction -≤+ m≰n
≰⇒>′ { -[1+ 0 ]}     { -[1+ 0 ]}     m≰n =  contradiction ≤-refl m≰n
≰⇒>′ { -[1+ suc _ ]} { -[1+ 0 ]}     m≰n =  contradiction (-≤- z≤n) m≰n
≰⇒>′ { -[1+ m ]}     { -[1+ suc n ]} m≰n with m ℕ.≤? n
... | yes m≤n  = -≤- m≤n
... | no  m≰n' = contradiction (-≤- (ℕₚ.≰⇒> m≰n')) m≰n
{-# WARNING_ON_USAGE ≰⇒>′
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
<′-irrelevant : Irrelevant _<′_
<′-irrelevant = ≤-irrelevant
{-# WARNING_ON_USAGE <′-irrelevant
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
+-monoˡ-<′ : ∀ n → (_+ n) Preserves _<′_ ⟶ _<′_
+-monoˡ-<′ n {i} {j} i<j
  rewrite sym (+-assoc (+ 1) i n)
          = +-monoˡ-≤ n i<j
{-# WARNING_ON_USAGE +-monoˡ-<′
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
+-monoʳ-<′ : ∀ n → (_+_ n) Preserves _<′_ ⟶ _<′_
+-monoʳ-<′ n {i} {j} i<j
  rewrite +-comm n i
        | +-comm n j
        = +-monoˡ-<′ n {i} {j} i<j
{-# WARNING_ON_USAGE +-monoʳ-<′
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
+-mono-<′ : _+_ Preserves₂ _<′_ ⟶ _<′_ ⟶ _<′_
+-mono-<′ {m} {n} {i} {j} m<n i<j = begin
  sucℤ (m + i) ≤⟨ suc-mono {m + i} (<′⇒≤ (+-monoˡ-<′ i {m} {n} m<n)) ⟩
  sucℤ (n + i) ≤⟨ +-monoʳ-<′ n i<j ⟩
  n + j        ∎
  where open ≤-Reasoning
{-# WARNING_ON_USAGE +-mono-<′
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
+-mono-≤-<′ : _+_ Preserves₂ _≤_ ⟶ _<′_ ⟶ _<′_
+-mono-≤-<′ {m} {n} {i} {j} m≤n i<j = ≤-<′-trans (+-monoˡ-≤ i m≤n) (+-monoʳ-<′ n i<j)
{-# WARNING_ON_USAGE +-mono-≤-<′
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
+-mono-<′-≤ : _+_ Preserves₂ _<′_ ⟶ _≤_ ⟶ _<′_
+-mono-<′-≤ {m} {n} {i} {j} m<n i≤j =
  <′-≤-trans {m + i} {n + i} {n + j} (+-monoˡ-<′ i {m} {n} m<n) (+-monoʳ-≤ n i≤j)
{-# WARNING_ON_USAGE +-mono-<′-≤
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
m≤pred[n]⇒m<′n : ∀ {m n} → m ≤ pred n → m <′ n
m≤pred[n]⇒m<′n {m} {n} m≤predn = begin
  sucℤ m               ≤⟨ +-monoʳ-≤ (+ 1) m≤predn ⟩
  + 1 + pred n         ≡⟨ sym (+-assoc (+ 1) -[1+ 0 ] n) ⟩
  (+ 1 + -[1+ 0 ]) + n ≡⟨ cong (_+ n) (+-inverseʳ (+ 1)) ⟩
  + 0 + n              ≡⟨ +-identityˡ n ⟩
  n                    ∎
  where open ≤-Reasoning
{-# WARNING_ON_USAGE m≤pred[n]⇒m<′n
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}
m<′n⇒m≤pred[n] : ∀ {m n} → m <′ n → m ≤ pred n
m<′n⇒m≤pred[n] {m} {n} m<n = begin
  m             ≡⟨ sym (pred-suc m) ⟩
  pred (sucℤ m) ≤⟨ pred-mono m<n ⟩
  pred n        ∎
  where open ≤-Reasoning
{-# WARNING_ON_USAGE m<′n⇒m≤pred[n]
"Warning: _<′_ was deprecated in v1.1.
Please use _<_ instead."
#-}

-- Version 1.2

[1+m]*n≡n+m*n = suc-*
{-# WARNING_ON_USAGE [1+m]*n≡n+m*n
"Warning: [1+m]*n≡n+m*n was deprecated in v1.1.
Please use suc-* instead."
#-}
