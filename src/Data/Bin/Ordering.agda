------------------------------------------------------------------------
-- The Agda standard library
--
-- Ordering on Bin and certain its properties.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Ordering where

open import Data.Bin.Base
open import Data.Bin.Properties
open import Data.Nat as ℕ using (ℕ; z≤n; s≤s)
open import Data.Nat.Properties as ℕₚ using (m+n∸m≡n; m+n∸n≡m)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum
open import Function
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality.Core using (≢-sym; resp₂)
import Relation.Binary.Reasoning.Base.Triple as InequalityReasoning
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

-- The ordering relation

infix 4 _<_ _>_ _≤_ _≮_ _≯_ _≰_ _≱_

data _<_ : Rel Bin 0ℓ  where
  0<even    : ∀ {x} → zero < 2[1+ x ]
  0<odd     : ∀ {x} → zero < 1+[2 x ]
  even<even : ∀ {x y} → x < y → 2[1+ x ] < 2[1+ y ]
  even<odd  : ∀ {x y} → x < y → 2[1+ x ] < 1+[2 y ]
  odd<even  : ∀ {x y} → x < y ⊎ x ≡ y → 1+[2 x ] < 2[1+ y ]
  odd<odd   : ∀ {x y} → x < y → 1+[2 x ] < 1+[2 y ]

  -- In these constructors "even" stands for nonzero even.
{-
Example. Explanation for  even<odd x<y :
2(1+x) < 1+2y  ~  1+2(1+x) ≤ 1+2y  ~  2(1+x) ≤ 2y  ~  1+x ≤ y  ~ x < y

For  odd<even (inj₁ x<y) :    1+2x < 2(1+y)  ~  2(1+x) ≤ 2(1+y)  ~  x ≤ y
-}

_>_ :  Rel Bin 0ℓ
x > y =  y < x

_≤_ :  Rel Bin 0ℓ
x ≤ y =  x < y ⊎ x ≡ y

_≥_ :  Rel Bin 0ℓ
x ≥ y =  y ≤ x

_≮_ :  Rel Bin 0ℓ
x ≮ y =  ¬ (x < y)

_≯_ :  Rel Bin 0ℓ
x ≯ y =  ¬ (x > y)

_≰_ :  Rel Bin 0ℓ
x ≰ y =  ¬ (x ≤ y)

_≱_ :  Rel Bin 0ℓ
x ≱ y =  ¬ (x ≥ y)

_<ₙon_ :  Rel Bin 0ℓ
_<ₙon_ =  ℕ._<_ on toℕ

x≮0 : ∀ {x} → x ≮ zero    -- to use instead of λ()
x≮0 ()

1+[2x]<2[1+x] :  ∀ x → 1+[2 x ] < 2[1+ x ]
1+[2x]<2[1+x] x =  odd<even (inj₂ refl)

<-irrefl : Irreflexive _≡_ _<_
<-irrefl {zero}     {zero}      _  ()
<-irrefl {zero}     {2[1+ _ ]}  ()
<-irrefl {zero}     {1+[2 _ ]}  ()
<-irrefl {2[1+ _ ]} {zero}      ()
<-irrefl {2[1+ x ]} {2[1+ .x ]} refl (even<even x<x) =  <-irrefl refl x<x
<-irrefl {1+[2 x ]} {1+[2 .x ]} refl (odd<odd x<x)   =  <-irrefl refl x<x

<⇒≢ :  _<_ ⇒ _≢_
<⇒≢ x<x refl =  <-irrefl refl x<x

>⇒≢ :  _>_ ⇒ _≢_
>⇒≢ {_} {_} y<x =  ≢-sym (<⇒≢ y<x)

≡⇒≮ :  _≡_ ⇒ _≮_
≡⇒≮ x≡y x<y =  <⇒≢ x<y x≡y

≡⇒≯ :  _≡_ ⇒ _≯_
≡⇒≯ x≡y x>y =  >⇒≢ x>y x≡y

<-trans : Transitive _<_
<-trans {_}             {_}      {zero}     _  ()
<-trans {zero}          {_}      {2[1+ _ ]} _  _  =  0<even
<-trans {_}             {zero}   {_}        ()
<-trans {zero}          {_}      {1+[2 _ ]} _  _  =  0<odd
<-trans (even<even x<y) (even<even y<z)        =  even<even (<-trans x<y y<z)
<-trans (even<even x<y) (even<odd y<z)         =  even<odd (<-trans x<y y<z)
<-trans (even<odd x<y)  (odd<even (inj₁ y<z))  =  even<even (<-trans x<y y<z)
<-trans (even<odd x<y)  (odd<even (inj₂ refl)) =  even<even x<y
<-trans (even<odd x<y)  (odd<odd y<z)          =  even<odd (<-trans x<y y<z)
<-trans (odd<even (inj₁ x<y))  (even<even y<z) =  odd<even (inj₁ (<-trans x<y y<z))
<-trans (odd<even (inj₂ refl)) (even<even x<z) =  odd<even (inj₁ x<z)
<-trans (odd<even (inj₁ x<y))  (even<odd y<z)  =  odd<odd (<-trans x<y y<z)
<-trans (odd<even (inj₂ refl)) (even<odd x<z)  =  odd<odd x<z
<-trans (odd<odd x<y) (odd<even (inj₁ y<z))    =  odd<even (inj₁ (<-trans x<y y<z))
<-trans (odd<odd x<y) (odd<even (inj₂ refl))   =  odd<even (inj₁ x<y)
<-trans (odd<odd x<y) (odd<odd y<z)            =  odd<odd (<-trans x<y y<z)

<⇒≯ : _<_ ⇒ _≯_
<⇒≯ x<y y<x =  <-irrefl refl (<-trans x<y y<x)

>⇒≮ : _>_ ⇒ _≮_
>⇒≮ y<x =  <⇒≯ y<x

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = inj₁

------------------------------------------------------------------------------
-- resolving inequality comparison
------------------------------------------------------------------------------

open Tri

<-cmp :  ∀ (x y) → Tri (x < y) (x ≡ y) (x > y)
<-cmp zero     zero      = tri≈ x≮0    refl  x≮0
<-cmp zero     2[1+ _ ]  = tri< 0<even (λ()) x≮0
<-cmp zero     1+[2 _ ]  = tri< 0<odd  (λ()) x≮0
<-cmp 2[1+ _ ] zero      = tri> (λ())  (λ()) 0<even
<-cmp 2[1+ x ] 2[1+ y ]  with <-cmp x y
... | tri< x<y _    _   =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = even<even x<y
... | tri≈ _   refl _   =  tri≈ (<-irrefl refl) refl (<-irrefl refl)
... | tri> _   _    x>y =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = even<even x>y

<-cmp 2[1+ x ] 1+[2 y ]  with <-cmp x y
... | tri< x<y _    _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = even<odd x<y
... | tri≈ _   refl _ =  tri> (>⇒≮ gt) (>⇒≢ gt) gt
  where
  gt = subst (_< 2[1+ x ]) refl (1+[2x]<2[1+x] x)

... | tri> _ _ y<x =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = odd<even (inj₁ y<x)

<-cmp 1+[2 _ ] zero =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = 0<odd
<-cmp 1+[2 x ] 2[1+ y ]  with <-cmp x y
... | tri< x<y _ _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = odd<even (inj₁ x<y)
... | tri≈ _ x≡y _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = odd<even (inj₂ x≡y)
... | tri> _ _ x>y =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = even<odd x>y

<-cmp 1+[2 x ] 1+[2 y ]  with <-cmp x y
... | tri< x<y _  _   =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = odd<odd x<y
... | tri≈ _ refl _   =  tri≈ (≡⇒≮ refl) refl (≡⇒≯ refl)
... | tri> _ _    x>y =  tri> (>⇒≮ gt) (>⇒≢ gt) gt  where gt = odd<odd x>y

------------------------------------------------------------------------------
-- Several monotonicity proofs for toℕ, fromℕ.
------------------------------------------------------------------------------

toℕ-mono-< :  toℕ Preserves _<_ ⟶ ℕ._<_
toℕ-mono-< {_}        {zero}     ()
toℕ-mono-< {zero}     {2[1+ _ ]} _               =  ℕₚ.0<1+n
toℕ-mono-< {zero}     {1+[2 _ ]} _               =  ℕₚ.0<1+n
toℕ-mono-< {2[1+ x ]} {2[1+ y ]} (even<even x<y) =  begin
  ℕ.suc (2 ℕ.* (ℕ.suc xN))    ≤⟨ ℕₚ.+-monoʳ-≤ 1 (ℕₚ.*-monoʳ-≤ 2 xN<yN) ⟩
  ℕ.suc (2 ℕ.* yN)            ≤⟨ ℕₚ.≤-step ℕₚ.≤-refl ⟩
  2 ℕ.+ (2 ℕ.* yN)            ≡⟨ sym (ℕₚ.*-distribˡ-+ 2 1 yN) ⟩
  2 ℕ.* (ℕ.suc yN)            ∎
  where open ℕₚ.≤-Reasoning;  xN = toℕ x;  yN = toℕ y;  xN<yN = toℕ-mono-< x<y

toℕ-mono-< {2[1+ x ]} {1+[2 y ]} (even<odd x<y) =  ℕₚ.+-monoʳ-≤ 1 (ℕₚ.*-monoʳ-≤ 2 xN<yN)
  where
  xN = toℕ x;  yN = toℕ y;  xN<yN = toℕ-mono-< x<y

toℕ-mono-< {1+[2 x ]} {2[1+ y ]} (odd<even (inj₁ x<y)) =   begin
  ℕ.suc (ℕ.suc (2 ℕ.* xN))    ≡⟨ refl ⟩
  2 ℕ.+ (2 ℕ.* xN)            ≡⟨ sym (ℕₚ.*-distribˡ-+ 2 1 xN) ⟩
  2 ℕ.* (ℕ.suc xN)            ≤⟨ ℕₚ.*-monoʳ-≤ 2 xN<yN ⟩
  2 ℕ.* yN                    ≤⟨ ℕₚ.*-monoʳ-≤ 2 (ℕₚ.≤-step ℕₚ.≤-refl) ⟩
  2 ℕ.* (ℕ.suc yN)            ∎
  where open ℕₚ.≤-Reasoning;  xN = toℕ x;  yN = toℕ y;  xN<yN = toℕ-mono-< x<y

toℕ-mono-< {1+[2 x ]} {2[1+ .x ]} (odd<even (inj₂ refl)) =
  ℕₚ.≤-reflexive (sym (ℕₚ.*-distribˡ-+ 2 1 xN))  where xN = toℕ x

toℕ-mono-< {1+[2 x ]} {1+[2 y ]} (odd<odd x<y) =  ℕₚ.+-monoʳ-< 1 (ℕₚ.*-monoʳ-< 1 xN<yN)
  where xN = toℕ x;  yN = toℕ y;  xN<yN = toℕ-mono-< x<y

fromℕ-mono-< :  fromℕ Preserves ℕ._<_ ⟶ _<_
fromℕ-mono-< {m} {n} m<n =  aux (<-cmp x y)
  where
  open P.≡-Reasoning
  x       = fromℕ m;      y       = fromℕ n
  toℕ-x≡m = toℕ-fromℕ m;  toℕ-y≡n = toℕ-fromℕ n

  aux : Tri (x < y) (x ≡ y) (x > y) → x < y
  aux (tri< x<y _   _) =  x<y
  aux (tri≈ _   x≡y _) =  contradiction m≡n (ℕₚ.<⇒≢ m<n)
    where
    m≡n = begin
      m       ≡⟨ sym toℕ-x≡m ⟩
      toℕ x   ≡⟨ cong toℕ x≡y ⟩
      toℕ y   ≡⟨ toℕ-y≡n ⟩
      n       ∎
  aux (tri> _ _ y<x) =  contradiction m<n (ℕₚ.<⇒≯ n<m)
    where
    yN<xN = toℕ-mono-< y<x;  n<m = subst₂ ℕ._<_ toℕ-y≡n toℕ-x≡m yN<xN


fromℕ-mono-≤ :  fromℕ Preserves ℕ._≤_ ⟶ _≤_
fromℕ-mono-≤ m≤n  with ℕₚ.m≤n⇒m<n∨m≡n m≤n
... | inj₁ m<n =  inj₁ (fromℕ-mono-< m<n)
... | inj₂ m≡n =  inj₂ (cong fromℕ m≡n)

toℕ-mono-≤ :  toℕ Preserves _≤_ ⟶ ℕ._≤_
toℕ-mono-≤ (inj₁ x<y)  =  ℕₚ.<⇒≤ (toℕ-mono-< x<y)
toℕ-mono-≤ (inj₂ refl) =  ℕₚ.≤-reflexive refl

<⇒<ₙon :  ∀ {x y} → x < y → x <ₙon y
<⇒<ₙon x<y =  toℕ-mono-< x<y

<ₙon⇒< :  ∀ {x y} → x <ₙon y → x < y
<ₙon⇒< {x} {y} xN<yN =  subst₂ _<_ (fromℕ-toℕ x) (fromℕ-toℕ y) xN'<yN'
  where
  xN'<yN' = fromℕ-mono-< xN<yN

------------------------------------------------------------------------------
-- Reflexivity, transitivity, antisymmetry
------------------------------------------------------------------------------

≤-refl :  Reflexive _≤_
≤-refl =  inj₂ refl

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive {x} {_} refl =  ≤-refl {x}

≤-trans : Transitive _≤_
≤-trans (inj₁ x<y)  (inj₁ y<z)            =  inj₁ (<-trans x<y y<z)
≤-trans {x} {_} {_} (inj₁ x<y) (inj₂ y≡z) =  inj₁ (subst (x <_) y≡z x<y)
≤-trans {_} {_} {z} (inj₂ x≡y) (inj₁ y<z) =  inj₁ (subst (_< z) (sym x≡y) y<z)
≤-trans             (inj₂ x≡y) (inj₂ y≡z) =  inj₂ (trans x≡y y≡z)

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym (inj₂ x≡y) _          =  x≡y
≤-antisym _          (inj₂ y≡x) =  sym y≡x
≤-antisym (inj₁ x<y) (inj₁ y<x) =  contradiction y<x (<⇒≯ x<y)

------------------------------------------------------------------------------
-- Several other properties for _<_, _≤_.
------------------------------------------------------------------------------

≤→≢→< :  ∀ {x y} → x ≤ y → x ≢ y → x < y
≤→≢→< (inj₁ x<y) _   =  x<y
≤→≢→< (inj₂ x≡y) x≢y =  contradiction x≡y x≢y

0≤x :  ∀ x → zero ≤ x
0≤x zero     =  ≤-refl {zero}
0≤x 2[1+ _ ] =  inj₁ 0<even
0≤x 1+[2 x ] =  inj₁ 0<odd

x≢0⇒x>0 :  ∀ {x} → x ≢ zero → x > zero
x≢0⇒x>0 {zero}     0≢0 =  contradiction refl 0≢0
x≢0⇒x>0 {2[1+ _ ]} _   =  0<even
x≢0⇒x>0 {1+[2 _ ]} _   =  0<odd

x≤0⇒x≡0 :  ∀ {x} → x ≤ zero → x ≡ zero
x≤0⇒x≡0 {x} x≤0 =  ≤-antisym x≤0 (0≤x x)

0<suc :  ∀ x → zero < suc x
0<suc x =  x≢0⇒x>0 (suc≢0 {x})

<⇒≱ :  _<_ ⇒ _≱_
<⇒≱ x<y (inj₁ y<x) =  contradiction y<x (<⇒≯ x<y)
<⇒≱ x<y (inj₂ y≡x) =  contradiction (sym y≡x) (<⇒≢ x<y)

≤⇒≯ :  _≤_ ⇒ _≯_
≤⇒≯ x≤y x>y =  <⇒≱ x>y x≤y

≮⇒≥ :  _≮_ ⇒ _≥_
≮⇒≥ {x} {y} x≮y  with <-cmp x y
... | tri< lt _  _   =  contradiction lt x≮y
... | tri≈ _  eq _   =  ≤-reflexive (sym eq)
... | tri> _  _  y<x =  <⇒≤ y<x

≰⇒> :  _≰_ ⇒ _>_
≰⇒> {x} {y} x≰y  with <-cmp x y
... | tri< lt _  _   =  contradiction (<⇒≤ lt) x≰y
... | tri≈ _  eq _   =  contradiction (≤-reflexive eq) x≰y
... | tri> _  _  x>y =  x>y

≤,≢⇒< :  ∀ {x y} → x ≤ y → x ≢ y → x < y
≤,≢⇒< (inj₁ x<y) _   =  x<y
≤,≢⇒< (inj₂ x≡y) x≢y =  contradiction x≡y x≢y

<-≤-trans :  ∀ {x y z} → x < y → y ≤ z → x < z
<-≤-trans x<y (inj₁ y<z)  =  <-trans x<y y<z
<-≤-trans x<y (inj₂ refl) =  x<y

≤-<-trans :  ∀ {x y z} → x ≤ y → y < z → x < z
≤-<-trans (inj₁ x<y)  y<z =  <-trans x<y y<z
≤-<-trans (inj₂ refl) y<z =  y<z

≡0-by≤ :  ∀ {x y} → x ≤ y → y ≡ zero → x ≡ zero
≡0-by≤ x≤0 refl =  x≤0⇒x≡0 x≤0

≢0-by≤ :  ∀ {x y} → x ≤ y → x ≢ zero → y ≢ zero
≢0-by≤ x≤y x≢0 =  x≢0 ∘ ≡0-by≤ x≤y

_<?_ : Decidable _<_
x <? y  with <-cmp x y
... | tri< lt  _ _ =  yes lt
... | tri≈ ¬lt _ _ =  no ¬lt
... | tri> ¬lt _ _ =  no ¬lt

_≤?_ : Decidable _≤_
x ≤? y  with <-cmp x y
... | tri< lt _  _  =  yes (<⇒≤ {x} {y} lt)
... | tri≈ _  eq _  =  yes (≤-reflexive eq)
... | tri> _  _  gt =  no (<⇒≱ {y} {x} gt)

≤-isPreorder :  IsPreorder _≡_ _≤_
≤-isPreorder =  record
  { isEquivalence = isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

------------------------------------------------------------------------------
-- Several monotonicity proofs for _+_, suc
------------------------------------------------------------------------------

private
  module IneqReasoning = InequalityReasoning {A = Bin} {_≈_ = _≡_} ≤-isPreorder <-trans
                                             (resp₂ _<_) <⇒≤ <-≤-trans ≤-<-trans

+-mono-≤ :  _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' =  begin
  x + y                  ≈⟨ sym $ cong₂ _+_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m + fromℕ n      ≈⟨ sym (fromℕ-homo-+ m n) ⟩
  fromℕ (m ℕ.+ n)        ≤⟨ fromℕ-mono-≤ (ℕₚ.+-mono-≤ m≤m' n≤n') ⟩
  fromℕ (m' ℕ.+ n')      ≈⟨ fromℕ-homo-+ m' n' ⟩
  fromℕ m' + fromℕ n'    ≈⟨ cong₂ _+_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' + y'                ∎
  where
  open IneqReasoning
  m    = toℕ x;             m'   = toℕ x'
  n    = toℕ y;             n'   = toℕ y'
  m≤m' = toℕ-mono-≤ x≤x';   n≤n' = toℕ-mono-≤ y≤y'

+-monoˡ-≤ :  ∀ x → (_+ x) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ x y≤z =  +-mono-≤ y≤z (≤-refl {x})

+-monoʳ-≤ :  ∀ x → (x +_) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ x y≤z =  +-mono-≤ (≤-refl {x}) y≤z

+-mono-<-≤ :  _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {x} {x'} {y} {y'} x<x' y≤y' =  begin-strict
  x + y                  ≈⟨ sym $ cong₂ _+_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m + fromℕ n      ≈⟨ sym (fromℕ-homo-+ m n) ⟩
  fromℕ (m ℕ.+ n)        <⟨ fromℕ-mono-< (ℕₚ.+-mono-<-≤ m<m' n≤n') ⟩
  fromℕ (m' ℕ.+ n')      ≈⟨ fromℕ-homo-+ m' n' ⟩
  fromℕ m' + fromℕ n'    ≈⟨ cong₂ _+_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' + y'                ∎
  where
  open IneqReasoning
  m    = toℕ x;             n    = toℕ y
  m'   = toℕ x';            n'   = toℕ y'
  m<m' = toℕ-mono-< x<x';   n≤n' = toℕ-mono-≤ y≤y'

+-mono-≤-< :  _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {x} {x'} {y} {y'} x≤x' y<y' =  subst₂ _<_ (+-comm y x) (+-comm y' x') y+x<y'+x'
  where
  y+x<y'+x' =  +-mono-<-≤ y<y' x≤x'

+-monoˡ-< :  ∀ x → (_+ x) Preserves _<_ ⟶ _<_
+-monoˡ-< x y<z =  +-mono-<-≤ y<z (≤-refl {x})

+-monoʳ-< :  ∀ x → (x +_) Preserves _<_ ⟶ _<_
+-monoʳ-< x y<z =  +-mono-≤-< (≤-refl {x}) y<z

suc-mono-≤ :  suc Preserves _≤_ ⟶ _≤_
suc-mono-≤ {x} {y} x≤y =  begin
  suc x     ≈⟨ suc≗1+ x ⟩
  1B + x    ≤⟨ +-monoʳ-≤ 1B x≤y ⟩
  1B + y    ≈⟨ sym (suc≗1+ y) ⟩
  suc y     ∎
  where open IneqReasoning

------------------------------------------------------------------------------
-- Some more properties for _<_, _≤_.
------------------------------------------------------------------------------

x≤y+x :  ∀ (x y) → x ≤ y + x
x≤y+x x y =  begin
  x          ≈⟨ sym (+-identityˡ x) ⟩
  zero + x   ≤⟨ +-monoˡ-≤ x (0≤x y) ⟩
  y + x      ∎
  where open IneqReasoning

x≤x+y :  ∀ (x y) → x ≤ x + y
x≤x+y x y =  begin
  x        ≤⟨ x≤y+x x y ⟩
  y + x    ≈⟨ +-comm y x ⟩
  x + y    ∎
  where open IneqReasoning

x<1+x :  ∀ x → x < 1B + x
x<1+x x = begin-strict
  x                 ≈⟨ sym (fromℕ-toℕ x) ⟩
  fromℕ n           <⟨ fromℕ-mono-< (ℕₚ.n<1+n {n}) ⟩
  fromℕ (ℕ.suc n)   ≈⟨ fromℕ-homo-+ 1 n ⟩
  1B + fromℕ n      ≈⟨ cong (1B +_) (fromℕ-toℕ x) ⟩
  1B + x            ∎
  where
  open IneqReasoning;  n = toℕ x

x<x+1 :  ∀ x → x < x + 1B
x<x+1 x =  begin-strict
  x        <⟨ x<1+x x ⟩
  1B + x   ≈⟨ +-comm 1B x ⟩
  x + 1B   ∎
  where open IneqReasoning

x<suc[x] :  ∀ x → x < suc x
x<suc[x] x =  begin-strict
  x        <⟨ x<1+x x ⟩
  1B + x   ≈⟨ sym (suc≗1+ x) ⟩
  suc x    ∎
  where open IneqReasoning

x≤suc[x] :  ∀ x → x ≤ suc x
x≤suc[x] x =  <⇒≤ {x} {suc x} (x<suc[x] x)

x≢suc[x] :  ∀ x → x ≢ suc x
x≢suc[x] =  <⇒≢ ∘ x<suc[x]

pred[x]<x :  ∀ {x} → x ≢ zero → pred x < x
pred[x]<x {x} x≢0 =  begin-strict
  pred x          <⟨ x<suc[x] (pred x) ⟩
  suc (pred x)    ≈⟨ suc-pred x≢0 ⟩
  x               ∎
  where open IneqReasoning

------------------------------------------------------------------------------
-- Monotonicity proofs for _*_, double.
------------------------------------------------------------------------------

*-mono-≤ :  _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
*-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' =  begin
  x * y                  ≈⟨ sym $ cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m * fromℕ n      ≈⟨ sym (fromℕ-homo-* m n) ⟩
  fromℕ (m ℕ.* n)        ≤⟨ fromℕ-mono-≤ (ℕₚ.*-mono-≤ m≤m' n≤n') ⟩
  fromℕ (m' ℕ.* n')      ≈⟨ fromℕ-homo-* m' n' ⟩
  fromℕ m' * fromℕ n'    ≈⟨ cong₂ _*_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' * y'                ∎
  where
  open IneqReasoning
  m    = toℕ x;              m'   = toℕ x'
  n    = toℕ y;              n'   = toℕ y'
  m≤m' = toℕ-mono-≤ x≤x';    n≤n' = toℕ-mono-≤ y≤y'

*-monoʳ-≤ :  ∀ x → (x *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤ x y≤y' =  *-mono-≤ (≤-refl {x}) y≤y'

*-monoˡ-≤ :  ∀ x → (_* x) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤ x y≤y' =  *-mono-≤ y≤y' (≤-refl {x})

*-mono-< :  _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
*-mono-< {x} {x'} {y} {y'} x<x' y<y' =  begin-strict
  x * y                  ≈⟨ sym $ cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m * fromℕ n      ≈⟨ sym (fromℕ-homo-* m n) ⟩
  fromℕ (m ℕ.* n)        <⟨ fromℕ-mono-< (ℕₚ.*-mono-< m<m' n<n') ⟩
  fromℕ (m' ℕ.* n')      ≈⟨ fromℕ-homo-* m' n' ⟩
  fromℕ m' * fromℕ n'    ≈⟨ cong₂ _*_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' * y'                ∎
  where
  open IneqReasoning
  m    = toℕ x;              m'   = toℕ x'
  n    = toℕ y;              n'   = toℕ y'
  m<m' = toℕ-mono-< x<x';    n<n' = toℕ-mono-< y<y'

*-monoʳ-< :  ∀ x → ((suc x) *_) Preserves _<_ ⟶ _<_
*-monoʳ-< x {y} {z} y<z =  begin-strict
  (suc x) * y      ≈⟨ suc-* x y ⟩
  y + xy           <⟨ +-mono-<-≤ y<z xy≤xz ⟩
  z + xz           ≈⟨ sym (suc-* x z) ⟩
  (suc x) * z      ∎
  where
  open IneqReasoning;  xy    = x * y
  xz = x * z;          xy≤xz = *-monoʳ-≤ x (<⇒≤ {y} {z} y<z)

*-monoˡ-< :  ∀ x → (_* (suc x)) Preserves _<_ ⟶ _<_
*-monoˡ-< x {y} {z} y<z = begin-strict
  y * (suc x)   ≈⟨ *-comm y (suc x) ⟩
  (suc x) * y   <⟨ *-monoʳ-< x y<z ⟩
  (suc x) * z   ≈⟨ *-comm (suc x) z ⟩
  z * (suc x)   ∎
  where open IneqReasoning

double-mono-≤ :  double Preserves _≤_ ⟶ _≤_
double-mono-≤ {x} {y} x≤y =  begin
  double x   ≈⟨ double≗2B* x ⟩
  2B * x     ≤⟨ *-monoʳ-≤ 2B x≤y ⟩
  2B * y     ≈⟨ sym (double≗2B* y) ⟩
  double y   ∎
  where open IneqReasoning

double-mono-< :  double Preserves _<_ ⟶ _<_
double-mono-< {x} {y} x<y =  begin-strict
  double x   ≈⟨ double≗2B* x ⟩
  2B * x     <⟨ *-monoʳ-< 1B x<y ⟩
  2B * y     ≈⟨ sym (double≗2B* y) ⟩
  double y   ∎
  where open IneqReasoning

double-back-mono-≤ :  ∀ {x y} → double x ≤ double y → x ≤ y
double-back-mono-≤ {x} {y} 2x≤2y  with <-cmp x y
... | tri< x<y _   _   =  <⇒≤ x<y
... | tri≈ _   x≡y _   =  ≤-reflexive x≡y
... | tri> _   _   x>y =  contradiction 2x≤2y (<⇒≱ 2x>2y)  where 2x>2y = double-mono-< x>y

double-back-mono-< :  ∀ {x y} → double x < double y → x < y
double-back-mono-< {x} {y} 2x<2y  with <-cmp x y
... | tri< x<y _    _   =  x<y
... | tri≈ _   refl _   =  contradiction 2x<2y (<-irrefl refl)
... | tri> _   _    x>y =  contradiction 2x>2y (<⇒≯ 2x<2y)  where
                                                             2x>2y = double-mono-< x>y

------------------------------------------------------------------------------
-- Some more properties for _<_, _≤_.
------------------------------------------------------------------------------

x<double[x] :  ∀ x → x ≢ zero → x < double x
x<double[x] x x≢0 =  begin-strict
  x                 ≈⟨ sym (suc-pred x≢0) ⟩
  suc px            ≈⟨ sym (*-identityʳ (suc px)) ⟩
  suc px * 1B       <⟨ *-monoʳ-< px (x<1+x 1B) ⟩
  suc px * 2B       ≈⟨ *-comm (suc px) 2B ⟩
  2B * suc px       ≈⟨ sym (double≗2B* (suc px)) ⟩
  double (suc px)   ≈⟨ cong double (suc-pred x≢0) ⟩
  double x          ∎
  where open IneqReasoning;  px = pred x

suc[x]≤⇒x< :  ∀ {x y} → suc x ≤ y → x < y
suc[x]≤⇒x< {x} {_} (inj₁ sx<y) =  <-trans (x<suc[x] x) sx<y
suc[x]≤⇒x< {x} {_} (inj₂ sx≡y) =  subst (x <_) sx≡y (x<suc[x] x)

x<⇒suc[x]≤ :  ∀ {x y} → x < y → suc x ≤ y
x<⇒suc[x]≤ {x} {y} x<y =  begin
  suc x                  ≈⟨ sym (fromℕ-toℕ (suc x)) ⟩
  fromℕ (toℕ (suc x))    ≈⟨ cong fromℕ (toℕ-suc x) ⟩
  fromℕ (ℕ.suc m)        ≤⟨ fromℕ-mono-≤ 1+m≤n ⟩
  fromℕ n                ≈⟨ fromℕ-toℕ y ⟩
  y                      ∎
  where open IneqReasoning;  m = toℕ x;  n = toℕ y;  1+m≤n = toℕ-mono-< x<y

suc[x]≤double[x] :  ∀ x → x ≢ zero → suc x ≤ double x
suc[x]≤double[x] x =  x<⇒suc[x]≤ {x} {double x} ∘ x<double[x] x

x≤suc[y]*x :  ∀ (x y) → x ≤ (suc y) * x
x≤suc[y]*x x y =  begin
  x             ≤⟨ x≤x+y x (y * x) ⟩
  x + y * x     ≈⟨ sym (suc-* y x) ⟩
  (suc y) * x   ∎
  where open IneqReasoning

x≤double[x] :  ∀ x → x ≤ double x
x≤double[x] x =  begin
  x         ≤⟨ x≤x+y x x ⟩
  x + x     ≈⟨ sym (double[x]≡x+x x) ⟩
  double x  ∎
  where open IneqReasoning

suc[x]<2[1+x] :  ∀ x → suc x < 2[1+ x ]
suc[x]<2[1+x] x =  begin-strict
  suc x           <⟨ x<double[x] (suc x) suc≢0  ⟩
  double (suc x)  ≈⟨ sym (2[1+_]-as∘ x) ⟩
  2[1+ x ]        ∎
  where open IneqReasoning

x<2[1+x] :  ∀ x → x < 2[1+ x ]
x<2[1+x] x =  <-trans (x<suc[x] x) (suc[x]<2[1+x] x)

x<1+[2x] :  ∀ x → x < 1+[2 x ]
x<1+[2x] x =  begin-strict
  x               <⟨ x<suc[x] x ⟩
  suc x           ≤⟨ suc-mono-≤ (x≤double[x] x) ⟩
  suc (double x)  ≈⟨ sym (1+[2_]-as∘ x) ⟩
  1+[2 x ]        ∎
  where open IneqReasoning

double[x]<1+[2x] :  ∀ x → double x < 1+[2 x ]
double[x]<1+[2x] x =  begin-strict
  double x         <⟨ x<suc[x] (double x) ⟩
  suc (double x)   ≈⟨ sym (1+[2_]-as∘ x) ⟩
  1+[2 x ]         ∎
  where open IneqReasoning

pred-mono-≤ :  pred Preserves _≤_ ⟶ _≤_
pred-mono-≤ {x} {y} x≤y =  begin
  pred x             ≈⟨ cong pred (sym (fromℕ-toℕ x)) ⟩
  pred (fromℕ m)     ≈⟨ sym (fromℕ-pred m) ⟩
  fromℕ (ℕ.pred m)   ≤⟨ fromℕ-mono-≤ (ℕₚ.pred-mono m≤n) ⟩
  fromℕ (ℕ.pred n)   ≈⟨ fromℕ-pred n ⟩
  pred (fromℕ n)     ≈⟨ cong pred (fromℕ-toℕ y) ⟩
  pred y             ∎
  where
  open IneqReasoning;  m = toℕ x;  n = toℕ y;  m≤n = toℕ-mono-≤ x≤y

x<1⇒x≡0 :  ∀ {x} → x < 1B → x ≡ zero
x<1⇒x≡0 {x} x<1 =  x≤0⇒x≡0 x≤0
  where
  open IneqReasoning;  suc[x]≤1 = x<⇒suc[x]≤ {x} {1B} x<1
  x≤0 = begin
    x             ≈⟨ sym (pred-suc x) ⟩
    pred (suc x)  ≤⟨ pred-mono-≤ suc[x]≤1 ⟩
    pred 1B       ≈⟨ refl ⟩
    zero          ∎

------------------------------------------------------------------------------
-- StrictTotalOrder and DecTotalOrder instances for Bin.
------------------------------------------------------------------------------

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence =  isEquivalence
  ; trans         =  λ {x y z} → <-trans {x} {y} {z}
  ; compare       =  <-cmp
  }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { isStrictTotalOrder =  <-isStrictTotalOrder
  }

≤-isPartialOrder :  IsPartialOrder _≡_ _≤_
≤-isPartialOrder =  record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-total :  Relation.Binary.Total _≤_
≤-total x y  with <-cmp x y
... | tri< le _  _  =  inj₁ (<⇒≤ le)
... | tri≈ _  eq _  =  inj₁ (≤-reflexive eq)
... | tri> _  _  gt =  inj₂ (<⇒≤ gt)

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

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }
