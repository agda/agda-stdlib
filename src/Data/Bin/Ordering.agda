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
open import Data.Nat.Properties as ℕp using (m+n∸m≡n; m+n∸n≡m)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; _$_; flip; case_of_; _on_)
open import Level using () renaming (zero to 0ℓ)
open import Relation.Binary using
  (Rel; Reflexive; Symmetric; Antisymmetric; Transitive; Irreflexive; Tri; _⇒_;
   Decidable; _Preserves_⟶_; _Preserves₂_⟶_⟶_; _Respects₂_; IsPreorder;
   IsPartialOrder; Poset; IsTotalOrder; IsDecTotalOrder; DecTotalOrder;
   IsStrictTotalOrder; StrictTotalOrder
  )
open import Relation.Binary.PropositionalEquality as P using
  (_≡_; _≢_; refl; sym; trans; subst; subst₂; cong; cong₂; isEquivalence)
open import Relation.Binary.PropositionalEquality.Core using (≢-sym)
import Relation.Binary.Reasoning.Base.Triple as InequalityReasoning
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open Bin

-- The ordering relation

infix 4 _<_ _>_ _≤_

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

_>_ _≤_ _≥_ _≮_ _≯_ _≰_ _≱_ :  Rel Bin 0ℓ

_>_   =  flip _<_
x ≤ y =  x < y ⊎ x ≡ y
_≥_   =  flip _≤_
_≮_ x =  ¬_ ∘ _<_ x
_≯_ x =  ¬_ ∘ _>_ x
_≰_ x =  ¬_ ∘ _≤_ x
_≱_ x =  ¬_ ∘ _≥_ x

≮0 : ∀ {x} → x ≮ zero    -- to use instead of λ()
≮0 ()

1+[2x]<2[1+x] :  ∀ x → 1+[2 x ] < 2[1+ x ]
1+[2x]<2[1+x] x =  odd<even (inj₂ refl)

<-irrefl : Irreflexive _≡_ _<_

<-irrefl {zero}     {zero}      _  ()
<-irrefl {zero}     {2[1+ _ ]}  ()
<-irrefl {zero}     {1+[2 _ ]}  ()
<-irrefl {2[1+ _ ]} {zero}      ()
<-irrefl {2[1+ x ]} {2[1+ .x ]} refl =  x'≮x'
  where
  x'≮x' : 2[1+ x ] ≮ 2[1+ x ]
  x'≮x' (even<even x<x) =  <-irrefl refl x<x

<-irrefl {1+[2 x ]} {1+[2 .x ]} refl =  x'≮x'
  where
  x'≮x' : 1+[2 x ] ≮ 1+[2 x ]
  x'≮x' (odd<odd x<x) =  <-irrefl refl x<x

<⇒≢ :  _<_ ⇒ _≢_
<⇒≢ {x} {_} x<y x≡y =  <-irrefl {x} {x} refl x<x
  where
  x<x = subst (x <_) (sym x≡y) x<y

>⇒≢ :  _>_ ⇒ _≢_
>⇒≢ {_} {_} y<x =  ≢-sym (<⇒≢ y<x)

≡⇒≮ :  _≡_ ⇒ _≮_
≡⇒≮ x≡y x<y =  <⇒≢ x<y x≡y

≡⇒≯ :  _≡_ ⇒ _≯_
≡⇒≯ x≡y x>y =  >⇒≢ x>y x≡y

<-trans : Transitive _<_
<-trans {_}      {_}      {zero}     _  ()
<-trans {zero}   {_}      {2[1+ _ ]} _  _  =  0<even
<-trans {_}      {zero}   {_}        ()
<-trans {zero}   {_}      {1+[2 _ ]} _  _  =  0<odd

<-trans {2[1+ x ]} {2[1+ y ]} {2[1+ z ]} (even<even x<y) (even<even y<z) =
                                                    even<even (<-trans x<y y<z)
<-trans {2[1+ x ]} {2[1+ y ]} {1+[2 z ]} (even<even x<y) (even<odd y<z) =
                                                    even<odd (<-trans x<y y<z)
<-trans {2[1+ x ]} {1+[2 y ]} {2[1+ z ]} (even<odd x<y) (odd<even (inj₁ y<z)) =
                                                    even<even (<-trans x<y y<z)
<-trans {2[1+ x ]} {1+[2 y ]} {2[1+ .y ]} (even<odd x<y)
                                          (odd<even (inj₂ refl)) =  even<even x<y
<-trans {2[1+ x ]} {1+[2 y ]} {1+[2 z ]} (even<odd x<y) (odd<odd y<z) =
                                                        even<odd (<-trans x<y y<z)
<-trans {1+[2 x ]} {2[1+ y ]} {2[1+ z ]} (odd<even (inj₁ x<y)) (even<even y<z) =
                                                   odd<even (inj₁ (<-trans x<y y<z))
<-trans {1+[2 x ]} {2[1+ .x ]} {2[1+ z ]} (odd<even (inj₂ refl))
                                          (even<even x<z) =  odd<even (inj₁ x<z)
<-trans {1+[2 x ]} {2[1+ y ]} {1+[2 z ]} (odd<even (inj₁ x<y)) (even<odd y<z) =
                                                         odd<odd (<-trans x<y y<z)
<-trans {1+[2 x ]} {2[1+ .x ]} {1+[2 z ]} (odd<even (inj₂ refl)) (even<odd x<z) =
                                                                 odd<odd x<z
<-trans {1+[2 x ]} {1+[2 y ]} {2[1+ z ]} (odd<odd x<y) (odd<even (inj₁ y<z)) =
                                                  odd<even (inj₁ (<-trans x<y y<z))
<-trans {1+[2 x ]} {1+[2 y ]} {2[1+ .y ]} (odd<odd x<y) (odd<even (inj₂ refl)) =
                                                             odd<even (inj₁ x<y)
<-trans {1+[2 x ]} {1+[2 y ]} {1+[2 z ]} (odd<odd x<y) (odd<odd y<z) =
                                                       odd<odd (<-trans x<y y<z)

<⇒≯ : _<_ ⇒ _≯_
<⇒≯ {x} {y} x<y y<x =  <-irrefl refl (<-trans {x} {y} {x} x<y y<x)

>⇒≮ : _>_ ⇒ _≮_
>⇒≮ {x} {y} y<x =  <⇒≯ {y} {x} y<x

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = inj₁

------------------------------------------------------------------------------
-- resolving inequality comparison
------------------------------------------------------------------------------

open Tri

<-cmp :  ∀ (x y) → Tri (x < y) (x ≡ y) (x > y)
<-cmp zero     zero      = tri≈ ≮0     refl  ≮0
<-cmp zero     2[1+ _ ]  = tri< 0<even (λ()) ≮0
<-cmp zero     1+[2 _ ]  = tri< 0<odd  (λ()) ≮0
<-cmp 2[1+ _ ] zero      = tri> (λ())  (λ()) 0<even
<-cmp 2[1+ x ] 2[1+ y ]  with <-cmp x y
... | tri< x<y _   _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)  where lt = even<even x<y
... | tri≈ _   x≡y _ =  tri≈ (<-irrefl eq) eq (<-irrefl (sym eq))
  where
  eq = cong 2[1+_] x≡y
... | tri> _ _ x>y =  tri> (>⇒≮ gt) (>⇒≢ gt) gt
  where
  gt : 2[1+ x ] > 2[1+ y ]
  gt = even<even x>y

<-cmp 2[1+ x ] 1+[2 y ]  with <-cmp x y
... | tri< x<y _    _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)
  where
  lt = even<odd x<y

... | tri≈ _   x≡y _ =  tri> (>⇒≮ gt) (>⇒≢ gt) gt
  where
  1+2x≡1+2y = cong 1+[2_] x≡y;  1+2x<2[1+x] = 1+[2x]<2[1+x] x

  gt : 1+[2 y ] < 2[1+ x ]
  gt = subst (_< 2[1+ x ]) 1+2x≡1+2y (1+[2x]<2[1+x] x)

... | tri> _ _ y<x =  tri> (>⇒≮ gt) (>⇒≢ gt) gt
  where
  gt : 1+[2 y ] < 2[1+ x ]
  gt = odd<even (inj₁ y<x)

<-cmp 1+[2 _ ] zero =  tri> (>⇒≮ gt) (>⇒≢ gt) gt
  where
  gt = 0<odd

<-cmp 1+[2 x ] 2[1+ y ]  with <-cmp x y
... | tri< x<y _ _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)
  where
  lt = odd<even (inj₁ x<y)

... | tri≈ _ x≡y _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)
  where
  lt = odd<even (inj₂ x≡y)

... | tri> _ _ x>y =  tri> (>⇒≮ gt) (>⇒≢ gt) gt
  where
  gt = even<odd x>y

<-cmp 1+[2 x ] 1+[2 y ]  with <-cmp x y
... | tri< x<y _ _ =  tri< lt (<⇒≢ lt) (<⇒≯ lt)
  where
  lt = odd<odd x<y

... | tri≈ _ x≡y _ =  tri≈ (≡⇒≮ eq) eq (≡⇒≯ eq)
  where
  eq = cong 1+[2_] x≡y

... | tri> _ _ x>y =  tri> (>⇒≮ gt) (>⇒≢ gt) gt
  where
  gt = odd<odd x>y

------------------------------------------------------------------------------
-- Several monotonicity proofs for toℕ, fromℕ.
------------------------------------------------------------------------------

toℕ-mono-< :  toℕ Preserves _<_ ⟶ ℕ._<_
toℕ-mono-< {_}        {zero}     ()
toℕ-mono-< {zero}     {2[1+ _ ]} _               =  ℕp.0<1+n
toℕ-mono-< {zero}     {1+[2 _ ]} _               =  ℕp.0<1+n
toℕ-mono-< {2[1+ x ]} {2[1+ y ]} (even<even x<y) =  x'N<y'N
  where
  open ℕp.≤-Reasoning
  xN      = toℕ x
  yN      = toℕ y
  xN<yN   = toℕ-mono-< x<y
  x'N<y'N = begin
    ℕ.suc (2 ℕ.* (ℕ.suc xN))   ≤⟨ ℕp.+-monoʳ-≤ 1 (ℕp.*-monoʳ-≤ 2 xN<yN) ⟩
    ℕ.suc (2 ℕ.* yN)            ≤⟨ ℕp.≤-step ℕp.≤-refl ⟩
    2 ℕ.+ (2 ℕ.* yN)            ≡⟨ sym (ℕp.*-distribˡ-+ 2 1 yN) ⟩
    2 ℕ.* (ℕ.suc yN)            ∎

toℕ-mono-< {2[1+ x ]} {1+[2 y ]} (even<odd x<y) =  x'N<y'N
  where
  xN      = toℕ x
  yN      = toℕ y
  xN<yN   = toℕ-mono-< x<y
  x'N<y'N = ℕp.+-monoʳ-≤ 1 (ℕp.*-monoʳ-≤ 2 xN<yN)

toℕ-mono-< {1+[2 x ]} {2[1+ y ]} (odd<even (inj₁ x<y)) =  x'N<y'N
  where
  open ℕp.≤-Reasoning
  xN      = toℕ x
  yN      = toℕ y
  xN<yN   = toℕ-mono-< x<y
  x'N<y'N = begin
    ℕ.suc (ℕ.suc (2 ℕ.* xN))   ≡⟨ refl ⟩
    2 ℕ.+ (2 ℕ.* xN)            ≡⟨ sym (ℕp.*-distribˡ-+ 2 1 xN) ⟩
    2 ℕ.* (ℕ.suc xN)            ≤⟨ ℕp.*-monoʳ-≤ 2 xN<yN ⟩
    2 ℕ.* yN                     ≤⟨ ℕp.*-monoʳ-≤ 2 (ℕp.≤-step ℕp.≤-refl) ⟩
    2 ℕ.* (ℕ.suc yN)            ∎


toℕ-mono-< {1+[2 x ]} {2[1+ .x ]} (odd<even (inj₂ refl)) =  x'N<y'N
  where
  xN = toℕ x

  x'N<y'N :  ℕ.suc (ℕ.suc (2 ℕ.* xN))  ℕ.≤  2 ℕ.* (ℕ.suc xN)
  x'N<y'N =  ℕp.≤-reflexive (sym (ℕp.*-distribˡ-+ 2 1 xN))

toℕ-mono-< {1+[2 x ]} {1+[2 y ]} (odd<odd x<y) =  x'N<y'N
  where
  xN      = toℕ x
  yN      = toℕ y
  xN<yN   = toℕ-mono-< x<y
  x'N<y'N = ℕp.+-monoʳ-< 1 (ℕp.*-monoʳ-< 1 xN<yN)


fromℕ-mono-< :  fromℕ Preserves ℕ._<_ ⟶ _<_
fromℕ-mono-< {m} {n} m<n =
  let
    open P.≡-Reasoning
    x       = fromℕ m;      y       = fromℕ n
    toℕ-x≡m = toℕ-fromℕ m;  toℕ-y≡n = toℕ-fromℕ n
  in
  case <-cmp x y of \
  { (tri< x<y _   _) → x<y
  ; (tri≈ _   x≡y _) → let m≡n = begin
                            m       ≡⟨ sym toℕ-x≡m ⟩
                            toℕ x   ≡⟨ cong toℕ x≡y ⟩
                            toℕ y   ≡⟨ toℕ-y≡n ⟩
                            n       ∎
                       in
                       contradiction m≡n (ℕp.<⇒≢ m<n)

  ; (tri> _ _ y<x) → let yN<xN = toℕ-mono-< y<x
                         n<m   = subst₂ ℕ._<_ toℕ-y≡n toℕ-x≡m yN<xN
                      in
                      contradiction m<n (ℕp.<⇒≯ n<m)
  }

fromℕ-mono-≤ :  fromℕ Preserves ℕ._≤_ ⟶ _≤_
fromℕ-mono-≤ {m} {n} m≤n  with ℕp.m≤n⇒m<n∨m≡n m≤n
... | inj₁ m<n =  inj₁ (fromℕ-mono-< m<n)
... | inj₂ m≡n =  inj₂ (cong fromℕ m≡n)

toℕ-mono-≤ :  toℕ Preserves _≤_ ⟶ ℕ._≤_
toℕ-mono-≤ {x} {y} (inj₁ x<y) =  ℕp.<⇒≤ (toℕ-mono-< x<y)
toℕ-mono-≤ {x} {y} (inj₂ x≡y) =  ℕp.≤-reflexive (cong toℕ x≡y)

------------------------------------------------------------------------------
-- Reflexivity, transitivity, antisymmetry
------------------------------------------------------------------------------

≤-refl :  Reflexive _≤_
≤-refl =  inj₂ refl

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive {x} {_} refl =  ≤-refl {x}

≤-trans : Transitive _≤_
≤-trans (inj₁ x<y)  (inj₁ y<z)             =  inj₁ (<-trans x<y y<z)
≤-trans {x} {_} {_} (inj₁ x<y)  (inj₂ y≡z) =  inj₁ (subst (x <_) y≡z x<y)
≤-trans {_} {_} {z} (inj₂ x≡y) (inj₁ y<z)  =  inj₁ (subst (_< z) (sym x≡y) y<z)
≤-trans             (inj₂ x≡y) (inj₂ y≡z)  =  inj₂ (trans x≡y y≡z)

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

0≤ :  ∀ x → zero ≤ x
0≤ zero     =  ≤-refl {zero}
0≤ 2[1+ _ ] =  inj₁ 0<even
0≤ 1+[2 x ] =  inj₁ 0<odd

≢0⇒> :  ∀ {x} → x ≢ zero → x > zero
≢0⇒> {zero}     0≢0 =  contradiction refl 0≢0
≢0⇒> {2[1+ _ ]} _   =  0<even
≢0⇒> {1+[2 _ ]} _   =  0<odd

≤0⇒≡ :  ∀ {x} → x ≤ zero → x ≡ zero
≤0⇒≡ {x} x≤0 =  ≤-antisym x≤0 (0≤ x)

0<suc :  ∀ x → zero < suc x
0<suc x =  ≢0⇒> (suc≢0 {x})

<⇒≱ :  _<_ ⇒ _≱_
<⇒≱ x<y (inj₁ y<x) =  contradiction y<x (<⇒≯ x<y)
<⇒≱ x<y (inj₂ y≡x) =  contradiction (sym y≡x) (<⇒≢ x<y)

≤⇒≯ :  _≤_ ⇒ _≯_
≤⇒≯ {x} {y} x≤y x>y =  <⇒≱ {y} {x} x>y x≤y

≮⇒≥ :  _≮_ ⇒ _≥_
≮⇒≥ {x} {y} x≮y  with <-cmp x y
... | tri< lt _  _   =  contradiction lt x≮y
... | tri≈ _  eq _   =  ≤-reflexive (sym eq)
... | tri> _  _  y<x =  <⇒≤ {y} {x} y<x

≰⇒> :  _≰_ ⇒ _>_
≰⇒> {x} {y} x≰y  with <-cmp x y
... | tri< lt _  _   =  contradiction (<⇒≤ {x} {y} lt) x≰y
... | tri≈ _  eq _   =  contradiction (≤-reflexive eq) x≰y
... | tri> _  _  x>y =  x>y

≤,≢⇒< :  ∀ {x y} → x ≤ y → x ≢ y → x < y
≤,≢⇒< (inj₁ x<y) _   =  x<y
≤,≢⇒< (inj₂ x≡y) x≢y =  contradiction x≡y x≢y

<-≤-trans :  ∀ {x y z} → x < y → y ≤ z → x < z
<-≤-trans             x<y (inj₁ y<z) =  <-trans x<y y<z
<-≤-trans {x} {_} {_} x<y (inj₂ y≡z) =  subst (x <_) y≡z x<y

≤-<-trans :  ∀ {x y z} → x ≤ y → y < z → x < z
≤-<-trans             (inj₁ x<y) y<z =  <-trans x<y y<z
≤-<-trans {_} {_} {z} (inj₂ x≡y) y<z =  subst (_< z) (sym x≡y) y<z

≡0-by≤ :  ∀ {x y} → x ≤ y → y ≡ zero → x ≡ zero
≡0-by≤ {x} {y} x≤y y≡0 =  ≤0⇒≡ x≤0
  where
  x≤0 = subst (x ≤_) y≡0 x≤y

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

<-resp-≈ :  _<_ Respects₂ _≡_
<-resp-≈ =  ( (\{x y y'} y≡y' x<y → subst (x <_) y≡y' x<y) ,
              (\{y x x'} x≡x' x<y → subst (_< y) x≡x' x<y)
            )

------------------------------------------------------------------------------
-- Several monotonicity proofs for _+_, suc
------------------------------------------------------------------------------

module IneqReasoning = InequalityReasoning {A = Bin} {_≈_ = _≡_} ≤-isPreorder <-trans
                                           <-resp-≈ <⇒≤ <-≤-trans ≤-<-trans

+-mono-≤ :  _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' =  begin
  x + y                  ≈⟨ sym $ cong₂ _+_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m + fromℕ n      ≈⟨ sym (fromℕ-homo-+ m n) ⟩
  fromℕ (m ℕ.+ n)        ≤⟨ fromℕ-mono-≤ (ℕp.+-mono-≤ m≤m' n≤n') ⟩
  fromℕ (m' ℕ.+ n')      ≈⟨ fromℕ-homo-+ m' n' ⟩
  fromℕ m' + fromℕ n'    ≈⟨ cong₂ _+_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' + y'                ∎
  where
  open IneqReasoning
  m    = toℕ x;             m'   = toℕ x'
  n    = toℕ y;             n'   = toℕ y'
  m≤m' = toℕ-mono-≤ x≤x';   n≤n' = toℕ-mono-≤ y≤y'

+-monoˡ-≤ :  ∀ x → (_+ x) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ x {y} {z} y≤z =  +-mono-≤ {y} {z} {x} {x} y≤z (≤-refl {x})

+-monoʳ-≤ :  ∀ x → (x +_) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ x {y} {z} y≤z =  +-mono-≤ {x} {x} {y} {z} (≤-refl {x}) y≤z

+-mono-<-≤ :  _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {x} {x'} {y} {y'} x<x' y≤y' =  begin-strict
    x + y                     ≈⟨ sym $ cong₂ _+_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
    fromℕ m + fromℕ n      ≈⟨ sym (fromℕ-homo-+ m n) ⟩
    fromℕ (m ℕ.+ n)          <⟨ fromℕ-mono-< (ℕp.+-mono-<-≤ m<m' n≤n') ⟩
    fromℕ (m' ℕ.+ n')        ≈⟨ fromℕ-homo-+ m' n' ⟩
    fromℕ m' + fromℕ n'    ≈⟨ cong₂ _+_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
    x' + y'                  ∎
  where
  open IneqReasoning
  m    = toℕ x;             n    = toℕ y
  m'   = toℕ x';            n'   = toℕ y'
  m<m' = toℕ-mono-< x<x';   n≤n' = toℕ-mono-≤ y≤y'

+-mono-≤-< :  _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-mono-≤-< {x} {x'} {y} {y'} x≤x' y<y' =  subst₂ _<_ (+-comm y x) (+-comm y' x') y+x<y'+x'
  where
  y+x<y'+x' =  +-mono-<-≤ {y} {y'} {x} {x'} y<y' x≤x'

+-monoˡ-< :  ∀ x → (_+ x) Preserves _<_ ⟶ _<_
+-monoˡ-< x {y} {z} y<z =  +-mono-<-≤ {y} {z} {x} {x} y<z (≤-refl {x})

+-monoʳ-< :  ∀ x → (x +_) Preserves _<_ ⟶ _<_
+-monoʳ-< x {y} {z} y<z =  +-mono-≤-< {x} {x} {y} {z} (≤-refl {x}) y<z

suc-mono-≤ :  suc Preserves _≤_ ⟶ _≤_
suc-mono-≤ {x} {y} x≤y =  begin
  suc x     ≈⟨ suc≗1+ x ⟩
  1B + x    ≤⟨ +-monoʳ-≤ 1B {x} {y} x≤y ⟩
  1B + y    ≈⟨ sym (suc≗1+ y) ⟩
  suc y     ∎
  where
  open IneqReasoning

------------------------------------------------------------------------------
-- Some more properties for _<_, _≤_.
------------------------------------------------------------------------------

x≤y+x :  ∀ (x y) → x ≤ y + x
x≤y+x x y =  begin
  x          ≈⟨ sym (+-identityˡ x) ⟩
  zero + x   ≤⟨ +-monoˡ-≤ x {zero} {y} (0≤ y) ⟩
  y + x      ∎
  where
  open IneqReasoning

x≤x+y :  ∀ (x y) → x ≤ x + y
x≤x+y x y =  begin
  x        ≤⟨ x≤y+x x y ⟩
  y + x    ≈⟨ +-comm y x ⟩
  x + y    ∎
  where
  open IneqReasoning

x<1+x :  ∀ x → x < 1B + x
x<1+x x = begin-strict
  x                 ≈⟨ sym (fromℕ-toℕ x) ⟩
  fromℕ n           <⟨ fromℕ-mono-< (ℕp.n<1+n {n}) ⟩
  fromℕ (ℕ.suc n)   ≈⟨ fromℕ-homo-+ 1 n ⟩
  1B + fromℕ n      ≈⟨ cong (1B +_) (fromℕ-toℕ x) ⟩
  1B + x            ∎
  where
  open IneqReasoning
  n = toℕ x

x<x+1 :  ∀ x → x < x + 1B
x<x+1 x =  begin-strict
  x        <⟨ x<1+x x ⟩
  1B + x   ≈⟨ +-comm 1B x ⟩
  x + 1B   ∎
  where
  open IneqReasoning

x<suc[x] :  ∀ x → x < suc x
x<suc[x] x =  begin-strict
  x        <⟨ x<1+x x ⟩
  1B + x   ≈⟨ sym (suc≗1+ x) ⟩
  suc x    ∎
  where
  open IneqReasoning

x≤suc[x] :  ∀ x → x ≤ suc x
x≤suc[x] x =  <⇒≤ {x} {suc x} (x<suc[x] x)

x≢suc[x] :  ∀ x → x ≢ suc x
x≢suc[x] =  <⇒≢ ∘ x<suc[x]

pred[x]<x :  ∀ {x} → x ≢ zero → pred x < x
pred[x]<x {x} x≢0 =  begin-strict
  pred x          <⟨ x<suc[x] (pred x) ⟩
  suc (pred x)    ≈⟨ suc-pred x x≢0 ⟩
  x               ∎
  where
  open IneqReasoning

------------------------------------------------------------------------------
-- Monotonicity proofs for _*_, double.
------------------------------------------------------------------------------

*-mono-≤ :  _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
*-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' =  begin
  x * y                  ≈⟨ sym $ cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m * fromℕ n      ≈⟨ sym (fromℕ-homo-* m n) ⟩
  fromℕ (m ℕ.* n)        ≤⟨ fromℕ-mono-≤ (ℕp.*-mono-≤ m≤m' n≤n') ⟩
  fromℕ (m' ℕ.* n')      ≈⟨ fromℕ-homo-* m' n' ⟩
  fromℕ m' * fromℕ n'    ≈⟨ cong₂ _*_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' * y'                ∎
  where
  open IneqReasoning
  m    = toℕ x;              m'   = toℕ x'
  n    = toℕ y;              n'   = toℕ y'
  m≤m' = toℕ-mono-≤ x≤x';    n≤n' = toℕ-mono-≤ y≤y'

*-monoʳ-≤ :  ∀ x → (x *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤ x {y} {y'} y≤y' =  *-mono-≤ {x} {x} {y} {y'} (≤-refl {x}) y≤y'

*-monoˡ-≤ :  ∀ x → (_* x) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤ x {y} {y'} y≤y' =  *-mono-≤ {y} {y'} {x} {x} y≤y' (≤-refl {x})

*-mono-< :  _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
*-mono-< {x} {x'} {y} {y'} x<x' y<y' =  begin-strict
  x * y                  ≈⟨ sym $ cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m * fromℕ n      ≈⟨ sym (fromℕ-homo-* m n) ⟩
  fromℕ (m ℕ.* n)        <⟨ fromℕ-mono-< (ℕp.*-mono-< m<m' n<n') ⟩
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
  y + xy           <⟨ +-mono-<-≤  {y} {z} {xy} {xz} y<z xy≤xz ⟩
  z + xz           ≈⟨ sym (suc-* x z) ⟩
  (suc x) * z      ∎
  where
  open IneqReasoning
  xy = x * y;   xz = x * z;   xy≤xz = *-monoʳ-≤ x (<⇒≤ {y} {z} y<z)

*-monoˡ-< :  ∀ x → (_* (suc x)) Preserves _<_ ⟶ _<_
*-monoˡ-< x {y} {z} y<z = begin-strict
  y * (suc x)   ≈⟨ *-comm y (suc x) ⟩
  (suc x) * y   <⟨ *-monoʳ-< x {y} {z} y<z ⟩
  (suc x) * z   ≈⟨ *-comm (suc x) z ⟩
  z * (suc x)   ∎
  where
  open IneqReasoning

double-mono-≤ :  double Preserves _≤_ ⟶ _≤_
double-mono-≤ {x} {y} x≤y =  begin
  double x   ≈⟨ double≗2B* x ⟩
  2B * x     ≤⟨ *-monoʳ-≤ 2B {x} {y} x≤y ⟩
  2B * y     ≈⟨ sym (double≗2B* y) ⟩
  double y   ∎
  where
  open IneqReasoning

double-mono-< :  double Preserves _<_ ⟶ _<_
double-mono-< {x} {y} x<y =  begin-strict
  double x   ≈⟨ double≗2B* x ⟩
  2B * x     <⟨ *-monoʳ-< 1B {x} {y} x<y ⟩
  2B * y     ≈⟨ sym (double≗2B* y) ⟩
  double y   ∎
  where
  open IneqReasoning

double-back-mono-≤ :  ∀ {x y} → double x ≤ double y → x ≤ y
double-back-mono-≤ {x} {y} 2x≤2y  with <-cmp x y
... | tri< x<y _   _   =  <⇒≤ {x} {y} x<y
... | tri≈ _   x≡y _   =  ≤-reflexive x≡y
... | tri> _   _   x>y =  contradiction 2x≤2y (<⇒≱ {double y} {double x} 2x>2y)
  where
  2x>2y = double-mono-< {y} {x} x>y

double-back-mono-< :  ∀ {x y} → double x < double y → x < y
double-back-mono-< {x} {y} 2x<2y  with <-cmp x y
... | tri< x<y _   _   =  x<y
... | tri≈ _   x≡y _   =  contradiction 2x<2y (<-irrefl 2x≡2y)
  where
  2x≡2y = cong double x≡y

... | tri> _   _    x>y =  contradiction 2x>2y (<⇒≯ {double x} {double y} 2x<2y)
  where
  2x>2y = double-mono-< {y} {x} x>y

------------------------------------------------------------------------------
-- Some more properties for _<_, _≤_.
------------------------------------------------------------------------------

x<double[x] :  ∀ x → x ≢ zero → x < double x
x<double[x] x x≢0 =  begin-strict
  x                 ≈⟨ sym (suc-pred x x≢0) ⟩
  suc px            ≈⟨ sym (*-identityʳ (suc px)) ⟩
  suc px * 1B       <⟨ *-monoʳ-< px (x<1+x 1B) ⟩
  suc px * 2B       ≈⟨ *-comm (suc px) 2B ⟩
  2B * suc px       ≈⟨ sym (double≗2B* (suc px)) ⟩
  double (suc px)   ≈⟨ cong double (suc-pred x x≢0) ⟩
  double x          ∎
  where
  open IneqReasoning
  px = pred x

suc[x]≤⇒x< :  ∀ {x y} → suc x ≤ y → x < y
suc[x]≤⇒x< {x} {_} (inj₁ sx<y)  =  <-trans (x<suc[x] x) sx<y
suc[x]≤⇒x< {x} {_} (inj₂ sx≡y) =  subst (x <_) sx≡y (x<suc[x] x)

x<⇒suc[x]≤ :  ∀ {x y} → x < y → suc x ≤ y
x<⇒suc[x]≤ {x} {y} x<y =  begin
  suc x                  ≈⟨ sym (fromℕ-toℕ (suc x)) ⟩
  fromℕ (toℕ (suc x))    ≈⟨ cong fromℕ (toℕ-suc x) ⟩
  fromℕ (ℕ.suc m)        ≤⟨ fromℕ-mono-≤ 1+m≤n ⟩
  fromℕ n                ≈⟨ fromℕ-toℕ y ⟩
  y                      ∎
  where
  open IneqReasoning
  m = toℕ x;  n = toℕ y;  1+m≤n = toℕ-mono-< x<y

suc[x]≤double[x] :  ∀ x → x ≢ zero → suc x ≤ double x
suc[x]≤double[x] x =  x<⇒suc[x]≤ {x} {double x} ∘ x<double[x] x

x≤suc[y]*x :  ∀ (x y) → x ≤ (suc y) * x
x≤suc[y]*x x y =  begin
  x             ≤⟨ x≤x+y x (y * x) ⟩
  x + y * x     ≈⟨ sym (suc-* y x) ⟩
  (suc y) * x   ∎
  where
  open IneqReasoning

x≤double[x] :  ∀ x → x ≤ double x
x≤double[x] x =  begin
  x         ≤⟨ x≤x+y x x ⟩
  x + x     ≈⟨ sym (double[x]≡x+x x) ⟩
  double x  ∎
  where
  open IneqReasoning

suc[x]<2[1+x] :  ∀ x → suc x < 2[1+ x ]
suc[x]<2[1+x] x =  begin-strict
  suc x           <⟨ x<double[x] (suc x) suc≢0  ⟩
  double (suc x)  ≈⟨ sym (2[1+-as∘ x) ⟩
  2[1+ x ]        ∎
  where
  open IneqReasoning

x<2[1+x] :  ∀ x → x < 2[1+ x ]
x<2[1+x] x =  <-trans {x} {suc x} {2[1+ x ]} (x<suc[x] x) (suc[x]<2[1+x] x)

x<1+[2x] :  ∀ x → x < 1+[2 x ]
x<1+[2x] x =  begin-strict
  x               <⟨ x<suc[x] x ⟩
  suc x           ≤⟨ suc-mono-≤ {x} {double x} (x≤double[x] x) ⟩
  suc (double x)  ≈⟨ sym (1+[2-as∘ x) ⟩
  1+[2 x ]        ∎
  where
  open IneqReasoning

double[x]<1+[2x] :  ∀ x → double x < 1+[2 x ]
double[x]<1+[2x] x =  begin-strict
  double x     <⟨ x<suc[x] (double x) ⟩
  suc (double x)   ≈⟨ sym (1+[2-as∘ x) ⟩
  1+[2 x ]     ∎
  where
  open IneqReasoning

pred-mono-≤ :  pred Preserves _≤_ ⟶ _≤_
pred-mono-≤ {x} {y} x≤y =  begin
  pred x             ≈⟨ cong pred (sym (fromℕ-toℕ x)) ⟩
  pred (fromℕ m)     ≈⟨ sym (fromℕ-pred m) ⟩
  fromℕ (ℕ.pred m)   ≤⟨ fromℕ-mono-≤ (ℕp.pred-mono m≤n) ⟩
  fromℕ (ℕ.pred n)   ≈⟨ fromℕ-pred n ⟩
  pred (fromℕ n)     ≈⟨ cong pred (fromℕ-toℕ y) ⟩
  pred y             ∎
  where
  open IneqReasoning
  m = toℕ x;  n = toℕ y;  m≤n = toℕ-mono-≤ x≤y

x<1⇒x≡0 :  ∀ {x} → x < 1B → x ≡ zero
x<1⇒x≡0 {x} x<1 =  ≤0⇒≡ x≤0
  where
  open IneqReasoning
  suc[x]≤1 = x<⇒suc[x]≤ {x} {1B} x<1
  x≤0 = begin
    x             ≈⟨ sym (pred-suc x) ⟩
    pred (suc x)  ≤⟨ pred-mono-≤ {suc x} {1B} suc[x]≤1 ⟩
    pred 1B       ≈⟨ refl ⟩
    zero          ∎

x≢0-nor-1⇒1<x :  ∀ {x} → x ≢ zero → x ≢ 1B → 1B < x
x≢0-nor-1⇒1<x {x} x≢0 x≢1  with <-cmp 1B x
... | tri< 1<x _   _   =  1<x
... | tri≈ _   1≡x _   =  contradiction (sym 1≡x) x≢1
... | tri> _   _   1>x =  contradiction (x<1⇒x≡0 1>x) x≢0

_<ₙon_ :  Rel Bin 0ℓ
_<ₙon_ =  ℕ._<_ on toℕ

<⇒<ₙon :  ∀ {x y} → x < y → x <ₙon y
<⇒<ₙon x<y =  toℕ-mono-< x<y

<ₙon⇒< :  ∀ {x y} → x <ₙon y → x < y
<ₙon⇒< {x} {y} xN<yN =  subst₂ _<_ (fromℕ-toℕ x) (fromℕ-toℕ y) xN'<yN'
  where
  xN'<yN' = fromℕ-mono-< xN<yN

------------------------------------------------------------------------------
-- StrictTotalOrder and DecTotalOrder instances for Bin.
------------------------------------------------------------------------------

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence =  isEquivalence
  ; trans         =  \{x y z} → <-trans {x} {y} {z}
  ; compare       =  <-cmp
  }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { Carrier            =  Bin
  ; _≈_                =  _≡_
  ; _<_                =  _<_
  ; isStrictTotalOrder =  <-isStrictTotalOrder
  }

≤-isPartialOrder :  IsPartialOrder _≡_ _≤_
≤-isPartialOrder =  record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-total :  Relation.Binary.Total _≤_
≤-total x y  with <-cmp x y
... | tri< le _  _  =  inj₁ (<⇒≤ {x} {y} le)
... | tri≈ _  eq _  =  inj₁ (≤-reflexive eq)
... | tri> _  _  gt =  inj₂ (<⇒≤ {y} {x} gt)

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record
  { Carrier         = Bin
  ; _≈_             = _≡_ {A = Bin}
  ; _≤_             = _≤_
  ; isDecTotalOrder = ≤-isDecTotalOrder
  }

