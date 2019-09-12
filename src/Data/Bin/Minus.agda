------------------------------------------------------------------------
-- The Agda standard library
--
-- Subtraction on Bin and some of its property proofs.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Minus where

open import Data.Bin.Base
open import Data.Bin.Properties
open import Data.Empty using (⊥)
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_; proj₁; proj₂; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; _$_)
open import Relation.Binary using (Tri; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as P using
  (_≡_; _≢_; _≗_; refl; sym; trans; cong; cong₂; resp₂; subst)
import Relation.Binary.Reasoning.Base.Triple as InequalityReasoning
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Algebra.FunctionProperties {A = Bin} _≡_
open import Algebra.Properties.CommutativeSemigroup +-semigroup +-comm
  using (xy∙z≈y∙xz)

private
  module IneqReasoning = InequalityReasoning {A = Bin} {_≈_ = _≡_} ≤-isPreorder
                                   <-trans (resp₂ _<_) <⇒≤ <-≤-trans ≤-<-trans
open Bin
open Tri
open _<_

------------------------------------------------------------------------------
-- Defining and implementing minus
------------------------------------------------------------------------------

data Minus : Bin → Bin → Bin → Set where
  minuend< :  ∀ {x y d} → x < y → d ≡ zero → Minus x y d
  minuend≡ :  ∀ {x y d} → x ≡ y → d ≡ zero → Minus x y d
  minuend> :  ∀ {x y d} → x > y → (x ≡ y + d) → Minus x y d

minus : ∀ x y → ∃ (λ d → Minus x y d)
--
-- It evaluates the cut difference d, the result of comparison (<, ≡, >),
-- and the witness for  x ≡ y + d  when x > y.

minus zero     zero     =  (zero , minuend≡ refl refl)
minus zero     2[1+ x ] =  (zero , minuend< 0<even refl)
minus zero     1+[2 x ] =  (zero , minuend< 0<odd refl)
minus 2[1+ x ] zero     =  (2[1+ x ] , minuend> 0<even refl)
minus 2[1+ x ] 2[1+ y ] =  aux (minus x y)
  where
  open IneqReasoning;  x' = 2[1+ x ];  y' = 2[1+ y ]

  aux :  ∃ (λ d → Minus x y d) → ∃ (λ d' → Minus x' y' d')
  aux (.zero , minuend< x<y refl)  =  (zero , minuend< (even<even x<y) refl)
  aux (.zero , minuend≡ x≡y refl)  =  (zero , minuend≡ (cong 2[1+_] x≡y) refl)
  aux (d ,     minuend> x>y x≡y+d) =  (2d , minuend> x'>y' (begin-equality
    2[1+ x ]              ≡⟨ cong 2[1+_] x≡y+d ⟩
    2[1+ (y + d) ]        ≡⟨ 2[1+_]-double-suc (y + d) ⟩
    double (suc (y + d))  ≡⟨ cong double (sym (suc-+ y d)) ⟩
    double ((suc y) + d)  ≡⟨ double-distrib-+ (suc y) d ⟩
    double (suc y) + 2d   ≡⟨ cong (_+ 2d) (sym (2[1+_]-double-suc y)) ⟩
    2[1+ y ] + 2d         ∎))
    where
    2d = double d;  x'>y' = even<even x>y

minus 2[1+ x ] 1+[2 y ] =  aux (minus x y)
  where
  -- 2(1+x) ∸ (1 + 2y) =  2 + 2x - (1 + 2y) =  1 + 2x - 2y

  open IneqReasoning;   x' = 2[1+ x ];   y' = 1+[2 y ]

  aux :  ∃ (λ d → Minus x y d) → ∃ (λ d' → Minus x' y' d')
  aux (.zero , minuend< x<y refl) =  (zero , minuend< (even<odd x<y) refl)
  aux (.zero , minuend≡ x≡y refl) =  (1B , minuend> x'>y' (begin-equality
    2[1+ x ]      ≡⟨ cong 2[1+_] x≡y ⟩
    2[1+ y ]      ≡⟨ refl ⟩
    suc 1+[2 y ]  ≡⟨ suc≗1+ y' ⟩
    1B + y'       ≡⟨ +-comm 1B y' ⟩
    y' + 1B       ∎))
    where
    x'>y' = odd<even (inj₂ (sym x≡y))

  aux (d , minuend> x>y x≡y+d) =  (d' , minuend> x'>y' x'≡y'+d')
    where
    d'       = 1+[2 d ]
    x'≡y'+d' = sym (cong (suc ∘ 1+[2_]) (sym x≡y+d))
    x'>y'    = <-trans (odd<odd x>y) (odd<even (inj₂ refl))

minus 1+[2 x ] zero     =  (1+[2 x ] , minuend> 0<odd refl)
minus 1+[2 x ] 1+[2 y ] =  aux (minus x y)
  where
  open IneqReasoning;  x' = 1+[2 x ];  y' = 1+[2 y ]

  aux :  ∃ (λ d → Minus x y d) → ∃ (λ d' → Minus x' y' d')
  aux (.zero , minuend< x<y refl) =  (zero , minuend< (odd<odd x<y) refl)
  aux (.zero , minuend≡ x≡y refl) =  (zero , minuend≡ (cong 1+[2_] x≡y) refl)
  aux (d , minuend> x>y x≡y+d)    =  (2d , minuend> x'>y' (begin-equality
    1+[2 x ]              ≡⟨ cong 1+[2_] x≡y+d ⟩
    1+[2 (y + d) ]        ≡⟨ 1+[2_]-suc-double (y + d) ⟩
    suc (double (y + d))  ≡⟨ cong suc (double-distrib-+ y d) ⟩
    suc (double y + 2d)   ≡⟨ sym (suc-+ (double y) 2d) ⟩
    suc (double y) + 2d   ≡⟨ cong (_+ 2d) (sym (1+[2_]-suc-double y)) ⟩
    1+[2 y ] + 2d         ∎))
    where
    2d = double d;   x'>y' = odd<odd x>y

minus 1+[2 x ] 2[1+ y ] =  aux (minus x y)    -- res = (1 + 2x) ∸ 2(1 + y) = ...
  where
  open IneqReasoning
  x'  = 1+[2 x ];   y' = 2[1+ y ];   1+x = suc x
  1+y = suc y;      2x = double x;   2y = double y

  aux :  ∃ (λ d → Minus x y d) → ∃ (λ d' → Minus x' y' d')
  aux (.zero , minuend< x<y refl) =  (zero , minuend< x'<y' refl)
    where
    x'<y' = <-trans (odd<odd x<y) (odd<even (inj₂ refl))

  aux (.zero , minuend≡ x≡y refl) =  (zero , minuend< x'<y' refl)
    where
    x'<y' =  subst (_< 2[1+ y ]) (sym (cong 1+[2_] x≡y)) (odd<even (inj₂ refl))

  aux (d , minuend> x>y x≡y+d) =  (d' , minuend> x'>y' x'≡y'+d')
    where
    2d     = double d;   pd  = pred d;      suc-2y   = suc 2y
    suc-pd = suc pd;     2pd = double pd;   suc2*-pd = suc 2pd

    d≢0 : d ≢ 0B
    d≢0 d≡0 =  <-irrefl (sym x≡y) x>y
      where
      x≡y = begin-equality
        x        ≡⟨ x≡y+d ⟩
        y + d    ≡⟨ cong (y +_) d≡0 ⟩
        y + 0B   ≡⟨ +-identityʳ y ⟩
        y        ∎

    d≡suc-pd = sym (suc-pred d≢0)
    d'       = 1+[2 pd ]
    0<d'     = 0<odd
    x'≡y'+d' = begin-equality
      1+[2 x ]                           ≡⟨ cong 1+[2_] x≡y+d ⟩
      1+[2 (y + d) ]                     ≡⟨ 1+[2_]-suc-double (y + d) ⟩
      suc (double (y + d))               ≡⟨ cong suc (double-distrib-+ y d) ⟩
      suc (2y + 2d)                      ≡⟨ sym (suc-+ 2y 2d) ⟩
      suc-2y + 2d                        ≡⟨ cong ((suc-2y +_) ∘ double) d≡suc-pd ⟩
      suc-2y + double (suc pd)           ≡⟨ cong (suc-2y +_) (double≗2B* suc-pd) ⟩
      suc-2y + 2B * (suc pd)             ≡⟨ cong (suc-2y +_) (*-suc 2B pd) ⟩
      suc-2y + (2B + (2B * pd))          ≡⟨ cong ((suc-2y +_) ∘ (2B +_)) (sym (double≗2B* pd)) ⟩
      suc-2y + (2B + 2pd)                ≡⟨ refl ⟩
      suc-2y + ((1B + 1B) + 2pd)         ≡⟨ cong (suc-2y +_) (+-assoc 1B 1B 2pd) ⟩
      suc-2y + (1B + (1B + 2pd))         ≡⟨ cong ((suc-2y +_) ∘ (1B +_)) (sym (suc≗1+ 2pd)) ⟩
      suc-2y + (1B + suc2*-pd)           ≡⟨ sym (+-assoc suc-2y 1B suc2*-pd) ⟩
      (suc 2y + 1B) + suc2*-pd           ≡⟨ cong ((_+ suc2*-pd) ∘ (_+ 1B)) (suc≗1+ 2y) ⟩
      ((1B + 2y) + 1B) + suc2*-pd        ≡⟨ cong (_+ suc2*-pd) (xy∙z≈y∙xz 1B 2y 1B) ⟩
      (2y + 2B) + suc2*-pd               ≡⟨ refl ⟩
      (double y + double 1B) + suc2*-pd  ≡⟨ cong (_+ suc2*-pd) (sym (double-distrib-+ y 1B)) ⟩
      double (y + 1B) + suc2*-pd         ≡⟨ cong ((_+ suc2*-pd) ∘ double) (+-comm y 1B) ⟩
      double (1B + y) + suc2*-pd         ≡⟨ cong ((_+ suc2*-pd) ∘ double) (sym (suc≗1+ y)) ⟩
      double (suc y) + suc 2pd           ≡⟨ cong₂ _+_ (sym (2[1+_]-double-suc y))
                                                      (sym (1+[2_]-suc-double pd)) ⟩
      y' + d'                            ∎

    x'>y' = begin-strict
      y'        ≡⟨ +-identityʳ y' ⟩
      y' + 0B   <⟨ +-monoʳ-< y' 0<d' ⟩
      y' + d'   ≡⟨ sym x'≡y'+d' ⟩
      x'        ∎

infixl 6 _∸_

_∸_ : Op₂ Bin              -- the proper result of minus
_∸_ x =  proj₁ ∘ minus x


------------------------------------------------------------------------------
-- Properties of minus
------------------------------------------------------------------------------

x≤y⇒x∸y≡0 :  ∀ {x y} → x ≤ y → x ∸ y ≡ 0B
x≤y⇒x∸y≡0 {x} {y} x≤y  with  minus x y
... | (_ , minuend< _   d≡0) =  d≡0
... | (_ , minuend≡ _   d≡0) =  d≡0
... | (_ , minuend> x>y _  ) =  contradiction x>y (≤⇒≯ x≤y)

x∸y≡0⇒x≤y :  ∀ {x y} → x ∸ y ≡ 0B → x ≤ y
x∸y≡0⇒x≤y {x} {y} x-y≡0 =  aux (proj₂ res)
  where
  open IneqReasoning;  res = minus x y;  d = proj₁ res;  d≡0 = x-y≡0

  aux : Minus x y d → x ≤ y
  aux (minuend< x<y _    ) =  <⇒≤ x<y
  aux (minuend≡ x≡y _    ) =  ≤-reflexive x≡y
  aux (minuend> x>y x≡y+d) =  contradiction x>y (≡⇒≯  (begin-equality
    x        ≡⟨ x≡y+d ⟩
    y + d    ≡⟨ cong (y +_) d≡0 ⟩
    y + 0B   ≡⟨ +-identityʳ y ⟩
    y        ∎))

x<y⇒0<y∸x :  ∀ {x y} → x < y → 0B < y ∸ x
x<y⇒0<y∸x {x} {y} x<y  with <-cmp (y ∸ x) 0B
... | tri> _ _     gt =  gt
... | tri≈ _ y∸x≡0 _  =  contradiction (x∸y≡0⇒x≤y y∸x≡0) (<⇒≱ x<y)
... | tri< y∸x<0 _ _  =  contradiction y∸x<0 x≮0

x∸x :  ∀ x → x ∸ x ≡ 0B
x∸x x =  x≤y⇒x∸y≡0 (≤-refl {x})

0∸ :  ∀ x → 0B ∸ x ≡ 0B
0∸ x =  x≤y⇒x∸y≡0 (0≤x x)

[x+y]∸y≡x :  ∀ x y → (x + y) ∸ y ≡ x
[x+y]∸y≡x x y  with  minus (x + y) y
... | (_ , minuend< x+y<0+y _  ) =  contradiction 0+y≤x+y (<⇒≱  x+y<0+y)
  where
  0+y≤x+y =  +-monoˡ-≤ y (0≤x x)

... | (d , minuend≡ x+y≡0+y d≡0)       =  trans d≡0 (sym (+-cancelʳ-≡ x 0B
                                                                    x+y≡0+y))
... | (d , minuend> 0+y<x+y x+y≡0+y+d) =  sym x≡d
  where
  open IneqReasoning
  x+y≡d+y = begin-equality
    x + y          ≡⟨ x+y≡0+y+d ⟩
    (0B + y) + d   ≡⟨ cong (_+ d) (+-identityˡ y) ⟩
    y + d          ≡⟨ +-comm y d ⟩
    d + y          ∎

  x≡d =  +-cancelʳ-≡ x d x+y≡d+y

[x+y]∸x≡y :  ∀ x y → (x + y) ∸ x ≡ y
[x+y]∸x≡y x y =  trans (cong (_∸ x) (+-comm x y)) ([x+y]∸y≡x y x)

∸-identityʳ :  RightIdentity 0B _∸_
∸-identityʳ x =  trans (cong (_∸ 0B) $ sym $ +-identityʳ x) ([x+y]∸y≡x x 0B)

x+[y∸x]≡y :  ∀ {x y} → x ≤ y → x + (y ∸ x) ≡ y
x+[y∸x]≡y {x} {y} x≤y =  aux (minus y x)
  where
  open IneqReasoning

  aux :  ∃ (λ d → Minus y x d) → x + (y ∸ x) ≡ y
  aux (_ , minuend< y<x _) =  contradiction y<x (≤⇒≯  x≤y)
  aux (_ , minuend≡ y≡x _) =  begin-equality
    x + (y ∸ x)   ≡⟨ cong₂ _+_ (sym y≡x) (cong (_∸ x) y≡x) ⟩
    y + (x ∸ x)   ≡⟨ cong (y +_) (x∸x x) ⟩
    y + 0B        ≡⟨ +-identityʳ y ⟩
    y             ∎

  aux (d , minuend> x<y y≡x+d) =  begin-equality
    x + (y ∸ x)        ≡⟨ cong ((x +_) ∘ (_∸ x)) y≡d+x ⟩
    x + ((d + x) ∸ x)  ≡⟨ cong (x +_) ([x+y]∸y≡x d x) ⟩
    x + d              ≡⟨ sym y≡x+d ⟩
    y                  ∎
    where y≡d+x = trans y≡x+d (+-comm x d)

[x∸y]+y≡x :  ∀ {x y} → y ≤ x → (x ∸ y) + y ≡ x
[x∸y]+y≡x {x} {y} y≤x =  trans (+-comm (x ∸ y) y) (x+[y∸x]≡y y≤x)

pred≗∸1 :  pred ≗ (_∸ 1B)
pred≗∸1 x =  aux (x ≟ 0B)
  where
  open IneqReasoning;  px = pred x

  aux : Dec (x ≡ 0B) → pred x ≡ x ∸ 1B
  aux (yes x≡0) =  trans (cong pred x≡0) (cong (_∸ 1B) (sym x≡0))
  aux (no x≢0)  =  begin-equality
    pred x           ≡⟨ cong pred (sym (suc-pred x≢0)) ⟩
    pred (suc px)    ≡⟨ pred-suc px ⟩
    px               ≡⟨ sym ([x+y]∸y≡x px 1B) ⟩
    (px + 1B) ∸ 1B   ≡⟨ cong (_∸ 1B) (+-comm px 1B) ⟩
    (1B + px) ∸ 1B   ≡⟨ cong (_∸ 1B) (sym (suc≗1+ px)) ⟩
    (suc px) ∸ 1B    ≡⟨ cong (_∸ 1B) (suc-pred x≢0) ⟩
    x ∸ 1B           ∎

toℕ-homo-∸ :  ∀ x y → toℕ (x ∸ y) ≡ (toℕ x) ℕ.∸ (toℕ y)
toℕ-homo-∸ x y  with <-cmp x y
... | tri< x<y _ _ =  begin
  toℕ (x ∸ y)  ≡⟨ cong toℕ (x≤y⇒x∸y≡0 x≤y) ⟩
  toℕ 0B       ≡⟨ refl ⟩
  0            ≡⟨ sym (ℕₚ.m≤n⇒m∸n≡0 m≤n) ⟩
  m ℕ.∸ n      ∎
  where
  open P.≡-Reasoning;  m = toℕ x;  n = toℕ y;  x≤y = <⇒≤ x<y;  m≤n = toℕ-mono-≤ x≤y

... | tri≈ _ x≡y _ =  trans (cong toℕ (x≤y⇒x∸y≡0 x≤y)) (sym (ℕₚ.m≤n⇒m∸n≡0 m≤n))
  where
  m = toℕ x;  n = toℕ y;  x≤y = ≤-reflexive x≡y;  m≤n = toℕ-mono-≤ x≤y

... | tri> _ _ y<x =  begin
  toℕ (x ∸ y)                   ≡⟨ sym (ℕₚ.m+n∸n≡m (toℕ (x ∸ y)) n) ⟩
  ((toℕ (x ∸ y)) ℕ.+ n) ℕ.∸ n   ≡⟨ cong (ℕ._∸ n) eq ⟩
  ((m ℕ.∸ n) ℕ.+ n) ℕ.∸ n       ≡⟨ ℕₚ.m+n∸n≡m (m ℕ.∸ n) n ⟩
  m ℕ.∸ n                       ∎
  where
  open P.≡-Reasoning;  m = toℕ x;  n = toℕ y;  y≤x = <⇒≤ y<x;  n≤m = toℕ-mono-≤ y≤x
  eq = begin
    toℕ (x ∸ y) ℕ.+ n   ≡⟨ sym (toℕ-homo-+ (x ∸ y) y) ⟩
    toℕ ((x ∸ y) + y)   ≡⟨ cong toℕ (+-comm (x ∸ y) y) ⟩
    toℕ (y + (x ∸ y))   ≡⟨ cong toℕ (x+[y∸x]≡y y≤x) ⟩
    m                   ≡⟨ sym (ℕₚ.m+[n∸m]≡n n≤m) ⟩
    n ℕ.+ (m ℕ.∸ n)     ≡⟨ ℕₚ.+-comm n (m ℕ.∸ n) ⟩
    (m ℕ.∸ n) ℕ.+ n     ∎

fromℕ-homo-∸  :  (m n : ℕ) → fromℕ (m ℕ.∸ n) ≡ (fromℕ m) ∸ (fromℕ n)
fromℕ-homo-∸ m n =  begin-equality
  fromℕ (m ℕ.∸ n)          ≡⟨ cong fromℕ (cong₂ ℕ._∸_ m≡xN n≡yN) ⟩
  fromℕ (toℕ x ℕ.∸ toℕ y)  ≡⟨ cong fromℕ (sym (toℕ-homo-∸ x y)) ⟩
  fromℕ (toℕ (x ∸ y))      ≡⟨ fromℕ-toℕ (x ∸ y) ⟩
  x ∸ y                    ∎
  where
  open IneqReasoning
  x    = fromℕ m;             y    = fromℕ n
  m≡xN = sym (toℕ-fromℕ m);   n≡yN = sym (toℕ-fromℕ n)

*-distribˡ-∸ :  _*_ DistributesOverˡ _∸_
*-distribˡ-∸ x y z =  begin-equality
  x * (y ∸ z)                                ≡⟨ sym (fromℕ-toℕ (x * (y ∸ z))) ⟩
  fromℕ (toℕ (x * (y ∸ z)))                  ≡⟨ cong fromℕ (toℕ-homo-* x (y ∸ z)) ⟩
  fromℕ (k ℕ.* (toℕ (y ∸ z)))                ≡⟨ cong (fromℕ ∘ (k ℕ.*_)) (toℕ-homo-∸ y z) ⟩
  fromℕ (k ℕ.* (m ℕ.∸ n))                    ≡⟨ cong fromℕ (ℕₚ.*-distribˡ-∸ k m n) ⟩
  fromℕ ((k ℕ.* m) ℕ.∸ (k ℕ.* n))            ≡⟨ fromℕ-homo-∸ (k ℕ.* m) (k ℕ.* n) ⟩
  fromℕ (k ℕ.* m) ∸ fromℕ (k ℕ.* n)          ≡⟨ cong₂ _∸_ (fromℕ-homo-* k m) (fromℕ-homo-* k n) ⟩
  (fromℕ k * fromℕ m) ∸ (fromℕ k * fromℕ n)  ≡⟨ cong₂ _∸_ (cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ y))
                                                  (cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ z)) ⟩
  x * y ∸ x * z                              ∎
  where open IneqReasoning;  k = toℕ x;  m = toℕ y;  n = toℕ z

*-distribʳ-∸ :  _*_ DistributesOverʳ _∸_
*-distribʳ-∸ x y z =  begin-equality
  (y ∸ z) * x     ≡⟨ *-comm _ x ⟩
  x * (y ∸ z)     ≡⟨ *-distribˡ-∸ x y z ⟩
  x * y ∸ x * z   ≡⟨ cong₂ _∸_ (*-comm x y) (*-comm x z) ⟩
  y * x ∸ z * x   ∎
  where open IneqReasoning

double-distrib-∸ :  ∀ x y → double (x ∸ y) ≡ double x ∸ double y
double-distrib-∸ x y =  begin-equality
  double (x ∸ y)       ≡⟨ double≗2B* (x ∸ y) ⟩
  2B * (x ∸ y)         ≡⟨ *-distribˡ-∸ 2B x y ⟩
  2B * x ∸ 2B * y      ≡⟨ cong₂ _∸_ (sym (double≗2B* x)) (sym (double≗2B* y)) ⟩
  double x ∸ double y  ∎
  where open IneqReasoning

+-∸-comm :  ∀ {x} y {o} → o ≤ x → (x + y) ∸ o ≡ (x ∸ o) + y
+-∸-comm {x} y {o} o≤x =  begin-equality
  (x + y) ∸ o                 ≡⟨ sym (fromℕ-toℕ ((x + y) ∸ o)) ⟩
  fromℕ (toℕ ((x + y) ∸ o))   ≡⟨ cong fromℕ (toℕ-homo-∸ (x + y) o) ⟩
  fromℕ (toℕ (x + y) ℕ.∸ n)   ≡⟨ cong (fromℕ ∘ (ℕ._∸ n)) (toℕ-homo-+ x y) ⟩
  fromℕ ((k ℕ.+ m) ℕ.∸ n)     ≡⟨ cong fromℕ (ℕₚ.+-∸-comm m n≤k) ⟩
  fromℕ ((k ℕ.∸ n) ℕ.+ m)     ≡⟨ fromℕ-homo-+ (k ℕ.∸ n) m ⟩
  fromℕ (k ℕ.∸ n) + fromℕ m   ≡⟨ cong ((fromℕ (k ℕ.∸ n)) +_) (fromℕ-toℕ y) ⟩
  fromℕ (k ℕ.∸ n) + y         ≡⟨ cong (_+ y) (fromℕ-homo-∸ k n) ⟩
  (fromℕ k ∸ fromℕ n) + y     ≡⟨ cong (_+ y) (cong₂ _∸_ (fromℕ-toℕ x) (fromℕ-toℕ o)) ⟩
  (x ∸ o) + y                 ∎
  where
  open IneqReasoning;  k = toℕ x;  m = toℕ y;  n = toℕ o;  n≤k = toℕ-mono-≤ o≤x

∸-+-assoc :  ∀ x y o → (x ∸ y) ∸ o ≡ x ∸ (y + o)
∸-+-assoc x y o =  begin-equality
  (x ∸ y) ∸ o                    ≡⟨ sym (fromℕ-toℕ ((x ∸ y) ∸ o)) ⟩
  fromℕ (toℕ ((x ∸ y) ∸ o))      ≡⟨ cong fromℕ (toℕ-homo-∸ (x ∸ y) o) ⟩
  fromℕ (toℕ (x ∸ y) ℕ.∸ n)      ≡⟨ cong (fromℕ ∘ (ℕ._∸ n)) (toℕ-homo-∸ x y) ⟩
  fromℕ ((k ℕ.∸ m) ℕ.∸ n)        ≡⟨ cong fromℕ (ℕₚ.∸-+-assoc k m n) ⟩
  fromℕ (k ℕ.∸ (m ℕ.+ n))        ≡⟨ fromℕ-homo-∸ k (m ℕ.+ n) ⟩
  fromℕ k ∸ fromℕ (m ℕ.+ n)      ≡⟨ cong ((fromℕ k) ∸_) (fromℕ-homo-+ m n) ⟩
  fromℕ k ∸ (fromℕ m + fromℕ n)  ≡⟨ cong ((fromℕ k) ∸_) (cong₂ _+_ (fromℕ-toℕ y) (fromℕ-toℕ o)) ⟩
  fromℕ k ∸ (y + o)              ≡⟨ cong (_∸ (y + o)) (fromℕ-toℕ x) ⟩
  x ∸ (y + o)                    ∎
  where
  open IneqReasoning;  k = toℕ x;  m = toℕ y;  n = toℕ o

+-∸-assoc :  ∀ x {y o} → o ≤ y → (x + y) ∸ o ≡ x + (y ∸ o)
+-∸-assoc x {y} {o} o≤y =  begin-equality
  (x + y) ∸ o                 ≡⟨ sym (fromℕ-toℕ ((x + y) ∸ o)) ⟩
  fromℕ (toℕ ((x + y) ∸ o))   ≡⟨ cong fromℕ (toℕ-homo-∸ (x + y) o) ⟩
  fromℕ (toℕ (x + y) ℕ.∸ n)   ≡⟨ cong (fromℕ ∘ (ℕ._∸ n)) (toℕ-homo-+ x y) ⟩
  fromℕ ((k ℕ.+ m) ℕ.∸ n)     ≡⟨ cong fromℕ (ℕₚ.+-∸-assoc k n≤m) ⟩
  fromℕ (k ℕ.+ (m ℕ.∸ n))     ≡⟨ fromℕ-homo-+ k (m ℕ.∸ n) ⟩
  fromℕ k + fromℕ (m ℕ.∸ n)   ≡⟨ cong (_+ (fromℕ (m ℕ.∸ n))) (fromℕ-toℕ x) ⟩
  x + fromℕ (m ℕ.∸ n)         ≡⟨ cong (x +_) (fromℕ-homo-∸ m n) ⟩
  x + (fromℕ m ∸ fromℕ n)     ≡⟨ cong (x +_) (cong₂ _∸_ (fromℕ-toℕ y) (fromℕ-toℕ o)) ⟩
  x + (y ∸ o)                 ∎
  where
  open IneqReasoning;  k = toℕ x;  m = toℕ y;  n = toℕ o;  n≤m = toℕ-mono-≤ o≤y

x+y∸x+z :  ∀ x y z →  (x + y) ∸ (x + z) ≡ y ∸ z
x+y∸x+z x y z =  trans (sym (∸-+-assoc (x + y) x z)) (cong (_∸ z) ([x+y]∸x≡y x y))

suc[x]∸suc[y] :  ∀ x y → suc x ∸ suc y ≡ x ∸ y
suc[x]∸suc[y] x y =  trans (cong₂ _∸_ (suc≗1+ x) (suc≗1+ y)) (x+y∸x+z 1B x y)

∸-mono-≤ :  _∸_ Preserves₂ _≤_ ⟶ _≥_ ⟶ _≤_
∸-mono-≤ {x} {x'} {y} {y'} x≤x' y'≤y =  begin
  x ∸ y                   ≡⟨ sym (fromℕ-toℕ (x ∸ y)) ⟩
  fromℕ (toℕ (x ∸ y))     ≡⟨ cong fromℕ (toℕ-homo-∸ x y) ⟩
  fromℕ (xN ℕ.∸ yN)       ≤⟨ fromℕ-mono-≤ (ℕₚ.∸-mono xN≤x'N y'N≤yN) ⟩
  fromℕ (x'N ℕ.∸ y'N)     ≡⟨ fromℕ-homo-∸ x'N y'N ⟩
  fromℕ x'N ∸ fromℕ y'N   ≡⟨ cong₂ _∸_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' ∸ y'                 ∎
  where
  open IneqReasoning;  xN = toℕ x;  yN = toℕ y;  x'N = toℕ x';  y'N = toℕ y'

  xN≤x'N = toℕ-mono-≤ x≤x';   y'N≤yN = toℕ-mono-≤ y'≤y

∸-monoˡ-≤ :  ∀ x → (_∸ x) Preserves _≤_ ⟶ _≤_
∸-monoˡ-≤ x {y} {z} y≤z =  ∸-mono-≤ y≤z (≤-refl {x})

x∸y≤x :  ∀ x y → x ∸ y ≤ x
x∸y≤x x y =  begin
  x ∸ y    ≤⟨ ∸-mono-≤ (≤-refl {x}) (0≤x y) ⟩
  x ∸ 0B   ≡⟨ ∸-identityʳ x ⟩
  x        ∎
  where open IneqReasoning

x∸y<x :  ∀ {x y} → x ≢ 0B → y ≢ 0B → x ∸ y < x
x∸y<x {x} {y} x≢0 y≢0 =  begin-strict
  x ∸ y             ≡⟨ cong₂ _∸_ (sym (suc-pred x≢0)) (sym (suc-pred y≢0)) ⟩
  suc px ∸ suc py   ≡⟨ suc[x]∸suc[y] px py ⟩
  px ∸ py           ≤⟨ x∸y≤x px py ⟩
  px                <⟨ pred[x]<x x≢0 ⟩
  x                 ∎
  where open IneqReasoning;  px = pred x;  py = pred y

odd≢double :  ∀ x y → 1+[2 x ] ≢ double y
odd≢double x y 1+[2x]≡2y =  aux (x <? y)
  where
  open IneqReasoning
  2x = double x;   2y = double y;   2y≤1+[2x] = ≤-reflexive (sym 1+[2x]≡2y)
  1+[2x]≤2y = ≤-reflexive 1+[2x]≡2y

  2x+1≡1+[2x] =  begin-equality
    2x + 1B    ≡⟨ +-comm 2x 1B ⟩
    1B + 2x    ≡⟨ sym (suc≗1+ 2x) ⟩
    suc 2x     ≡⟨ sym (1+[2_]-suc-double x) ⟩
    1+[2 x ]   ∎

  aux : Dec (x < y) → ⊥
  aux (yes x<y) =  double≢1 (begin-equality
    double (y ∸ x)         ≡⟨ double-distrib-∸ y x ⟩
    2y ∸ 2x                ≡⟨ sym (suc-pred 2y∸2x≢0) ⟩
    suc (pred (2y ∸ 2x))   ≡⟨ cong suc (pred≗∸1 (2y ∸ 2x)) ⟩
    suc ((2y ∸ 2x) ∸ 1B)   ≡⟨ cong suc (∸-+-assoc 2y 2x 1B) ⟩
    suc (2y ∸ (2x + 1B))   ≡⟨ cong (suc ∘ (2y ∸_)) 2x+1≡1+[2x] ⟩
    suc (2y ∸ 1+[2 x ])    ≡⟨ cong suc (x≤y⇒x∸y≡0 2y≤1+[2x]) ⟩
    1B                     ∎)
    where
    2x<2y = double-mono-< x<y

    2y∸2x≢0 : 2y ∸ 2x ≢ 0B
    2y∸2x≢0 2y∸2x≡0 =  <⇒≱ 2x<2y 2y≤2x  where
                                        2y≤2x = x∸y≡0⇒x≤y 2y∸2x≡0

  aux (no x≮y) = suc≢0 $ begin-equality
    suc (2x ∸ 2y)   ≡⟨ suc≗1+ (2x ∸ 2y) ⟩
    1B + (2x ∸ 2y)  ≡⟨ sym (+-∸-assoc 1B 2y≤2x) ⟩
    (1B + 2x) ∸ 2y  ≡⟨ cong (_∸ 2y) (sym (suc≗1+ 2x)) ⟩
    (suc 2x) ∸ 2y   ≡⟨ cong (_∸ 2y) (sym (1+[2_]-suc-double x)) ⟩
    1+[2 x ] ∸ 2y   ≡⟨ x≤y⇒x∸y≡0 1+[2x]≤2y ⟩
    0B              ∎
    where y≤x = ≮⇒≥ x≮y;   2y≤2x = double-mono-≤ y≤x

*-cancelˡ-≡ :  ∀ {x} y z → x ≢ 0B → x * y ≡ x * z → y ≡ z
*-cancelˡ-≡ {x} y z x≢0 xy≡xz =  ≤-antisym y≤z z≤y
  where
  open IneqReasoning
  xy    = x * y;               xz    = x * z
  xy≤xz = ≤-reflexive xy≡xz;   xz≤xy = ≤-reflexive (sym xy≡xz)

  eq :  x * (y ∸ z) ≡ 0B
  eq =  trans (*-distribˡ-∸ x y z) (x≤y⇒x∸y≡0 xy≤xz)

  eq' :  x * (z ∸ y) ≡ 0B
  eq' =  trans (*-distribˡ-∸ x z y) (x≤y⇒x∸y≡0 xz≤xy)

  y≤z : y ≤ z
  y≤z with x*y≡0⇒x≡0∨y≡0 x eq
  ... | inj₁ x≡0   =  contradiction x≡0 x≢0
  ... | inj₂ y∸z≡0 =  x∸y≡0⇒x≤y y∸z≡0

  z≤y : z ≤ y
  z≤y with x*y≡0⇒x≡0∨y≡0 x eq'
  ... | inj₁ x≡0   =  contradiction x≡0 x≢0
  ... | inj₂ z∸y≡0 =  x∸y≡0⇒x≤y z∸y≡0

double-injective :  ∀ {x y} → double x ≡ double y → x ≡ y
double-injective {x} {y} 2x≡2y =  *-cancelˡ-≡ x y 2[1+x]≢0 (begin-equality
  2B * x     ≡⟨ sym (double≗2B* x) ⟩
  double x   ≡⟨ 2x≡2y ⟩
  double y   ≡⟨ double≗2B* y ⟩
  2B * y     ∎)
  where open IneqReasoning

