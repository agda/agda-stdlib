------------------------------------------------------------------------
-- The Agda standard library
--
-- Subtraction on Bin and some of its property proofs.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Binary.Minus where

open import Algebra using (Op₂; Magma)
open import Data.Empty using (⊥)
open import Data.Fin using (#_)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Binary.Base
open import Data.Nat.Binary.Properties
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using ([]; _∷_)
open import Function using (_∘_; _$_)
open import Level using (0ℓ)
open import Relation.Binary using (Tri; tri<; tri≈; tri>; _Preserves_⟶_;
                                                          _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Algebra.Definitions {A = ℕᵇ} _≡_
open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup
  using (xy∙z≈y∙xz; x∙yz≈y∙xz)
open import Algebra.Solver.CommutativeMonoid +-0-commutativeMonoid

infixl 6 _∸_

_∸_ : Op₂ ℕᵇ
zero     ∸ _        = 0ᵇ
x        ∸ zero     = x
2[1+ x ] ∸ 2[1+ y ] = double (x ∸ y)
1+[2 x ] ∸ 1+[2 y ] = double (x ∸ y)
2[1+ x ] ∸ 1+[2 y ] with x <? y
... | yes _ = 0ᵇ
... | no _  = 1+[2 (x ∸ y) ]
1+[2 x ] ∸ 2[1+ y ] with x ≤? y
... | yes _ = 0ᵇ
... | no _  = pred (double (x ∸ y))

------------------------------------------------------------------------
-- Properties of _∸_ and _≤_/_<_

x∸0≡x : ∀ x → x ∸ 0ᵇ ≡ x
x∸0≡x zero     = refl
x∸0≡x 2[1+ _ ] = refl
x∸0≡x 1+[2 _ ] = refl

even∸odd-for≥ : ∀ {x y} → x ≥ y → 2[1+ x ] ∸ 1+[2 y ] ≡ 1+[2 (x ∸ y) ]
even∸odd-for≥ {x} {y} x≥y with x <? y
... | no _    = refl
... | yes x<y = contradiction x≥y (<⇒≱ x<y)

odd∸even-for> : ∀ {x y} → x > y → 1+[2 x ] ∸ 2[1+ y ] ≡ pred (double (x ∸ y))
odd∸even-for> {x} {y} x>y with x ≤? y
... | no _    = refl
... | yes x≤y = contradiction x>y (≤⇒≯ x≤y)

x≤y⇒x∸y≡0 : ∀ {x y} → x ≤ y → x ∸ y ≡ 0ᵇ
x≤y⇒x∸y≡0 {zero} {_} _           = refl
x≤y⇒x∸y≡0 (inj₁ (even<even x<y)) = x≡0⇒double[x]≡0 (x≤y⇒x∸y≡0 (inj₁ x<y))
x≤y⇒x∸y≡0 {2[1+ x ]} {2[1+ x ]} (inj₂ refl) =
  x≡0⇒double[x]≡0 (x≤y⇒x∸y≡0 {x} {x} (inj₂ refl))
x≤y⇒x∸y≡0 {2[1+ x ]} {1+[2 y ]} (inj₁ (even<odd x<y)) with x <? y
... | yes _  = refl
... | no x≮y = contradiction x<y x≮y
x≤y⇒x∸y≡0 {1+[2 x ]} {2[1+ y ]} (inj₁ (odd<even x≤y)) with x ≤? y
... | yes _  = refl
... | no x≰y = contradiction x≤y x≰y
x≤y⇒x∸y≡0 {1+[2 _ ]} {2[1+ _ ]} (inj₂ ())
x≤y⇒x∸y≡0 {1+[2 _ ]} {1+[2 _ ]} (inj₁ (odd<odd x<y)) =
  x≡0⇒double[x]≡0 (x≤y⇒x∸y≡0 (inj₁ x<y))
x≤y⇒x∸y≡0 {1+[2 x ]} {1+[2 x ]} (inj₂ refl) =
  x≡0⇒double[x]≡0 (x≤y⇒x∸y≡0 (≤-refl {x}))

x∸x≡0 : ∀ x → x ∸ x ≡ 0ᵇ
x∸x≡0 x = x≤y⇒x∸y≡0 (≤-refl {x})

x>y⇒x∸y≢0 : ∀ {x y} → x > y → x ∸ y ≢ 0ᵇ
x>y⇒x∸y≢0 {x'@(2[1+ x ])} {zero} _ = subst (_≢ 0ᵇ) (sym (x∸0≡x x')) 2[1+x]≢0
x>y⇒x∸y≢0 {2[1+ _ ]} {2[1+ _ ]} (even<even y<x) = x≢0⇒double[x]≢0 (x>y⇒x∸y≢0 y<x)
x>y⇒x∸y≢0 {2[1+ x ]} {1+[2 y ]} (odd<even y≤x) with x <? y
... | no _    = 1+[2x]≢0 {x ∸ y}
... | yes x<y = contradiction y≤x (<⇒≱ x<y)
x>y⇒x∸y≢0 {x'@(1+[2 x ])} {y'@(2[1+ y ])} (even<odd y<x) =
  subst (_≢ 0ᵇ) (pred[2d]≡x'∸y') pred[2d]≢0
  where
  -- d = x ∸ y
  d≢0            = x>y⇒x∸y≢0 y<x
  pred[2d]≡x'∸y' = sym (odd∸even-for> y<x)
  1≤d            = x<y⇒suc[x]≤y (x≢0⇒x>0 d≢0)
  2≤2d           = double-mono-≤ 1≤d
  1≤pred[2d]     = pred-mono-≤ 2≤2d
  0<pred[2d]     = suc[x]≤y⇒x<y 1≤pred[2d]
  pred[2d]≢0     = >⇒≢ 0<pred[2d]
x>y⇒x∸y≢0 {1+[2 _ ]} {1+[2 _ ]} (odd<odd y<x) = x≢0⇒double[x]≢0 (x>y⇒x∸y≢0 y<x)

x∸y≡0⇒x≤y : ∀ {x y} → x ∸ y ≡ 0ᵇ → x ≤ y
x∸y≡0⇒x≤y {x} {y} x∸y≡0 with x ≤? y
... | yes leq = leq
... | no x≰y  = contradiction x∸y≡0 (x>y⇒x∸y≢0 (≰⇒> x≰y))

x<y⇒0<y∸x : ∀ {x y} → x < y → 0ᵇ < y ∸ x
x<y⇒0<y∸x {x} {y} x<y with <-cmp (y ∸ x) 0ᵇ
... | tri> _ _     gt = gt
... | tri≈ _ y∸x≡0 _  = contradiction (x∸y≡0⇒x≤y y∸x≡0) (<⇒≱ x<y)
... | tri< y∸x<0 _ _  = contradiction y∸x<0 x≮0

---------------------------------------------------------------
-- Properties of _∸_ and _+_ and _≤_

x≥y⇒x≡[x∸y]+y : ∀ {x y} → x ≥ y → x ≡ (x ∸ y) + y
x≥y⇒x≡[x∸y]+y {zero} {y} y≤0 = sym $ begin-equality
  (0ᵇ ∸ y) + y     ≡⟨ cong₂ _+_ (cong (0ᵇ ∸_) y≡0) y≡0 ⟩
  (0ᵇ ∸ 0ᵇ) + 0ᵇ   ≡⟨ +-identityʳ 0ᵇ ⟩
  0ᵇ               ∎
  where open ≤-Reasoning;  y≡0 = x≤0⇒x≡0 y≤0
x≥y⇒x≡[x∸y]+y {2[1+ _ ]}                      (inj₁ 0<even)          = refl
x≥y⇒x≡[x∸y]+y {x'@(2[1+ x ])} {y'@(2[1+ y ])} (inj₁ (even<even y<x)) =
  sym $ begin-equality
  x'∸y' + 2[1+ y ]                 ≡⟨ cong (x'∸y' +_) (2[1+_]-double-suc y) ⟩
  (double x∸y) + (double (suc y))  ≡⟨ sym (double-distrib-+ x∸y (suc y)) ⟩
  double (x∸y + suc y)             ≡⟨ cong double (+-comm x∸y (suc y)) ⟩
  double (suc y + x∸y)             ≡⟨ cong double (suc-+ y x∸y) ⟩
  double (suc (y + x∸y))           ≡⟨ cong (double ∘ suc) (+-comm y x∸y) ⟩
  double (suc (x∸y + y))           ≡⟨ cong (double ∘ suc) $ sym $
                                      x≥y⇒x≡[x∸y]+y (inj₁ y<x) ⟩
  double (suc x)                   ≡⟨ sym (2[1+_]-double-suc x) ⟩
  2[1+ x ]                         ∎
  where open ≤-Reasoning;  x∸y = x ∸ y;  x'∸y' = x' ∸ y'
x≥y⇒x≡[x∸y]+y {z@(2[1+ x ])} {2[1+ x ]} (inj₂ refl) = sym $ begin-equality
  (z ∸ z) + z   ≡⟨ cong (_+ z) (x∸x≡0 z) ⟩
  0ᵇ + z        ≡⟨ +-identityˡ z ⟩
  z             ∎
  where open ≤-Reasoning
x≥y⇒x≡[x∸y]+y {x'@(2[1+ x ])} {y'@(1+[2 y ])} (inj₁ (odd<even y≤x)) =
  sym $ begin-equality
  (x' ∸ y') + y'                       ≡⟨ cong (_+ y') (even∸odd-for≥ y≤x) ⟩
  1+[2 x∸y ] + y'                      ≡⟨ cong₂ _+_ (1+[2_]-suc-double x∸y)
                                                    (1+[2_]-suc-double y) ⟩
  suc (double x∸y) + suc (double y)    ≡⟨ cong₂ _+_ (suc≗1+ (double x∸y)) (suc≗1+ (double y)) ⟩
  (1ᵇ + double x∸y) + (1ᵇ + double y)  ≡⟨ eq ⟩
  2ᵇ + (double x∸y + double y)         ≡⟨ cong (2ᵇ +_) (sym (double-distrib-+ x∸y y)) ⟩
  2ᵇ + double (x∸y + y)                ≡⟨ cong ((2ᵇ +_) ∘ double) $ sym $
                                         x≥y⇒x≡[x∸y]+y y≤x ⟩
  double 1ᵇ + double x                 ≡⟨ sym (double-distrib-+ 1ᵇ x) ⟩
  double (1ᵇ + x)                      ≡⟨ cong double (sym (suc≗1+ x)) ⟩
  double (suc x)                       ≡⟨ sym (2[1+_]-double-suc x) ⟩
  2[1+ x ]                             ∎
  where
  open ≤-Reasoning
  x∸y = x ∸ y
  eq = let _+_ = _⊕_;  a = var (# 0);  b = var (# 1);  c = var (# 2)
       in
       prove 3 ((a + b) + (a + c)) ((a + a) + (b + c)) (1ᵇ ∷ (double x∸y) ∷ (double y) ∷ [])
x≥y⇒x≡[x∸y]+y {1+[2 x ]}      {zero}          (inj₁ 0<odd)          = refl
x≥y⇒x≡[x∸y]+y {x'@(1+[2 x ])} {y'@(2[1+ y ])} (inj₁ (even<odd y<x)) = sym $ begin-equality
  (x' ∸ y') + y'                        ≡⟨ cong₂ _+_ (odd∸even-for> y<x)
                                                     (2[1+_]-double-suc y) ⟩
  pred (double x∸y) + (double (suc y))  ≡⟨ pred[x]+y≡x+pred[y] 2[x∸y]≢0 2[suc[y]]≢0 ⟩
  2[x∸y] + pred (double (suc y))        ≡⟨ cong ((2[x∸y] +_) ∘ pred) (double-suc y) ⟩
  2[x∸y] + pred (suc 1ᵇ + 2y)           ≡⟨ cong ((2[x∸y] +_) ∘ pred) (suc-+ 1ᵇ 2y) ⟩
  2[x∸y] + pred (suc (1ᵇ + 2y))         ≡⟨ cong (2[x∸y] +_) (pred-suc (1ᵇ + 2y)) ⟩
  2[x∸y] + (1ᵇ + 2y)                    ≡⟨ x∙yz≈y∙xz 2[x∸y] 1ᵇ 2y ⟩
  1ᵇ + (2[x∸y] + 2y)                    ≡⟨ cong (1ᵇ +_) $ sym $ double-distrib-+ x∸y y ⟩
  1ᵇ + double (x∸y + y)                 ≡⟨ cong ((1ᵇ +_) ∘ double) $ sym $
                                           x≥y⇒x≡[x∸y]+y (inj₁ y<x) ⟩
  1ᵇ + 2x                               ≡⟨ sym (suc≗1+ 2x) ⟩
  suc 2x                                ≡⟨ sym (1+[2_]-suc-double x) ⟩
  x'                                    ∎
  where
  open ≤-Reasoning
  x∸y = x ∸ y;  2x = double x;  2y = double y;  2[x∸y] = double x∸y;  x∸y>0 = x<y⇒0<y∸x y<x
  x∸y≢0       = >⇒≢ x∸y>0
  2[x∸y]≢0    = x≢0⇒double[x]≢0 x∸y≢0
  2[suc[y]]≢0 = x≢0⇒double[x]≢0 (suc≢0 {y})
x≥y⇒x≡[x∸y]+y {x'@(1+[2 x ])} {y'@(1+[2 y ])} (inj₁ (odd<odd y<x)) = sym $ begin-equality
  (x' ∸ y') + y'                 ≡⟨ cong ((x' ∸ y') +_) (1+[2_]-suc-double y) ⟩
  double x∸y + (suc (double y))  ≡⟨ x+suc[y]≡suc[x]+y (double x∸y) (double y) ⟩
  suc (double x∸y) + double y    ≡⟨ suc-+ (double x∸y) (double y) ⟩
  suc (double x∸y + double y)    ≡⟨ cong suc $ sym $ double-distrib-+ x∸y y ⟩
  suc (double (x∸y + y))         ≡⟨ sym (1+[2_]-suc-double _) ⟩
  1+[2 (x∸y + y) ]               ≡⟨ cong 1+[2_] $ sym $ x≥y⇒x≡[x∸y]+y (inj₁ y<x) ⟩
  1+[2 x ]                       ∎
  where open ≤-Reasoning;  x∸y = x ∸ y
x≥y⇒x≡[x∸y]+y {x'@(1+[2 x ])} {1+[2 x ]} (inj₂ refl) = sym $ begin-equality
  (x' ∸ x') + x'  ≡⟨ cong (_+ x') (x∸x≡0 x') ⟩
  0ᵇ + x'         ≡⟨ sym (+-identityˡ x') ⟩
  x'              ∎
  where open ≤-Reasoning

[x+y]∸y≡x : ∀ x y → (x + y) ∸ y ≡ x
[x+y]∸y≡x x y = sym x≡d
  where
  d       = (x + y) ∸ y;           y≤x+y = x≤y+x y x
  x+y≡d+y = x≥y⇒x≡[x∸y]+y y≤x+y;   x≡d   = +-cancelʳ-≡ x d x+y≡d+y

[x+y]∸x≡y : ∀ x y → (x + y) ∸ x ≡ y
[x+y]∸x≡y x y = trans (cong (_∸ x) (+-comm x y)) ([x+y]∸y≡x y x)

∸-identityʳ : RightIdentity 0ᵇ _∸_
∸-identityʳ x = trans (cong (_∸ 0ᵇ) $ sym $ +-identityʳ x) ([x+y]∸y≡x x 0ᵇ)

x+[y∸x]≡y : ∀ {x y} → x ≤ y → x + (y ∸ x) ≡ y
x+[y∸x]≡y {x} {y} x≤y = begin-equality
  x + (y ∸ x)   ≡⟨ +-comm x _ ⟩
  (y ∸ x) + x   ≡⟨ sym (x≥y⇒x≡[x∸y]+y x≤y) ⟩
  y             ∎
  where open ≤-Reasoning

[x∸y]+y≡x : ∀ {x y} → y ≤ x → (x ∸ y) + y ≡ x
[x∸y]+y≡x {x} {y} y≤x = trans (+-comm (x ∸ y) y) (x+[y∸x]≡y y≤x)

toℕ-homo-∸ : ∀ x y → toℕ (x ∸ y) ≡ (toℕ x) ℕ.∸ (toℕ y)
toℕ-homo-∸ x y with <-cmp x y
... | tri< x<y _ _ = begin
  toℕ (x ∸ y)   ≡⟨ cong toℕ (x≤y⇒x∸y≡0 x≤y) ⟩
  toℕ 0ᵇ        ≡⟨⟩
  0             ≡⟨ sym (ℕₚ.m≤n⇒m∸n≡0 m≤n) ⟩
  m ℕ.∸ n       ∎
  where
  open ≡-Reasoning
  m = toℕ x;  n = toℕ y;  x≤y = <⇒≤ x<y;  m≤n = toℕ-mono-≤ x≤y
... | tri≈ _ x≡y _ = begin
  toℕ (x ∸ y)  ≡⟨ cong toℕ (x≤y⇒x∸y≡0 {x} {y} x≤y) ⟩
  toℕ 0ᵇ       ≡⟨⟩
  0            ≡⟨ sym (ℕₚ.m≤n⇒m∸n≡0 m≤n) ⟩
  m ℕ.∸ n      ∎
  where
  open ≡-Reasoning
  m = toℕ x;   n = toℕ y;   x≤y = ≤-reflexive x≡y;   m≤n = toℕ-mono-≤ x≤y
... | tri> _ _ y<x = begin
  toℕ (x ∸ y)                    ≡⟨ sym (ℕₚ.m+n∸n≡m (toℕ (x ∸ y)) n) ⟩
  ((toℕ (x ∸ y)) ℕ.+ n) ℕ.∸ n    ≡⟨ cong (ℕ._∸ n) eq ⟩
  ((m ℕ.∸ n) ℕ.+ n) ℕ.∸ n        ≡⟨ ℕₚ.m+n∸n≡m (m ℕ.∸ n) n ⟩
  m ℕ.∸ n                        ∎
  where
  open ≡-Reasoning
  m = toℕ x;   n = toℕ y;   y≤x = <⇒≤ y<x;   n≤m = toℕ-mono-≤ y≤x
  eq = begin
    toℕ (x ∸ y) ℕ.+ n    ≡⟨ sym (toℕ-homo-+ (x ∸ y) y) ⟩
    toℕ ((x ∸ y) + y)    ≡⟨ cong toℕ (+-comm (x ∸ y) y) ⟩
    toℕ (y + (x ∸ y))    ≡⟨ cong toℕ (x+[y∸x]≡y y≤x) ⟩
    m                    ≡⟨ sym (ℕₚ.m+[n∸m]≡n n≤m) ⟩
    n ℕ.+ (m ℕ.∸ n)      ≡⟨ ℕₚ.+-comm n (m ℕ.∸ n) ⟩
    (m ℕ.∸ n) ℕ.+ n      ∎

∸-magma : Magma 0ℓ 0ℓ
∸-magma = magma _∸_

import Algebra.Morphism.TwoMagmas ∸-magma ℕₚ.∸-magma
  as Magmas∸ℕᵇ-ℕ

fromℕ-homo-∸ : ∀ m n → fromℕ (m ℕ.∸ n) ≡ (fromℕ m) ∸ (fromℕ n)
fromℕ-homo-∸ = Magmas∸ℕᵇ-ℕ.IsHomo⇒IsHomo-rev toℕ fromℕ (cong fromℕ)
                                             (toℕ-fromℕ , fromℕ-toℕ) toℕ-homo-∸

∸-+-assoc : ∀ x y o → (x ∸ y) ∸ o ≡ x ∸ (y + o)
∸-+-assoc x y o = begin-equality
  (x ∸ y) ∸ o                     ≡⟨ sym (fromℕ-toℕ ((x ∸ y) ∸ o)) ⟩
  fromℕ (toℕ ((x ∸ y) ∸ o))       ≡⟨ cong fromℕ (toℕ-homo-∸ (x ∸ y) o) ⟩
  fromℕ (toℕ (x ∸ y) ℕ.∸ n)       ≡⟨ cong (fromℕ ∘ (ℕ._∸ n)) (toℕ-homo-∸ x y) ⟩
  fromℕ ((k ℕ.∸ m) ℕ.∸ n)         ≡⟨ cong fromℕ (ℕₚ.∸-+-assoc k m n) ⟩
  fromℕ (k ℕ.∸ (m ℕ.+ n))         ≡⟨ fromℕ-homo-∸ k (m ℕ.+ n) ⟩
  fromℕ k ∸ fromℕ (m ℕ.+ n)       ≡⟨ cong ((fromℕ k) ∸_) (fromℕ-homo-+ m n) ⟩
  fromℕ k ∸ (fromℕ m + fromℕ n)   ≡⟨ cong ((fromℕ k) ∸_) $
                                     cong₂ _+_ (fromℕ-toℕ y) (fromℕ-toℕ o) ⟩
  fromℕ k ∸ (y + o)               ≡⟨ cong (_∸ (y + o)) (fromℕ-toℕ x) ⟩
  x ∸ (y + o)                     ∎
  where open ≤-Reasoning;  k = toℕ x;  m = toℕ y;  n = toℕ o

+-∸-assoc : ∀ x {y o} → o ≤ y → (x + y) ∸ o ≡ x + (y ∸ o)
+-∸-assoc x {y} {o} o≤y = begin-equality
  (x + y) ∸ o                  ≡⟨ sym (fromℕ-toℕ ((x + y) ∸ o)) ⟩
  fromℕ (toℕ ((x + y) ∸ o))    ≡⟨ cong fromℕ (toℕ-homo-∸ (x + y) o) ⟩
  fromℕ (toℕ (x + y) ℕ.∸ n)    ≡⟨ cong (fromℕ ∘ (ℕ._∸ n)) (toℕ-homo-+ x y) ⟩
  fromℕ ((k ℕ.+ m) ℕ.∸ n)      ≡⟨ cong fromℕ (ℕₚ.+-∸-assoc k n≤m) ⟩
  fromℕ (k ℕ.+ (m ℕ.∸ n))      ≡⟨ fromℕ-homo-+ k (m ℕ.∸ n) ⟩
  fromℕ k + fromℕ (m ℕ.∸ n)    ≡⟨ cong (_+ (fromℕ (m ℕ.∸ n))) (fromℕ-toℕ x) ⟩
  x + fromℕ (m ℕ.∸ n)          ≡⟨ cong (x +_) (fromℕ-homo-∸ m n) ⟩
  x + (fromℕ m ∸ fromℕ n)      ≡⟨ cong (x +_) $ cong₂ _∸_ (fromℕ-toℕ y) (fromℕ-toℕ o) ⟩
  x + (y ∸ o)                  ∎
  where
  open ≤-Reasoning
  k = toℕ x;  m = toℕ y;  n = toℕ o;  n≤m = toℕ-mono-≤ o≤y

x+y∸x+z : ∀ x y z → (x + y) ∸ (x + z) ≡ y ∸ z
x+y∸x+z x y z = begin-equality
  (x + y) ∸ (x + z)    ≡⟨ sym (∸-+-assoc (x + y) x z) ⟩
  ((x + y) ∸ x) ∸ z    ≡⟨ cong (_∸ z) ([x+y]∸x≡y x y) ⟩
  y ∸ z                ∎
  where open ≤-Reasoning

suc[x]∸suc[y] : ∀ x y → suc x ∸ suc y ≡ x ∸ y
suc[x]∸suc[y] x y = begin-equality
  suc x ∸ suc y         ≡⟨ cong₂ _∸_ (suc≗1+ x) (suc≗1+ y) ⟩
  (1ᵇ + x) ∸ (1ᵇ + y)   ≡⟨ x+y∸x+z 1ᵇ x y ⟩
  x ∸ y                 ∎
  where open ≤-Reasoning

∸-mono-≤ : _∸_ Preserves₂ _≤_ ⟶ _≥_ ⟶ _≤_
∸-mono-≤ {x} {x'} {y} {y'} x≤x' y'≤y = begin
  x ∸ y                   ≡⟨ sym (fromℕ-toℕ (x ∸ y)) ⟩
  fromℕ (toℕ (x ∸ y))     ≡⟨ cong fromℕ (toℕ-homo-∸ x y) ⟩
  fromℕ (xN ℕ.∸ yN)       ≤⟨ fromℕ-mono-≤ (ℕₚ.∸-mono xN≤x'N y'N≤yN) ⟩
  fromℕ (x'N ℕ.∸ y'N)     ≡⟨ fromℕ-homo-∸ x'N y'N ⟩
  fromℕ x'N ∸ fromℕ y'N   ≡⟨ cong₂ _∸_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' ∸ y'                 ∎
  where
  open ≤-Reasoning
  xN = toℕ x;   yN = toℕ y;   x'N = toℕ x';   y'N = toℕ y'

  xN≤x'N = toℕ-mono-≤ x≤x';   y'N≤yN = toℕ-mono-≤ y'≤y

∸-monoˡ-≤ : (x : ℕᵇ) → (_∸ x) Preserves _≤_ ⟶ _≤_
∸-monoˡ-≤ x y≤z = ∸-mono-≤ y≤z (≤-refl {x})

∸-monoʳ-≤ : (x : ℕᵇ) → (x ∸_) Preserves _≥_ ⟶ _≤_
∸-monoʳ-≤ x y≥z = ∸-mono-≤ (≤-refl {x}) y≥z

x∸y≤x : ∀ x y → x ∸ y ≤ x
x∸y≤x x y = begin
  x ∸ y    ≤⟨ ∸-monoʳ-≤ x (0≤x y) ⟩
  x ∸ 0ᵇ   ≡⟨ x∸0≡x x ⟩
  x        ∎
  where open ≤-Reasoning

x∸y<x : {x y : ℕᵇ} → x ≢ 0ᵇ → y ≢ 0ᵇ → x ∸ y < x
x∸y<x {x} {y} x≢0 y≢0 = begin-strict
  x ∸ y              ≡⟨ cong₂ _∸_ (sym (suc-pred x≢0)) (sym (suc-pred y≢0)) ⟩
  suc px ∸ suc py    ≡⟨ suc[x]∸suc[y] px py ⟩
  px ∸ py            ≤⟨ x∸y≤x px py ⟩
  px                 <⟨ pred[x]<x x≢0 ⟩
  x                  ∎
  where open ≤-Reasoning;  px = pred x;  py = pred y

------------------------------------------------------------------------
-- Properties of _∸_ and _*_

*-distribˡ-∸ :  _*_ DistributesOverˡ _∸_
*-distribˡ-∸ x y z = begin-equality
  x * (y ∸ z)                         ≡⟨ sym (fromℕ-toℕ (x * (y ∸ z))) ⟩
  fromℕ (toℕ (x * (y ∸ z)))           ≡⟨ cong fromℕ (toℕ-homo-* x (y ∸ z)) ⟩
  fromℕ (k ℕ.* (toℕ (y ∸ z)))         ≡⟨ cong (fromℕ ∘ (k ℕ.*_)) (toℕ-homo-∸ y z) ⟩
  fromℕ (k ℕ.* (m ℕ.∸ n))             ≡⟨ cong fromℕ (ℕₚ.*-distribˡ-∸ k m n) ⟩
  fromℕ ((k ℕ.* m) ℕ.∸ (k ℕ.* n))     ≡⟨ fromℕ-homo-∸ (k ℕ.* m) (k ℕ.* n) ⟩
  fromℕ (k ℕ.* m) ∸ fromℕ (k ℕ.* n)   ≡⟨ cong₂ _∸_ (fromℕ-homo-* k m)
                                                   (fromℕ-homo-* k n) ⟩
  (fromℕ k * fromℕ m) ∸ (fromℕ k * fromℕ n)
                                      ≡⟨ cong₂ _∸_ (cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ y))
                                                   (cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ z)) ⟩
  x * y ∸ x * z                       ∎
  where
  open ≤-Reasoning;  k = toℕ x;  m = toℕ y;  n = toℕ z

*-distribʳ-∸ : _*_ DistributesOverʳ _∸_
*-distribʳ-∸ x y z = begin-equality
  (y ∸ z) * x     ≡⟨ *-comm _ x ⟩
  x * (y ∸ z)     ≡⟨ *-distribˡ-∸ x y z ⟩
  x * y ∸ x * z   ≡⟨ cong₂ _∸_ (*-comm x y) (*-comm x z) ⟩
  y * x ∸ z * x   ∎
  where open ≤-Reasoning
