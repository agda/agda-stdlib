------------------------------------------------------------------------
-- The Agda standard library
--
-- Subtraction on Bin and some of its property proofs.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Binary.Minus where

open import Data.Nat.Binary.Base
open import Data.Nat.Binary.Properties
open import Data.Empty using (⊥)
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; _$_)
open import Relation.Binary using (Tri; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality as P using
  (_≡_; _≢_; _≗_; refl; sym; trans; cong; cong₂; resp₂; subst)
import Relation.Binary.Reasoning.Base.Triple as InequalityReasoning
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Algebra.FunctionProperties {A = ℕᵇ} _≡_
open import Algebra.Properties.CommutativeSemigroup +-semigroup +-comm
     using (xy∙z≈y∙xz; x∙yz≈y∙xz; xy∙zu≈xz∙yu)

private
  module IneqReasoning = InequalityReasoning {A = ℕᵇ} {_≈_ = _≡_} ≤-isPreorder
                                   <-trans (resp₂ _<_) <⇒≤ <-≤-trans ≤-<-trans
open ℕᵇ
open Tri
open _<_

Minus : ℕᵇ → ℕᵇ → Set                                 -- result of subtraction
Minus x y =  ℕᵇ × Tri (x < y) (x ≡ y) (x > y)

minus :  ∀ x y → Minus x y                            -- extended subtraction
minus zero     zero       =  (0ᵇ ,       tri-≈ refl)
minus zero     (2[1+ _ ]) =  (0ᵇ ,       tri-< 0<even)
minus zero     1+[2 _ ]   =  (0ᵇ ,       tri-< 0<odd)
minus 2[1+ x ] zero       =  (2[1+ x ] , tri-> 0<even)
minus 2[1+ x ] 2[1+ y ]   with minus x y
... | (d , cmp) = (double d , even<even-mono-cmp cmp)
minus 2[1+ x ] 1+[2 y ]  with minus x y
... | (_ , tri< x<y _   _)   =  (0ᵇ  , tri-< (even<odd x<y))
... | (d , tri≈ _   x≡y _)   =  (1+[2 d ] , tri-> (odd<even (inj₂ (sym x≡y))))
... | (d , tri> _   _   x>y) =  (1+[2 d ] , tri-> (odd<even (inj₁ x>y)))
minus 1+[2 x ] zero      =  (1+[2 x ] , tri-> 0<odd)
minus 1+[2 x ] 2[1+ y ]  with minus x y
... | (_ , tri< x<y _  _)   =  (0ᵇ , tri-< (odd<even (inj₁ x<y)))
... | (_ , tri≈ _   eq _)   =  (0ᵇ , tri-< (odd<even (inj₂ eq)))
... | (d , tri> _   _  x>y) =  (pred (double d) , tri-> (even<odd x>y))
minus 1+[2 x ] 1+[2 y ]  with minus x y
... | (d , cmp) =  (double d , odd<odd-mono-cmp cmp)

infixl 6 _∸_

_∸_ : Op₂ ℕᵇ              -- traditional subtraction
_∸_ x =  proj₁ ∘ minus x

0∸x≡0 :  ∀ x → 0ᵇ ∸ x ≡ 0ᵇ
0∸x≡0 zero     =  refl
0∸x≡0 2[1+ _ ] =  refl
0∸x≡0 1+[2 _ ] =  refl

x∸0≡x :  ∀ x → x ∸ 0ᵇ ≡ x
x∸0≡x zero     =  refl
x∸0≡x 2[1+ _ ] =  refl
x∸0≡x 1+[2 _ ] =  refl

even∸odd-for≥ :  ∀ {x y} → x ≥ y → 2[1+ x ] ∸ 1+[2 y ] ≡ 1+[2 (x ∸ y) ]
even∸odd-for≥ {x} {y} x≥y  with minus x y
... | (_ , tri< x<y _ _) =  contradiction x≥y (<⇒≱ x<y)
... | (_ , tri≈ _   _ _) =  refl
... | (_ , tri> _   _ _) =  refl

odd∸even-for> :  ∀ {x y} → x > y → 1+[2 x ] ∸ 2[1+ y ] ≡ pred (double (x ∸ y))
odd∸even-for> {x} {y} x>y  with minus x y
... | (_ , tri< x<y _   _) =  contradiction x>y (<⇒≯ x<y)
... | (_ , tri≈ _   x≡y _) =  contradiction x≡y (>⇒≢ x>y)
... | (_ , tri> _   _   _) =  refl

x≤y⇒x∸y≡0 :  ∀ {x y} → x ≤ y → x ∸ y ≡ 0ᵇ
x≤y⇒x∸y≡0 {zero} {y} _                       =  0∸x≡0 y
x≤y⇒x∸y≡0 (inj₁ (even<even x<y))             =  x≡0⇒double[x]≡0 (x≤y⇒x∸y≡0 (inj₁ x<y))
x≤y⇒x∸y≡0 {2[1+ x ]} {2[1+ .x ]} (inj₂ refl) =  x≡0⇒double[x]≡0 (x≤y⇒x∸y≡0 {x} {x} (inj₂ refl))
x≤y⇒x∸y≡0 {2[1+ x ]} {1+[2 y ]} (inj₁ (even<odd x<y))  with minus x y
... | (0ᵇ , tri< _ _   _  ) =  refl
... | (_ ,  tri≈ _ x≡y _  ) =  contradiction x≡y (<⇒≢ x<y)
... | (_ ,  tri> _ _   x>y) =  contradiction x>y (<⇒≯ x<y)

x≤y⇒x∸y≡0 {1+[2 x ]} {2[1+ y ]} (inj₁ (odd<even x≤y))  with minus x y
... | (_ , tri< _ _ _  ) =  refl
... | (_ , tri≈ _ _ _  ) =  refl
... | (_ , tri> _ _ x>y) =  contradiction x>y (≤⇒≯ x≤y)

x≤y⇒x∸y≡0 {1+[2 _ ]} {2[1+ _ ]} (inj₂ ())

x≤y⇒x∸y≡0 {1+[2 _ ]} {1+[2 _ ]}  (inj₁ (odd<odd x<y)) =  x≡0⇒double[x]≡0 (x≤y⇒x∸y≡0 (inj₁ x<y))
x≤y⇒x∸y≡0 {1+[2 x ]} {1+[2 .x ]} (inj₂ refl)          =
  x≡0⇒double[x]≡0 (x≤y⇒x∸y≡0 {x} {x} (inj₂ refl))

x∸x≡0 :  ∀ x → x ∸ x ≡ 0ᵇ
x∸x≡0 x =  x≤y⇒x∸y≡0 (≤-refl {x})

y<x⇒x∸y≢0 :  ∀ {x y} → y < x → x ∸ y ≢ 0ᵇ
y<x⇒x∸y≢0 {zero} {_} ()
y<x⇒x∸y≢0 {x'@(2[1+ x ])} {zero} _ = subst (_≢ 0ᵇ) (sym x'∸0≡x') 2[1+x]≢0  where
                                                                           x'∸0≡x' = x∸0≡x x'
y<x⇒x∸y≢0 {2[1+ _ ]} {2[1+ _ ]} (even<even y<x)  =  x≢0⇒double[x]≢0 (y<x⇒x∸y≢0 y<x)
y<x⇒x∸y≢0 {2[1+ x ]} {1+[2 y ]} (odd<even y≤x)   with minus x y
... | (_ , tri< x<y _ _) =  contradiction y≤x (<⇒≱ x<y)
... | (d , tri≈ _   _ _) =  1+[2x]≢0 {d}
... | (d , tri> _   _ _) =  1+[2x]≢0 {d}
y<x⇒x∸y≢0 {x'@(1+[2 x ])} {y'@(2[1+ y ])} (even<odd y<x) =
  subst (_≢ 0ᵇ) (sym x'∸y'≡pred[2d]) pred[2d]≢0
  where
  -- d = x ∸ y
  d≢0        = y<x⇒x∸y≢0 y<x;                x'∸y'≡pred[2d] = odd∸even-for> y<x
  1≤d        = x<y⇒suc[x]≤y (x≢0⇒x>0 d≢0);   2≤2d           = double-mono-≤ 1≤d
  1≤pred[2d] = pred-mono-≤ 2≤2d;             0<pred[2d]     = suc[x]≤y⇒x<y 1≤pred[2d]
  pred[2d]≢0 = >⇒≢ 0<pred[2d]

y<x⇒x∸y≢0 {1+[2 _ ]} {1+[2 _ ]} (odd<odd y<x) =  x≢0⇒double[x]≢0 (y<x⇒x∸y≢0 y<x)

x∸y≡0⇒x≤y :  ∀ {x y} → x ∸ y ≡ 0ᵇ → x ≤ y
x∸y≡0⇒x≤y {x} {y} x∸y≡0  with x ≤? y
... | yes leq = leq
... | no x≰y  = contradiction x∸y≡0 (y<x⇒x∸y≢0 (≰⇒> x≰y))

x<y⇒0<y∸x :  ∀ {x y} → x < y → 0ᵇ < y ∸ x
x<y⇒0<y∸x {x} {y} x<y  with <-cmp (y ∸ x) 0ᵇ
... | tri> _ _     gt =  gt
... | tri≈ _ y∸x≡0 _  =  contradiction (x∸y≡0⇒x≤y y∸x≡0) (<⇒≱ x<y)
... | tri< y∸x<0 _ _  =  contradiction y∸x<0 x≮0

y≤x⇒x≡[x∸y]+y :  ∀ {x y} → y ≤ x → x ≡ (x ∸ y) + y    -- the defining property for _∸_
y≤x⇒x≡[x∸y]+y {zero} {y} y≤0 =  sym $ begin-equality
  (0ᵇ ∸ y) + y    ≡⟨ cong₂ _+_ (cong (0ᵇ ∸_) y≡0) y≡0 ⟩
  (0ᵇ ∸ 0ᵇ) + 0ᵇ  ≡⟨ +-identityʳ 0ᵇ ⟩
  0ᵇ              ∎
  where open IneqReasoning;  y≡0 = x≤0⇒x≡0 y≤0

y≤x⇒x≡[x∸y]+y {x} {zero} _ =  sym $ begin-equality
  (x ∸ 0ᵇ) + 0ᵇ   ≡⟨ +-identityʳ (x ∸ 0ᵇ) ⟩
  x ∸ 0ᵇ          ≡⟨ x∸0≡x x ⟩
  x               ∎
  where open IneqReasoning

y≤x⇒x≡[x∸y]+y {x'@(2[1+ x ])} {y'@(2[1+ y ])} (inj₁ (even<even y<x)) =
  sym $ begin-equality
  x'∸y' + 2[1+ y ]                 ≡⟨ cong (x'∸y' +_) (2[1+_]-double-suc y) ⟩
  (double x∸y) + (double (suc y))  ≡⟨ sym (double-distrib-+ x∸y (suc y)) ⟩
  double (x∸y + suc y)             ≡⟨ cong double (+-comm x∸y (suc y)) ⟩
  double (suc y + x∸y)             ≡⟨ cong double (suc-+ y x∸y) ⟩
  double (suc (y + x∸y))           ≡⟨ cong (double ∘ suc) (+-comm y x∸y) ⟩
  double (suc (x∸y + y))           ≡⟨ cong (double ∘ suc) $ sym $ y≤x⇒x≡[x∸y]+y (inj₁ y<x) ⟩
  double (suc x)                   ≡⟨ sym (2[1+_]-double-suc x) ⟩
  2[1+ x ]                         ∎
  where open IneqReasoning;  x∸y = x ∸ y;  x'∸y' = x' ∸ y'

y≤x⇒x≡[x∸y]+y {z@(2[1+ x ])} {2[1+ .x ]} (inj₂ refl) =  sym $ begin-equality
  (z ∸ z) + z   ≡⟨ cong (_+ z) (x∸x≡0 z) ⟩
  0ᵇ + z        ≡⟨ +-identityˡ z ⟩
  z             ∎
  where open IneqReasoning

y≤x⇒x≡[x∸y]+y {x'@(2[1+ x ])} {y'@(1+[2 y ])} (inj₁ (odd<even y≤x)) =
  sym $ begin-equality
  (x' ∸ y') + y'                       ≡⟨ cong (_+ y') (even∸odd-for≥ y≤x) ⟩
  1+[2 x∸y ] + y'                      ≡⟨ cong₂ _+_ (1+[2_]-suc-double x∸y)
                                                    (1+[2_]-suc-double y) ⟩
  suc (double x∸y) + suc (double y)    ≡⟨ cong₂ _+_ (suc≗1+ (double x∸y)) (suc≗1+ (double y)) ⟩
  (1ᵇ + double x∸y) + (1ᵇ + double y)  ≡⟨ xy∙zu≈xz∙yu 1ᵇ (double x∸y) 1ᵇ (double y) ⟩
  2ᵇ + (double x∸y + double y)         ≡⟨ cong (2ᵇ +_) (sym (double-distrib-+ x∸y y)) ⟩
  2ᵇ + double (x∸y + y)                ≡⟨ cong ((2ᵇ +_) ∘ double) $ sym $ y≤x⇒x≡[x∸y]+y y≤x ⟩
  double 1ᵇ + double x                 ≡⟨ sym (double-distrib-+ 1ᵇ x) ⟩
  double (1ᵇ + x)                      ≡⟨ cong double (sym (suc≗1+ x)) ⟩
  double (suc x)                       ≡⟨ sym (2[1+_]-double-suc x) ⟩
  2[1+ x ]                             ∎
  where open IneqReasoning;  x∸y = x ∸ y

y≤x⇒x≡[x∸y]+y {x'@(1+[2 x ])} {y'@(2[1+ y ])} (inj₁ (even<odd y<x)) =  sym $ begin-equality
  (x' ∸ y') + y'                        ≡⟨ cong₂ _+_ (odd∸even-for> y<x) (2[1+_]-double-suc y) ⟩
  pred (double x∸y) + (double (suc y))  ≡⟨ pred[x]+y≡x+pred[y] 2[x∸y]≢0 2[suc[y]]≢0 ⟩
  2[x∸y] + pred (double (suc y))        ≡⟨ cong ((2[x∸y] +_) ∘ pred) (double-suc y) ⟩
  2[x∸y] + pred (suc 1ᵇ + 2y)           ≡⟨ cong ((2[x∸y] +_) ∘ pred) (suc-+ 1ᵇ 2y) ⟩
  2[x∸y] + pred (suc (1ᵇ + 2y))         ≡⟨ cong (2[x∸y] +_) (pred-suc (1ᵇ + 2y)) ⟩
  2[x∸y] + (1ᵇ + 2y)                    ≡⟨ x∙yz≈y∙xz 2[x∸y] 1ᵇ 2y ⟩
  1ᵇ + (2[x∸y] + 2y)                    ≡⟨ cong (1ᵇ +_) $ sym $ double-distrib-+ x∸y y ⟩
  1ᵇ + double (x∸y + y)                 ≡⟨ cong ((1ᵇ +_) ∘ double) $ sym $ y≤x⇒x≡[x∸y]+y (inj₁ y<x) ⟩
  1ᵇ + 2x                               ≡⟨ sym (suc≗1+ 2x) ⟩
  suc 2x                                ≡⟨ sym (1+[2_]-suc-double x) ⟩
  x'                                    ∎
  where
  open IneqReasoning
  x∸y = x ∸ y;  2x = double x;  2y = double y;  2[x∸y] = double x∸y;  x∸y>0 = x<y⇒0<y∸x y<x
  x∸y≢0       = >⇒≢ x∸y>0
  2[x∸y]≢0    = x≢0⇒double[x]≢0 x∸y≢0
  2[suc[y]]≢0 = x≢0⇒double[x]≢0 (suc≢0 {y})

y≤x⇒x≡[x∸y]+y {x'@(1+[2 x ])} {y'@(1+[2 y ])} (inj₁ (odd<odd y<x)) =  sym $ begin-equality
  (x' ∸ y') + y'                 ≡⟨ cong ((x' ∸ y') +_) (1+[2_]-suc-double y) ⟩
  double x∸y + (suc (double y))  ≡⟨ x+suc[y]≡suc[x]+y (double x∸y) (double y) ⟩
  suc (double x∸y) + double y    ≡⟨ suc-+ (double x∸y) (double y) ⟩
  suc (double x∸y + double y)    ≡⟨ cong suc $ sym $ double-distrib-+ x∸y y ⟩
  suc (double (x∸y + y))         ≡⟨ sym (1+[2_]-suc-double _) ⟩
  1+[2 (x∸y + y) ]               ≡⟨ cong 1+[2_] $ sym $ y≤x⇒x≡[x∸y]+y (inj₁ y<x) ⟩
  1+[2 x ]                       ∎
  where open IneqReasoning;  x∸y = x ∸ y

y≤x⇒x≡[x∸y]+y {x'@(1+[2 x ])} {1+[2 .x ]} (inj₂ refl) =  sym $ begin-equality
  (x' ∸ x') + x'  ≡⟨ cong (_+ x') (x∸x≡0 x') ⟩
  0ᵇ + x'         ≡⟨ sym (+-identityˡ x') ⟩
  x'              ∎
  where open IneqReasoning


[x+y]∸y≡x :  ∀ x y → (x + y) ∸ y ≡ x
[x+y]∸y≡x x y =  sym x≡d
  where
  d       = (x + y) ∸ y;           y≤x+y = x≤y+x y x
  x+y≡d+y = y≤x⇒x≡[x∸y]+y y≤x+y;   x≡d   = +-cancelʳ-≡ x d x+y≡d+y

[x+y]∸x≡y :  ∀ x y → (x + y) ∸ x ≡ y
[x+y]∸x≡y x y =  trans (cong (_∸ x) (+-comm x y)) ([x+y]∸y≡x y x)

∸-identityʳ :  RightIdentity 0ᵇ _∸_
∸-identityʳ x =  trans (cong (_∸ 0ᵇ) $ sym $ +-identityʳ x) ([x+y]∸y≡x x 0ᵇ)

x+[y∸x]≡y :  ∀ {x y} → x ≤ y → x + (y ∸ x) ≡ y
x+[y∸x]≡y {x} {y} x≤y =  begin-equality
  x + (y ∸ x)   ≡⟨ +-comm x _ ⟩
  (y ∸ x) + x   ≡⟨ sym (y≤x⇒x≡[x∸y]+y x≤y) ⟩
  y             ∎
  where open IneqReasoning

