------------------------------------------------------------------------
-- The Agda standard library
--
-- Subtraction on Bin and some of its properties.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Binary.Subtraction where

open import Algebra.Core using (Op₂)
open import Algebra.Bundles using (Magma)
open import Algebra.Consequences.Propositional using (comm∧distrˡ⇒distrʳ)
open import Algebra.Morphism.Consequences using (homomorphic₂-inv)
open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Binary.Base using (ℕᵇ; 0ᵇ; 2[1+_]; 1+[2_]; double;
  pred; toℕ; fromℕ; even<odd; odd<even; _≥_; _>_; _≤_; _<_; _+_; zero; suc; 1ᵇ;
  _*_)
open import Data.Nat.Binary.Properties
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using ([]; _∷_)
open import Function.Base using (_∘_; _$_)
open import Level using (0ℓ)
open import Relation.Binary
  using (Tri; tri<; tri≈; tri>; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality.Algebra using (magma)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂; sym; trans; subst; _≢_)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Negation using (contradiction)

open import Algebra.Definitions {A = ℕᵇ} _≡_
open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup
  using (xy∙z≈y∙xz; x∙yz≈y∙xz)
open import Algebra.Solver.CommutativeMonoid +-0-commutativeMonoid

private
  variable
    x y : ℕᵇ

------------------------------------------------------------------------
-- Definition

infixl 6 _∸_

_∸_ : Op₂ ℕᵇ
zero     ∸ _        = 0ᵇ
x        ∸ zero     = x
2[1+ x ] ∸ 2[1+ y ] = double (x ∸ y)
1+[2 x ] ∸ 1+[2 y ] = double (x ∸ y)
2[1+ x ] ∸ 1+[2 y ] = if does (x <? y) then 0ᵇ else 1+[2 (x ∸ y) ]
1+[2 x ] ∸ 2[1+ y ] = if does (x ≤? y) then 0ᵇ else pred (double (x ∸ y))

------------------------------------------------------------------------
-- Properties of _∸_ and _≡_

∸-magma : Magma 0ℓ 0ℓ
∸-magma = magma _∸_

x∸0≡x : ∀ x → x ∸ 0ᵇ ≡ x
x∸0≡x zero     = refl
x∸0≡x 2[1+ _ ] = refl
x∸0≡x 1+[2 _ ] = refl

x∸x≡0 : ∀ x → x ∸ x ≡ 0ᵇ
x∸x≡0 zero     = refl
x∸x≡0 2[1+ x ] = x≡0⇒double[x]≡0 (x∸x≡0 x)
x∸x≡0 1+[2 x ] = x≡0⇒double[x]≡0 (x∸x≡0 x)

toℕ-homo-∸ : ∀ x y → toℕ (x ∸ y) ≡ (toℕ x) ℕ.∸ (toℕ y)
toℕ-homo-∸ zero     zero     = refl
toℕ-homo-∸ zero     2[1+ y ] = refl
toℕ-homo-∸ zero     1+[2 y ] = refl
toℕ-homo-∸ 2[1+ x ] zero     = refl
toℕ-homo-∸ 2[1+ x ] 2[1+ y ] = begin
  toℕ (double (x ∸ y))          ≡⟨ toℕ-double (x ∸ y) ⟩
  2 ℕ.* toℕ (x ∸ y)             ≡⟨ cong (2 ℕ.*_) (toℕ-homo-∸ x y) ⟩
  2 ℕ.* (toℕ x ℕ.∸ toℕ y)       ≡⟨ ℕ.*-distribˡ-∸ 2 (ℕ.suc (toℕ x)) (ℕ.suc (toℕ y)) ⟩
  toℕ 2[1+ x ] ℕ.∸ toℕ 2[1+ y ] ∎
  where open ≡-Reasoning
toℕ-homo-∸ 2[1+ x ] 1+[2 y ] with x <? y
... | yes x<y  = sym (ℕ.m≤n⇒m∸n≡0 (toℕ-mono-≤ (inj₁ (even<odd x<y))))
... | no  x≮y  = begin
  ℕ.suc (2 ℕ.* toℕ (x ∸ y))                     ≡⟨ cong (ℕ.suc ∘ (2 ℕ.*_)) (toℕ-homo-∸ x y) ⟩
  ℕ.suc (2 ℕ.* (toℕ x ℕ.∸ toℕ y))               ≡⟨ cong ℕ.suc (ℕ.*-distribˡ-∸ 2 (toℕ x) (toℕ y)) ⟩
  ℕ.suc (2 ℕ.* toℕ x ℕ.∸ 2 ℕ.* toℕ y)           ≡⟨ sym (ℕ.+-∸-assoc 1 (ℕ.*-monoʳ-≤ 2 (toℕ-mono-≤ (≮⇒≥ x≮y)))) ⟩
  ℕ.suc (2 ℕ.* toℕ x) ℕ.∸ 2 ℕ.* toℕ y           ≡⟨ sym (cong (ℕ._∸ 2 ℕ.* toℕ y) (ℕ.+-suc (toℕ x) (1 ℕ.* toℕ x))) ⟩
  2 ℕ.* (ℕ.suc (toℕ x)) ℕ.∸ ℕ.suc (2 ℕ.* toℕ y) ∎
  where open ≡-Reasoning
toℕ-homo-∸ 1+[2 x ] zero     = refl
toℕ-homo-∸ 1+[2 x ] 2[1+ y ] with x ≤? y
... | yes x≤y = sym (ℕ.m≤n⇒m∸n≡0 (toℕ-mono-≤ (inj₁ (odd<even x≤y))))
... | no  _   = begin
  toℕ (pred (double (x ∸ y)))                   ≡⟨ toℕ-pred (double (x ∸ y)) ⟩
  ℕ.pred (toℕ (double (x ∸ y)))                 ≡⟨ cong ℕ.pred (toℕ-double (x ∸ y)) ⟩
  ℕ.pred (2 ℕ.* toℕ (x ∸ y))                    ≡⟨ cong (ℕ.pred ∘ (2 ℕ.*_)) (toℕ-homo-∸ x y) ⟩
  ℕ.pred (2 ℕ.* (toℕ x ℕ.∸ toℕ y))              ≡⟨ cong ℕ.pred (ℕ.*-distribˡ-∸ 2 (toℕ x) (toℕ y)) ⟩
  ℕ.pred (2 ℕ.* toℕ x ℕ.∸ 2 ℕ.* toℕ y)          ≡⟨ ℕ.pred[m∸n]≡m∸[1+n] (2 ℕ.* toℕ x) (2 ℕ.* toℕ y) ⟩
  2 ℕ.* toℕ x ℕ.∸ ℕ.suc (2 ℕ.* toℕ y)           ≡⟨ sym (cong (2 ℕ.* toℕ x ℕ.∸_) (ℕ.+-suc (toℕ y) (1 ℕ.* toℕ y))) ⟩
  ℕ.suc (2 ℕ.* toℕ x) ℕ.∸ 2 ℕ.* (ℕ.suc (toℕ y)) ∎
  where open ≡-Reasoning
toℕ-homo-∸ 1+[2 x ] 1+[2 y ] = begin
  toℕ (double (x ∸ y))        ≡⟨ toℕ-double (x ∸ y) ⟩
  2 ℕ.* toℕ (x ∸ y)           ≡⟨ cong (2 ℕ.*_) (toℕ-homo-∸ x y) ⟩
  2 ℕ.* (toℕ x ℕ.∸ toℕ y)     ≡⟨ ℕ.*-distribˡ-∸ 2 (toℕ x) (toℕ y) ⟩
  2 ℕ.* toℕ x ℕ.∸ 2 ℕ.* toℕ y ∎
  where open ≡-Reasoning

fromℕ-homo-∸ : ∀ m n → fromℕ (m ℕ.∸ n) ≡ (fromℕ m) ∸ (fromℕ n)
fromℕ-homo-∸ = homomorphic₂-inv ∸-magma ℕ.∸-magma
  (cong fromℕ) toℕ-inverseᵇ toℕ-homo-∸

------------------------------------------------------------------------
-- Properties of _∸_ and _≤_/_<_

even∸odd-for≥ : x ≥ y → 2[1+ x ] ∸ 1+[2 y ] ≡ 1+[2 (x ∸ y) ]
even∸odd-for≥ {x} {y} x≥y with x <? y
... | no _    = refl
... | yes x<y = contradiction x≥y (<⇒≱ x<y)

odd∸even-for> : x > y → 1+[2 x ] ∸ 2[1+ y ] ≡ pred (double (x ∸ y))
odd∸even-for> {x} {y} x>y with x ≤? y
... | no _    = refl
... | yes x≤y = contradiction x>y (≤⇒≯ x≤y)

x≤y⇒x∸y≡0 : x ≤ y → x ∸ y ≡ 0ᵇ
x≤y⇒x∸y≡0 {x} {y} = toℕ-injective ∘ trans (toℕ-homo-∸ x y) ∘ ℕ.m≤n⇒m∸n≡0 ∘ toℕ-mono-≤

x∸y≡0⇒x≤y : x ∸ y ≡ 0ᵇ → x ≤ y
x∸y≡0⇒x≤y {x} {y} = toℕ-cancel-≤ ∘ ℕ.m∸n≡0⇒m≤n ∘ trans (sym (toℕ-homo-∸ x y)) ∘ cong toℕ

x<y⇒y∸x>0 : x < y → y ∸ x > 0ᵇ
x<y⇒y∸x>0 {x} {y} = toℕ-cancel-< ∘ subst (ℕ._> 0) (sym (toℕ-homo-∸ y x)) ∘ ℕ.m<n⇒0<n∸m ∘ toℕ-mono-<

------------------------------------------------------------------------
-- Properties of _∸_ and _+_

[x∸y]+y≡x : x ≥ y → (x ∸ y) + y ≡ x
[x∸y]+y≡x {x} {y} x≥y = toℕ-injective (begin
  toℕ (x ∸ y + y)             ≡⟨ toℕ-homo-+ (x ∸ y) y ⟩
  toℕ (x ∸ y) ℕ.+ toℕ y       ≡⟨ cong (ℕ._+ toℕ y) (toℕ-homo-∸ x y) ⟩
  (toℕ x ℕ.∸ toℕ y) ℕ.+ toℕ y ≡⟨ ℕ.m∸n+n≡m (toℕ-mono-≤ x≥y) ⟩
  toℕ x                       ∎)
  where open ≡-Reasoning

x+y∸y≡x : ∀ x y → (x + y) ∸ y ≡ x
x+y∸y≡x x y = +-cancelʳ-≡ _ _ x ([x∸y]+y≡x (x≤y+x y x))

[x+y]∸x≡y : ∀ x y → (x + y) ∸ x ≡ y
[x+y]∸x≡y x y = trans (cong (_∸ x) (+-comm x y)) (x+y∸y≡x y x)

x+[y∸x]≡y : x ≤ y → x + (y ∸ x) ≡ y
x+[y∸x]≡y {x} {y} x≤y = begin-equality
  x + (y ∸ x)   ≡⟨ +-comm x _ ⟩
  (y ∸ x) + x   ≡⟨ [x∸y]+y≡x x≤y ⟩
  y             ∎
  where open ≤-Reasoning

∸-+-assoc : ∀ x y z → (x ∸ y) ∸ z ≡ x ∸ (y + z)
∸-+-assoc x y z = toℕ-injective $ begin
  toℕ ((x ∸ y) ∸ z)       ≡⟨ toℕ-homo-∸ (x ∸ y) z ⟩
  toℕ (x ∸ y) ℕ.∸ n       ≡⟨ cong (ℕ._∸ n) (toℕ-homo-∸ x y) ⟩
  (k ℕ.∸ m) ℕ.∸ n         ≡⟨ ℕ.∸-+-assoc k m n ⟩
  k ℕ.∸ (m ℕ.+ n)         ≡⟨ cong (k ℕ.∸_) (sym (toℕ-homo-+ y z)) ⟩
  k ℕ.∸ (toℕ (y + z))     ≡⟨ sym (toℕ-homo-∸ x (y + z)) ⟩
  toℕ (x ∸ (y + z))       ∎
  where open ≡-Reasoning;  k = toℕ x;  m = toℕ y;  n = toℕ z

+-∸-assoc : ∀ x {y z} → z ≤ y → (x + y) ∸ z ≡ x + (y ∸ z)
+-∸-assoc x {y} {z} z≤y = toℕ-injective $ begin
  toℕ ((x + y) ∸ z)     ≡⟨ toℕ-homo-∸ (x + y) z ⟩
  (toℕ (x + y)) ℕ.∸ n   ≡⟨ cong (ℕ._∸ n) (toℕ-homo-+ x y) ⟩
  (k ℕ.+ m) ℕ.∸ n       ≡⟨ ℕ.+-∸-assoc k n≤m ⟩
  k ℕ.+ (m ℕ.∸ n)       ≡⟨ cong (k ℕ.+_) (sym (toℕ-homo-∸ y z)) ⟩
  k ℕ.+ toℕ (y ∸ z)     ≡⟨ sym (toℕ-homo-+ x (y ∸ z)) ⟩
  toℕ (x + (y ∸ z))     ∎
  where
  open ≡-Reasoning;  k = toℕ x;  m = toℕ y;  n = toℕ z;  n≤m = toℕ-mono-≤ z≤y

x+y∸x+z≡y∸z : ∀ x y z → (x + y) ∸ (x + z) ≡ y ∸ z
x+y∸x+z≡y∸z x y z = begin-equality
  (x + y) ∸ (x + z)    ≡⟨ sym (∸-+-assoc (x + y) x z) ⟩
  ((x + y) ∸ x) ∸ z    ≡⟨ cong (_∸ z) ([x+y]∸x≡y x y) ⟩
  y ∸ z                ∎
  where open ≤-Reasoning

suc[x]∸suc[y] : ∀ x y → suc x ∸ suc y ≡ x ∸ y
suc[x]∸suc[y] x y = begin-equality
  suc x ∸ suc y         ≡⟨ cong₂ _∸_ (suc≗1+ x) (suc≗1+ y) ⟩
  (1ᵇ + x) ∸ (1ᵇ + y)   ≡⟨ x+y∸x+z≡y∸z 1ᵇ x y ⟩
  x ∸ y                 ∎
  where open ≤-Reasoning

∸-mono-≤ : _∸_ Preserves₂ _≤_ ⟶ _≥_ ⟶ _≤_
∸-mono-≤ {x} {y} {u} {v} x≤y v≤u = toℕ-cancel-≤ (begin
  toℕ (x ∸ u)      ≡⟨ toℕ-homo-∸ x u ⟩
  toℕ x ℕ.∸ toℕ u  ≤⟨ ℕ.∸-mono (toℕ-mono-≤ x≤y) (toℕ-mono-≤ v≤u) ⟩
  toℕ y ℕ.∸ toℕ v  ≡⟨ sym (toℕ-homo-∸ y v) ⟩
  toℕ (y ∸ v)      ∎)
  where open ℕ.≤-Reasoning

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
*-distribˡ-∸ x y z = toℕ-injective $ begin
  toℕ (x * (y ∸ z))              ≡⟨ toℕ-homo-* x (y ∸ z) ⟩
  k ℕ.* (toℕ (y ∸ z))            ≡⟨ cong (k ℕ.*_) (toℕ-homo-∸ y z) ⟩
  k ℕ.* (m ℕ.∸ n)                ≡⟨ ℕ.*-distribˡ-∸ k m n ⟩
  (k ℕ.* m) ℕ.∸ (k ℕ.* n)        ≡⟨ cong₂ ℕ._∸_ (sym (toℕ-homo-* x y)) (sym (toℕ-homo-* x z)) ⟩
  toℕ (x * y) ℕ.∸ toℕ (x * z)    ≡⟨ sym (toℕ-homo-∸ (x * y) (x * z)) ⟩
  toℕ ((x * y) ∸ (x * z))        ∎
  where open ≡-Reasoning;  k = toℕ x;  m = toℕ y;  n = toℕ z

*-distribʳ-∸ : _*_ DistributesOverʳ _∸_
*-distribʳ-∸ = comm∧distrˡ⇒distrʳ *-comm *-distribˡ-∸

*-distrib-∸ : _*_ DistributesOver _∸_
*-distrib-∸ = *-distribˡ-∸ , *-distribʳ-∸
