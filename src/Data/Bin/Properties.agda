------------------------------------------------------------------------
-- The Agda standard library
--
-- Arithmetic properties related to addition and multiplication of
-- binary represented natural numbers.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Properties where

open import Algebra
import      Algebra.FunctionProperties as FuncProp
open import Algebra.Structures
open import Data.Bin.Base
open import Data.Nat using (ℕ; s≤s)
                     renaming (suc to 1+_; pred to predₙ; _+_ to _+ₙ_;
                               _*_ to _*ₙ_; _∸_ to _∸ₙ_; _≤_ to _≤ₙ_)
            -- to distinguish these operators from their Bin versions

open import Data.Nat.Properties as ℕp using (even≢odd)
open import Data.Product    using (_,_; proj₁; proj₂; ∃)
open import Data.Sum        using (_⊎_; inj₁; inj₂)
open import Function        using (_∘_; _$_; id; const; case_of_)
open import Level           using () renaming (zero to 0ℓ)
open import Relation.Binary using (Setoid; DecSetoid; Decidable;
                                                      IsDecEquivalence)
open import Relation.Binary.PropositionalEquality as P using
     (_≡_; _≢_; _≗_; refl; sym; trans; cong; cong₂; subst; isEquivalence)
open import Relation.Nullary          using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

import Algebra.Properties.CommutativeSemigroup ℕp.+-semigroup ℕp.+-comm
                                                     as Of+ℕ-semigroup
import Algebra.Properties.CommutativeSemigroup ℕp.*-semigroup ℕp.*-comm
                                                     as Of*ℕ-semigroup
open FuncProp (_≡_ {A = Bin})
open P.≡-Reasoning
open Bin


------------------------------------------------------------------------------
-- Equality properties
------------------------------------------------------------------------------

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = P.setoid Bin

2suc≢0 :  ∀ {x} → 2suc x ≢ 0#
2suc≢0 ()

suc2*≢0 :  ∀ {x} → suc2* x ≢ 0#
suc2*≢0 ()

2suc-injective : ∀ {x y} → 2suc x ≡ 2suc y → x ≡ y
2suc-injective {0#}      {0#}      _    =  refl
2suc-injective {2suc _}  {2suc _}  refl =  refl
2suc-injective {suc2* _} {suc2* _} refl =  refl

suc2*-injective : ∀ {x y} → suc2* x ≡ suc2* y → x ≡ y
suc2*-injective {0#}      {0#}      _    =  refl
suc2*-injective {2suc _}  {2suc _}  refl =  refl
suc2*-injective {suc2* _} {suc2* _} refl =  refl


_≟_ :  Decidable (_≡_ {A = Bin})       -- Decidable equality on Bin.
0#        ≟ 0#        =  yes refl
0#        ≟ (2suc _)  =  no λ()
0#        ≟ (suc2* _) =  no λ()
(2suc _)  ≟ 0#        =  no λ()
(2suc x)  ≟ (2suc y)  with x ≟ y
... | yes eq =  yes (cong 2suc eq)
... | no ne  =  no (ne ∘ 2suc-injective)
(2suc _)  ≟ (suc2* _) =  no λ()
(suc2* _) ≟ 0#        =  no λ()
(suc2* _) ≟ (2suc _)  =  no λ()
(suc2* x) ≟ (suc2* y) with x ≟ y
... | yes eq =  yes (cong suc2* eq)
... | no ne  =  no (ne ∘ suc2*-injective)


|x|≡0⇒x≡0 :  ∀ {x} → size x ≡ 0 → x ≡ 0#
|x|≡0⇒x≡0 {0#} _ =  refl

suc≢0 :  ∀ {x} → suc x ≢ 0#
suc≢0 {0#}      ()
suc≢0 {2suc _}  ()
suc≢0 {suc2* _} ()

------------------------------------------------------------------------------
-- Constructor properties
------------------------------------------------------------------------------

x≢0⇒x+y≢0 :  ∀ {x} (y : Bin) → x ≢ 0# → x + y ≢ 0#
x≢0⇒x+y≢0 {2suc _} 0# _   =  λ()
x≢0⇒x+y≢0 {0#}     _  0≢0 =  contradiction refl 0≢0

2suc-as∘ :  2suc ≗ 2* ∘ suc
2suc-as∘ 0#       =  refl
2suc-as∘ (2suc x) =  begin
  2suc (2suc x)        ≡⟨ cong 2suc (2suc-as∘ x) ⟩
  2suc (2* (suc x))    ≡⟨⟩
  2* (suc2* (suc x))   ≡⟨⟩
  2* (suc (2suc x))    ∎

2suc-as∘ (suc2* x) =  refl



-- suc2*∘suc≗suc∘2suc :  suc2* ∘ suc ≗ suc ∘ 2suc   is by  const refl

suc2*-as∘ :  suc2* ≗ suc ∘ 2*
suc2*-as∘ 0#        = refl
suc2*-as∘ (2suc x)  = refl
suc2*-as∘ (suc2* x) = begin
  suc2* (suc2* x)     ≡⟨ cong suc2* (suc2*-as∘ x) ⟩
  suc2* (suc 2x)      ≡⟨⟩
  suc (2suc 2x)       ≡⟨ cong suc (2suc-as∘ 2x) ⟩
  suc (2* (suc 2x))   ≡⟨ cong (suc ∘ 2*) (sym (suc2*-as∘ x)) ⟩
  suc (2* (suc2* x))  ∎
  where
  2x = 2* x

pred∘suc :  pred ∘ suc ≗ id
pred∘suc 0#        =  refl
pred∘suc (2suc x)  =  sym (2suc-as∘ x)
pred∘suc (suc2* x) =  refl

suc∘pred :  (x : Bin) → x ≢ 0# → suc (pred x) ≡ x

suc∘pred 0#        0≢0 =  contradiction refl 0≢0
suc∘pred (2suc _)  _   =  refl
suc∘pred (suc2* x) _   =  begin
  suc (pred (suc2* x))   ≡⟨⟩
  suc (2* x)             ≡⟨ sym (suc2*-as∘ x) ⟩
  suc2* x                ∎


------------------------------------------------------------------------------
-- Addition properties. Chapter I.
------------------------------------------------------------------------------

+-identityˡ : LeftIdentity 0# _+_
+-identityˡ _ = refl

+-identityʳ : RightIdentity 0# _+_
+-identityʳ 0#        = refl
+-identityʳ (2suc _)  = refl
+-identityʳ (suc2* _) = refl

+-identity : Identity 0# _+_
+-identity = (+-identityˡ , +-identityʳ)

2*≢1 :  {x : Bin} → 2* x ≢ 1B
2*≢1 {0#} ()

suc≗1+ :  suc ≗ (1B +_)
suc≗1+ 0#        =  refl
suc≗1+ (2suc _)  =  refl
suc≗1+ (suc2* _) =  refl

suc-+ :  ∀ x y → (suc x) + y ≡ suc (x + y)
suc-+ 0# y = begin
  suc 0# + y     ≡⟨⟩
  1B + y         ≡⟨ sym (suc≗1+ y) ⟩
  suc y          ≡⟨⟩
  suc (0# + y)   ∎

suc-+ x 0# = begin
  suc x + 0#     ≡⟨ +-identityʳ (suc x) ⟩
  suc x          ≡⟨ cong suc (sym (+-identityʳ x)) ⟩
  suc (x + 0#)   ∎

suc-+ (2suc x) (2suc y) = begin
  (suc (2suc x)) + (2suc y)    ≡⟨⟩
  suc2* (suc x) + (2suc y)     ≡⟨⟩
  suc (2suc (suc x + y))       ≡⟨ cong (suc ∘ 2suc) (suc-+ x y) ⟩
  suc (2suc (suc (x + y)))     ≡⟨⟩
  suc ((2suc x) + (2suc y))    ∎

suc-+ (2suc x) (suc2* y) = begin
  (suc (2suc x)) + (suc2* y)     ≡⟨⟩
  (suc2* (suc x)) + (suc2* y)    ≡⟨⟩
  suc (suc2* (suc x + y))        ≡⟨ cong (suc ∘ suc2*) (suc-+ x y) ⟩
  suc (suc2* (suc (x + y)))      ≡⟨⟩
  suc (suc (2suc (x + y)))       ≡⟨⟩
  suc ((2suc x) + (suc2* y))     ∎

suc-+ (suc2* x) (2suc y)  =  refl
suc-+ (suc2* x) (suc2* y) =  refl


1+≗suc :  (1B +_) ≗ suc
1+≗suc = suc-+ 0#


------------------------------------------------------------------------------
-- Multiplication properties. Chapter I.
------------------------------------------------------------------------------

*-zeroˡ : LeftZero 0# _*_
*-zeroˡ _ = refl

*-zeroʳ : RightZero 0# _*_
*-zeroʳ 0#        = refl
*-zeroʳ (2suc _)  = refl
*-zeroʳ (suc2* _) = refl

*-zero : Zero 0# _*_
*-zero = (*-zeroˡ , *-zeroʳ )

x*y≡0⇒x≡0∨y≡0 :  ∀ x {y} → x * y ≡ 0# → x ≡ 0# ⊎ y ≡ 0#
x*y≡0⇒x≡0∨y≡0 0# {_}  _ =  inj₁ refl
x*y≡0⇒x≡0∨y≡0 _  {0#} _ =  inj₂ refl

nz*nz :  ∀ {x y} → x ≢ 0# → y ≢ 0# → x * y ≢ 0#
nz*nz {x} {_} x≢0 y≢0 xy≡0  with x*y≡0⇒x≡0∨y≡0 x xy≡0
... | inj₁ x≡0 =  x≢0 x≡0
... | inj₂ y≡0 =  y≢0 y≡0


------------------------------------------------------------------------------
-- Properties of toℕ and fromℕ. Chapter I.
------------------------------------------------------------------------------

toℕ∘2* :  ∀ x → toℕ (2* x) ≡ 2 *ₙ (toℕ x)
toℕ∘2* 0#       = refl
toℕ∘2* (2suc x) = begin
  toℕ (2* (2suc x))         ≡⟨⟩
  2 *ₙ (1+ (1+ (2 *ₙ m)))   ≡⟨⟩
  2 *ₙ (2 +ₙ 2m)            ≡⟨ cong (2 *ₙ_) (sym (ℕp.*-distribˡ-+ 2 1 m)) ⟩
  2 *ₙ (2 *ₙ (1+ m))        ≡⟨⟩
  2 *ₙ (toℕ (2suc x))       ∎
  where
  m = toℕ x;  2m = 2 *ₙ m;  open P.≡-Reasoning

toℕ∘2* (suc2* x) =  cong ((2 *ₙ_) ∘ 1+_) (toℕ∘2* x)


toℕ∘suc :  ∀ x → toℕ (suc x) ≡ 1+ (toℕ x)
toℕ∘suc 0#        =  refl
toℕ∘suc (2suc x)  =  cong (1+_ ∘ (2 *ₙ_)) (toℕ∘suc x)
toℕ∘suc (suc2* x) =  ℕp.*-distribˡ-+ 2 1 (toℕ x)

toℕ∘pred :  ∀ x → toℕ (pred x) ≡ predₙ (toℕ x)
toℕ∘pred 0#        =  refl
toℕ∘pred (2suc x)  =  cong predₙ $ sym $ ℕp.*-distribˡ-+ 2 1 (toℕ x)
toℕ∘pred (suc2* x) =  toℕ∘2* x


x≡0⇒toℕ-x≡0 :  ∀ {x} → x ≡ 0# → toℕ x ≡ 0
x≡0⇒toℕ-x≡0 {0#} _ = refl

toℕ-x≡0⇒x≡0 :  ∀ {x} → toℕ x ≡ 0 → x ≡ 0#
toℕ-x≡0⇒x≡0 {0#} _ = refl

toℕ+homo :  ∀ x y → toℕ (x + y) ≡ toℕ x +ₙ toℕ y
toℕ+homo 0# _  =  refl
toℕ+homo x  0# =  begin
  toℕ (x + 0#)      ≡⟨ cong toℕ (+-identityʳ x) ⟩
  toℕ x             ≡⟨ sym (ℕp.+-comm (toℕ x) 0) ⟩
  toℕ x +ₙ 0        ≡⟨⟩
  toℕ x +ₙ toℕ 0#   ∎

toℕ+homo (2suc x) (2suc y) = begin
  toℕ ((2suc x) + (2suc y))        ≡⟨⟩
  toℕ (2suc (suc (x + y)))         ≡⟨⟩
  2 *ₙ (1+ (toℕ (suc (x + y))))    ≡⟨ cong ((2 *ₙ_) ∘ 1+_) (toℕ∘suc (x + y)) ⟩
  2 *ₙ (1+ (1+ toℕ (x + y)))       ≡⟨ cong ((2 *ₙ_) ∘ 1+_ ∘ 1+_)
                                                      (toℕ+homo x y) ⟩
  2 *ₙ ((1+ (1+ (m +ₙ n))))        ≡⟨ cong ((2 *ₙ_) ∘ 1+_)
                                                    (sym (ℕp.+-assoc 1 m n)) ⟩
  2 *ₙ ((1+ ((1+ m) +ₙ n)))        ≡⟨ cong ((2 *ₙ_) ∘ 1+_ ∘ (_+ₙ n))
                                                          (ℕp.+-comm 1 m) ⟩
  2 *ₙ ((1+ ((m +ₙ 1) +ₙ n)))      ≡⟨ cong ((2 *ₙ_) ∘ 1+_)
                                           (ℕp.+-assoc m 1 n) ⟩
  2 *ₙ ((1+ ((m +ₙ (1+ n)))))      ≡⟨ cong (2 *ₙ_)
                                           (sym (ℕp.+-assoc 1 m (1+ n)))
                                    ⟩
  2 *ₙ ((1+ m) +ₙ (1+ n))          ≡⟨ ℕp.*-distribˡ-+ 2 (1+ m) (1+ n) ⟩
  (2 *ₙ (1+ m)) +ₙ (2 *ₙ (1+ n))   ≡⟨⟩
  toℕ (2suc x) +ₙ toℕ (2suc y)   ∎
  where
  m = toℕ x;  n = toℕ y

toℕ+homo (2suc x) (suc2* y) = begin
  toℕ ((2suc x) + (suc2* y))      ≡⟨⟩
  toℕ (suc (2suc (x + y)))        ≡⟨ toℕ∘suc (2suc (x + y)) ⟩
  1+ (toℕ (2suc (x + y)))         ≡⟨⟩
  1+ (2 *ₙ (1+ (toℕ (x + y))))    ≡⟨ cong (1+_ ∘ (2 *ₙ_) ∘ 1+_) (toℕ+homo x y)
                                   ⟩
  1+ (2 *ₙ (1+ (m +ₙ n)))         ≡⟨ cong (1+_ ∘ (2 *ₙ_))
                                                 (sym (ℕp.+-assoc 1 m n)) ⟩
  1+ (2 *ₙ (1+m +ₙ n))            ≡⟨ cong 1+_ (ℕp.*-distribˡ-+ 2 1+m n) ⟩
  1+ ((2 *ₙ 1+m) +ₙ 2 *ₙ n)       ≡⟨ Of+ℕ-semigroup.x∙yz≈y∙xz 1 _ (2 *ₙ n) ⟩
  (2 *ₙ 1+m) +ₙ (1+ (2 *ₙ n))     ≡⟨⟩
  toℕ (2suc x) +ₙ toℕ (suc2* y)   ∎
  where
  m = toℕ x;  n = toℕ y;  1+m = 1+ m

toℕ+homo (suc2* x) (2suc y) = begin
  toℕ ((suc2* x) + (2suc y))      ≡⟨⟩
  toℕ (suc (2suc (x + y)))        ≡⟨ toℕ∘suc (2suc (x + y)) ⟩
  1+ (toℕ (2suc (x + y)))         ≡⟨⟩
  1+ (2 *ₙ (1+ (toℕ (x + y))))    ≡⟨ cong (1+_ ∘ (2 *ₙ_) ∘ 1+_)
                                                         (toℕ+homo x y) ⟩
  1+ (2 *ₙ (1+ (m +ₙ n)))         ≡⟨ cong (1+_ ∘ (2 *ₙ_))
                                          (Of+ℕ-semigroup.x∙yz≈y∙xz 1 m n)
                                   ⟩
  1+ (2 *ₙ (m +ₙ 1+n))            ≡⟨ cong 1+_ (ℕp.*-distribˡ-+ 2 m 1+n) ⟩
  1+ (2 *ₙ m +ₙ 2 *ₙ 1+n)         ≡⟨ sym (ℕp.+-assoc 1 (2 *ₙ m) (2 *ₙ 1+n)) ⟩
  (1+ (2 *ₙ m)) +ₙ (2 *ₙ (1+ n))  ≡⟨⟩
  toℕ (suc2* x) +ₙ toℕ (2suc y)   ∎
  where
  m = toℕ x;  n = toℕ y;  1+n = 1+ n

toℕ+homo (suc2* x) (suc2* y) = begin
  toℕ ((suc2* x) + (suc2* y))       ≡⟨⟩
  toℕ (suc (suc2* (x + y)))         ≡⟨ toℕ∘suc (suc2* (x + y)) ⟩
  1+ (toℕ (suc2* (x + y)))          ≡⟨⟩
  1+ (1+ (2 *ₙ (toℕ (x + y))))      ≡⟨ cong (1+_ ∘ 1+_ ∘ (2 *ₙ_))
                                                       (toℕ+homo x y) ⟩
  1+ (1+ (2 *ₙ (m +ₙ n)))           ≡⟨ cong (1+_ ∘ 1+_) (ℕp.*-distribˡ-+ 2 m n)
                                     ⟩
  1+ (1+ (2 *ₙ m +ₙ 2 *ₙ n))        ≡⟨ cong 1+_
                                            (sym (ℕp.+-assoc 1 (2 *ₙ m) _)) ⟩
  1+ ((1+ (2 *ₙ m) +ₙ (2 *ₙ n)))    ≡⟨ (Of+ℕ-semigroup.x∙yz≈y∙xz
                                                         1 (1+ (2 *ₙ m)) _) ⟩
  (1+ (2 *ₙ m)) +ₙ (1+ (2 *ₙ n))    ≡⟨⟩
  toℕ (suc2* x) +ₙ toℕ (suc2* y)    ∎
  where
  m = toℕ x;  n = toℕ y


ext-fromℕ :  (n : ℕ) → ∃ (\x → toℕ x ≡ n)    -- Mind:  it costs O(n)
ext-fromℕ 0       =  (0# , refl)
ext-fromℕ (1+ n)  with ext-fromℕ n
...
    | (x , toℕ-x≡n) = (suc x , toℕ-suc-x≡1+n)
  where
  toℕ-suc-x≡1+n = begin
    toℕ (suc x)   ≡⟨ toℕ∘suc x ⟩
    1+ (toℕ x)    ≡⟨ cong 1+_ toℕ-x≡n ⟩
    1+ n          ∎

fromℕ : ℕ → Bin
fromℕ = proj₁ ∘ ext-fromℕ

fromℕ+homo :  (m n : ℕ) → fromℕ (m +ₙ n) ≡ fromℕ m + fromℕ n
fromℕ+homo 0      _ = refl
fromℕ+homo (1+ m) n = begin
  fromℕ ((1+ m) +ₙ n)         ≡⟨⟩
  suc (fromℕ (m +ₙ n))        ≡⟨ cong suc (fromℕ+homo m n) ⟩
  suc (a + b)                 ≡⟨ sym (suc-+ a b) ⟩
  (suc a) + b                 ≡⟨⟩
  (fromℕ (1+ m)) + (fromℕ n)  ∎
  where
  a = fromℕ m;  b = fromℕ n

toℕ∘fromℕ :  toℕ ∘ fromℕ ≗ id
toℕ∘fromℕ 0      = refl
toℕ∘fromℕ (1+ n) = begin
  toℕ (fromℕ (1+ n))   ≡⟨⟩
  toℕ (suc (fromℕ n))  ≡⟨ toℕ∘suc (fromℕ n) ⟩
  1+ (toℕ (fromℕ n))   ≡⟨ cong 1+_ (toℕ∘fromℕ n) ⟩
  1+ n                 ∎

toℕ-injective :  ∀ {x y} → toℕ x ≡ toℕ y → x ≡ y
toℕ-injective {0#}     {0#}     _               =  refl
toℕ-injective {2suc x} {2suc y} 2[1+xN]≡2[1+yN] =  cong 2suc x≡y
  where
  xN        = toℕ x
  yN        = toℕ y
  1+xN≡1+yN = ℕp.*-cancelˡ-≡ {1+ xN} {1+ yN} 1 2[1+xN]≡2[1+yN]
  xN≡yN     = cong predₙ 1+xN≡1+yN
  x≡y       = toℕ-injective xN≡yN

toℕ-injective {2suc x} {suc2* y} 2[1+xN]≡1+2yN =
                               contradiction 2[1+xN]≡1+2yN (even≢odd 1+xN yN)
  where
  1+xN = 1+ (toℕ x);  yN = toℕ y

toℕ-injective {suc2* x} {2suc y} 1+2xN≡2[1+yN] =
                        contradiction (sym 1+2xN≡2[1+yN]) (even≢odd 1+yN xN)
  where
  xN = toℕ x;  1+yN = 1+ (toℕ y)

toℕ-injective {suc2* x} {suc2* y} 1+2xN≡1+2yN =  cong suc2* x≡y
  where
  xN = toℕ x;  yN = toℕ y;  2xN≡2yN = cong predₙ 1+2xN≡1+2yN

  xN≡yN = ℕp.*-cancelˡ-≡ {xN} {yN} 1 2xN≡2yN;   x≡y = toℕ-injective xN≡yN


toℕ-surjective :  (y : ℕ) → ∃ (\x → toℕ x ≡ y)
toℕ-surjective 0       =  (0# , refl)
toℕ-surjective (1+ n)  with toℕ-surjective n
...
    | (a , toℕ-a≡n) = (suc a , toℕ-suc-a≡1+n)
  where
  toℕ-suc-a≡1+n = begin
    toℕ (suc a)   ≡⟨ toℕ∘suc a ⟩
    1+ (toℕ a)    ≡⟨ cong 1+_ toℕ-a≡n ⟩
    1+ n          ∎


fromℕ∘toℕ :  fromℕ ∘ toℕ ≗ id
fromℕ∘toℕ a =  toℕ-injective toℕ-b≡toℕ-a
  where
  toℕ-b≡toℕ-a = proj₂ (ext-fromℕ (toℕ a))

------------------------------------------------------------------------------
-- Summary:
-- 1)  toℕ : Bin → ℕ  is an isomorphism by _+_,
-- 2)  fromℕ            is a homomorphisms by _+_ coinverse with toℕ.
------------------------------------------------------------------------------

fromℕ∘pred :  (n : ℕ) → fromℕ (predₙ n) ≡ pred (fromℕ n)
fromℕ∘pred n =
  let (x , toℕ-x≡n) = ext-fromℕ n
  in
  begin
    fromℕ (predₙ n)         ≡⟨ cong (fromℕ ∘ predₙ) (sym (toℕ∘fromℕ n)) ⟩
    fromℕ (predₙ (toℕ x))   ≡⟨ cong fromℕ (sym (toℕ∘pred x)) ⟩
    fromℕ (toℕ (pred x))    ≡⟨ fromℕ∘toℕ (pred x) ⟩
    pred x                  ≡⟨ refl ⟩
    pred (fromℕ n)
  ∎


------------------------------------------------------------------------------
-- Addition properties. Chapter II.
-- Commutativity and associativity for _+_ are proved by using the isomorphism
-- to ℕ.
------------------------------------------------------------------------------

+-comm :  Commutative _+_
+-comm a b = begin
  a + b                    ≡⟨ sym (fromℕ∘toℕ (a + b)) ⟩
  fromℕ (toℕ (a + b))      ≡⟨ cong fromℕ (toℕ+homo a b) ⟩
  fromℕ (toℕ a +ₙ toℕ b)   ≡⟨ cong fromℕ (ℕp.+-comm (toℕ a) (toℕ b)) ⟩
  fromℕ (toℕ b +ₙ toℕ a)   ≡⟨ cong fromℕ (sym (toℕ+homo b a)) ⟩
  fromℕ (toℕ (b + a))      ≡⟨ fromℕ∘toℕ (b + a) ⟩
  b + a                    ∎

+-assoc :  Associative _+_
+-assoc a b c = begin
  (a + b) + c                  ≡⟨ sym (fromℕ∘toℕ ((a + b) + c)) ⟩
  fromℕ (toℕ ((a + b) + c))    ≡⟨ cong fromℕ (toℕ+homo (a + b) c) ⟩
  fromℕ (toℕ (a + b) +ₙ cN)    ≡⟨ cong (fromℕ ∘ (_+ₙ cN)) (toℕ+homo a b) ⟩
  fromℕ ((aN +ₙ bN) +ₙ cN)     ≡⟨ cong fromℕ (ℕp.+-assoc aN bN cN) ⟩
  fromℕ (aN +ₙ (bN +ₙ cN))     ≡⟨ cong (fromℕ ∘ (aN +ₙ_))
                                                (sym (toℕ+homo b c)) ⟩
  fromℕ (aN +ₙ toℕ (b + c))    ≡⟨ cong fromℕ (sym (toℕ+homo a (b + c))) ⟩
  fromℕ (toℕ (a + (b + c)))    ≡⟨ fromℕ∘toℕ (a + (b + c)) ⟩
  (a + (b + c))                ∎
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c


+-cancelˡ-≡ : LeftCancellative _+_       -- the proof is via toℕ
+-cancelˡ-≡ x {y} {z} x+y≡x+z = begin
  y         ≡⟨ sym (fromℕ∘toℕ y) ⟩
  fromℕ m   ≡⟨ cong fromℕ m≡n ⟩
  fromℕ n   ≡⟨ fromℕ∘toℕ z ⟩
  z         ∎
  where
  k = toℕ x;  m = toℕ y;  n = toℕ z

  eq = begin
    k +ₙ m         ≡⟨ sym (toℕ+homo x y) ⟩
    toℕ (x + y)    ≡⟨ cong toℕ x+y≡x+z ⟩
    toℕ (x + z)    ≡⟨ toℕ+homo x z ⟩
    k +ₙ n         ∎

  m≡n = begin
    m                ≡⟨ sym (ℕp.m+n∸n≡m m k)⟩
    (m +ₙ k) ∸ₙ k    ≡⟨ cong (_∸ₙ k) (ℕp.+-comm m k) ⟩
    (k +ₙ m) ∸ₙ k    ≡⟨ cong (_∸ₙ k) eq ⟩
    (k +ₙ n) ∸ₙ k    ≡⟨ cong (_∸ₙ k) (ℕp.+-comm k n) ⟩
    (n +ₙ k) ∸ₙ k    ≡⟨ ℕp.m+n∸n≡m n k ⟩
    n                ∎

+-cancelʳ-≡ : RightCancellative _+_
+-cancelʳ-≡ {x} y z y+x≡z+x =  +-cancelˡ-≡ x {y} {z} x+y≡x+z
  where
  x+y≡x+z = begin
    x + y   ≡⟨ +-comm x y ⟩
    y + x   ≡⟨ y+x≡z+x ⟩
    z + x   ≡⟨ +-comm z x ⟩
    x + z   ∎

decEquivalence :  IsDecEquivalence (_≡_ {A = Bin})
decEquivalence =  record{ isEquivalence = isEquivalence;  _≟_ = _≟_ }

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = record
  { Carrier          = Bin
  ; _≈_              = _≡_
  ; isDecEquivalence = decEquivalence
  }

+-isMagma :  IsMagma _≡_ _+_
+-isMagma =  record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

+-magma :  Magma 0ℓ 0ℓ
+-magma =  record{ isMagma = +-isMagma }

+-isSemigroup : IsSemigroup _≡_ _+_
+-isSemigroup = record{ isMagma = +-isMagma;  assoc = +-assoc }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record{ isSemigroup = +-isSemigroup }

+-0-isMonoid : IsMonoid _≡_ _+_ 0#
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { ε        = 0#
  ; isMonoid = +-0-isMonoid
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _≡_ _+_ 0#
+-0-isCommutativeMonoid = record
  { isSemigroup = +-isSemigroup
  ; identityˡ   = +-identityˡ
  ; comm        = +-comm
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }



------------------------------------------------------------------------------
-- Properties of multiplication, toℕ, fromℕ. Chapter II.
------------------------------------------------------------------------------

private  2*ₙ2*ₙ =  (2 *ₙ_) ∘ (2 *ₙ_)


toℕ*homo :  ∀ x y → toℕ (x * y) ≡ toℕ x *ₙ toℕ y
toℕ*homo x y =  aux x y (size x +ₙ size y) ℕp.≤-refl
  where
  aux :  (x y : Bin) → (cnt : ℕ) → (size x +ₙ size y ≤ₙ cnt) →
         toℕ (x * y) ≡ toℕ x *ₙ toℕ y

  aux 0# _  _ _ = refl
  aux x  0# _ _ = begin
    toℕ (x * 0#)      ≡⟨ cong toℕ (*-zeroʳ x) ⟩
    0                 ≡⟨ sym (ℕp.*-zeroʳ (toℕ x)) ⟩
    toℕ x *ₙ toℕ 0#   ∎

  ---------------------
  aux (2suc x) (2suc y) (1+ cnt) (s≤s |x|+1+|y|≤cnt) = begin
    toℕ (2suc x * 2suc y)               ≡⟨⟩
    toℕ (2* (2suc (x + (y + xy))))      ≡⟨ toℕ∘2* (2suc (x + (y + xy))) ⟩
    2 *ₙ (toℕ (2suc (x + (y + xy))))    ≡⟨⟩
    2*ₙ2*ₙ (1+ (toℕ (x + (y + xy))))    ≡⟨ cong (2*ₙ2*ₙ ∘ 1+_)
                                                    (toℕ+homo x (y + xy)) ⟩
    2*ₙ2*ₙ (1+ (m +ₙ (toℕ (y + xy))))   ≡⟨ cong (2*ₙ2*ₙ ∘ 1+_ ∘ (m +ₙ_))
                                                            (toℕ+homo y xy) ⟩
    2*ₙ2*ₙ (1+ (m +ₙ (n +ₙ toℕ xy)))
                                   ≡⟨ cong (2*ₙ2*ₙ ∘ 1+_ ∘ (m +ₙ_) ∘ (n +ₙ_))
                                           (aux x y cnt |x|+|y|≤cnt) ⟩
    2*ₙ2*ₙ (1+ (m +ₙ (n +ₙ mn)))   ≡⟨ cong 2*ₙ2*ₙ (sym eq) ⟩
    2 *ₙ (2 *ₙ (1+m *ₙ 1+n))       ≡⟨ cong (2 *ₙ_) (Of*ℕ-semigroup.x∙yz≈y∙xz
                                                                 2 1+m 1+n) ⟩
    2 *ₙ (1+m *ₙ (2 *ₙ 1+n))       ≡⟨ sym (ℕp.*-assoc 2 1+m (2 *ₙ 1+n)) ⟩
    (2 *ₙ 1+m) *ₙ (2 *ₙ 1+n)       ≡⟨⟩
    toℕ (2suc x) *ₙ toℕ (2suc y)   ∎
    where
    m   = toℕ x;   n  = toℕ y;   1+m = 1+ m
    1+n = 1+ n;     mn = m *ₙ n;   xy = x * y
    eq  = begin
      (1+m *ₙ (1+ n))           ≡⟨ ℕp.*-distribˡ-+ 1+m 1 n ⟩
      (1+m *ₙ 1 +ₙ 1+m *ₙ n)    ≡⟨ cong (_+ₙ (1+m *ₙ n)) (ℕp.*-identityʳ 1+m)
                                 ⟩
      1+ (m +ₙ 1+m *ₙ n)        ≡⟨ cong (1+_ ∘ (m +ₙ_))
                                                    (ℕp.*-distribʳ-+ n 1 m) ⟩
      1+ (m +ₙ (1 *ₙ n +ₙ mn))  ≡⟨ cong (1+_ ∘ (m +ₙ_) ∘ (_+ₙ mn))
                                                       (ℕp.*-identityˡ n) ⟩
      1+ (m +ₙ (n +ₙ mn))       ∎

    |x|+|y|≤cnt = ℕp.≤-trans (ℕp.+-monoʳ-≤ (size x) (ℕp.n≤1+n (size y)))
                              |x|+1+|y|≤cnt


  aux (2suc x) (suc2* y) (1+ cnt) (s≤s |x|+1+|y|≤cnt) = begin
    toℕ ((2suc x) * (suc2* y))           ≡⟨⟩
    toℕ (2suc (x + y * (2suc x)))        ≡⟨⟩
    2 *ₙ (1+ (toℕ (x + y * (2suc x))))   ≡⟨ cong ((2 *ₙ_) ∘ 1+_)
                                                             (toℕ+homo x _) ⟩
    2 *ₙ (1+ (m +ₙ (toℕ (y * (2suc x)))))  ≡⟨ cong ((2 *ₙ_) ∘ 1+_ ∘ (m +ₙ_))
                                                (aux y _ cnt |y|+1+|x|≤cnt) ⟩
    2 *ₙ (1+m +ₙ (n *ₙ (toℕ (2suc x))))  ≡⟨⟩
    2 *ₙ (1+m +ₙ (n *ₙ 2[1+m]))          ≡⟨ ℕp.*-distribˡ-+ 2 1+m _ ⟩
    2[1+m] +ₙ (2 *ₙ (n *ₙ 2[1+m]))       ≡⟨ cong (2[1+m] +ₙ_) $
                                            sym (ℕp.*-assoc 2 n _) ⟩
    2[1+m] +ₙ (2 *ₙ n) *ₙ 2[1+m]         ≡⟨ cong (_+ₙ ((2 *ₙ n) *ₙ 2[1+m]))
                                              (sym (ℕp.*-identityˡ 2[1+m])) ⟩
    1 *ₙ 2[1+m] +ₙ 2n *ₙ 2[1+m]          ≡⟨ sym (ℕp.*-distribʳ-+ 2[1+m]
                                                                   1 2n) ⟩
    (1+ 2n) *ₙ 2[1+m]                    ≡⟨ ℕp.*-comm (1+ 2n) 2[1+m] ⟩
    2[1+m] *ₙ (1+ 2n)                    ≡⟨⟩
    toℕ (2suc x) *ₙ toℕ (suc2* y)      ∎
    where
    m      = toℕ x;       n  = toℕ y;   1+m = 1+ m
    2[1+m] = 2 *ₙ (1+ m);  2n = 2 *ₙ n

    eq : size x +ₙ (1+ (size y)) ≡ size y +ₙ (1+ (size x))
    eq = Of+ℕ-semigroup.x∙yz≈z∙yx (size x) 1 _

    |y|+1+|x|≤cnt =  subst (_≤ₙ cnt) eq |x|+1+|y|≤cnt

      ---------
  aux (suc2* x) (2suc y) (1+ cnt) (s≤s |x|+1+|y|≤cnt) = begin
    toℕ ((suc2* x) * (2suc y))            ≡⟨⟩
    toℕ (2suc (y + x * (2suc y)))         ≡⟨⟩
    2 *ₙ (1+ (toℕ (y + x * (2suc y))))    ≡⟨ cong ((2 *ₙ_) ∘ 1+_)
                                                 (toℕ+homo y (x * (2suc y))) ⟩
    2 *ₙ (1+ (n +ₙ (toℕ (x * (2suc y)))))
                                        ≡⟨ cong ((2 *ₙ_) ∘ 1+_ ∘ (n +ₙ_))
                                           (aux x (2suc y) cnt |x|+1+|y|≤cnt)
                                         ⟩
    2 *ₙ (1+n +ₙ (m *ₙ toℕ (2suc y)))  ≡⟨⟩
    2 *ₙ (1+n +ₙ (m *ₙ 2[1+n]))        ≡⟨ ℕp.*-distribˡ-+ 2 1+n _ ⟩
    2[1+n] +ₙ (2 *ₙ (m *ₙ 2[1+n]))     ≡⟨ cong (2[1+n] +ₙ_)
                                               (sym (ℕp.*-assoc 2 m _)) ⟩
    2[1+n] +ₙ 2m *ₙ 2[1+n]             ≡⟨ cong (_+ₙ (2m *ₙ 2[1+n]))
                                               (sym (ℕp.*-identityˡ 2[1+n])) ⟩
    1 *ₙ 2[1+n] +ₙ 2m *ₙ 2[1+n]        ≡⟨ sym (ℕp.*-distribʳ-+ 2[1+n] 1 2m) ⟩
    (1+ 2m) *ₙ 2[1+n]                  ≡⟨⟩
    toℕ (suc2* x) *ₙ toℕ (2suc y)    ∎
    where
    m  = toℕ x;   n      = toℕ y;      1+n = 1+ n
    2m = 2 *ₙ m;   2[1+n] = 2 *ₙ (1+ n)


  aux (suc2* x) (suc2* y) (1+ cnt) (s≤s |x|+1+|y|≤cnt) = begin
    toℕ ((suc2* x) * (suc2* y))          ≡⟨⟩
    toℕ (suc2* (x + y * [1+2x]))         ≡⟨⟩
    1+ (2 *ₙ (toℕ (x + y * [1+2x])))     ≡⟨ cong (1+_ ∘ (2 *ₙ_))
                                                 (toℕ+homo x (y * [1+2x])) ⟩
    1+ (2 *ₙ (m +ₙ (toℕ (y * [1+2x]))))  ≡⟨ cong (1+_ ∘ (2 *ₙ_) ∘ (m +ₙ_))
                                            (aux y [1+2x] cnt |y|+1+|x|≤cnt)
                                           ⟩
    1+ (2 *ₙ (m +ₙ (n *ₙ [1+2x]')))    ≡⟨ cong 1+_ $
                                         ℕp.*-distribˡ-+ 2 m (n *ₙ [1+2x]')
                                        ⟩
    1+ (2m +ₙ (2 *ₙ (n *ₙ [1+2x]')))   ≡⟨ cong (1+_ ∘ (2m +ₙ_))
                                              (sym (ℕp.*-assoc 2 n _)) ⟩
    (1+ 2m) +ₙ 2n *ₙ [1+2x]'           ≡⟨⟩
    [1+2x]' +ₙ 2n *ₙ [1+2x]'           ≡⟨ cong (_+ₙ (2n *ₙ [1+2x]')) $
                                         sym (ℕp.*-identityˡ [1+2x]')
                                        ⟩
    1 *ₙ [1+2x]' +ₙ 2n *ₙ [1+2x]'      ≡⟨ sym (ℕp.*-distribʳ-+ [1+2x]' 1 2n) ⟩
    (1+ 2n) *ₙ [1+2x]'                 ≡⟨ ℕp.*-comm (1+ 2n) [1+2x]' ⟩
    toℕ (suc2* x) *ₙ toℕ (suc2* y)     ∎
    where
    m      = toℕ x;    n       = toℕ y;       2m = 2 *ₙ m;    2n = 2 *ₙ n
    [1+2x] = suc2* x;   [1+2x]' = toℕ [1+2x]

    eq : size x +ₙ (1+ (size y)) ≡ size y +ₙ (1+ (size x))
    eq = Of+ℕ-semigroup.x∙yz≈z∙yx (size x) 1 _

    |y|+1+|x|≤cnt = subst (_≤ₙ cnt) eq |x|+1+|y|≤cnt


fromℕ*homo :  ∀ m n → fromℕ (m *ₙ n) ≡ fromℕ m * fromℕ n
fromℕ*homo m n = begin
  fromℕ (m *ₙ n)           ≡⟨ cong fromℕ (cong₂ _*ₙ_ m≡aN n≡bN) ⟩
  fromℕ (toℕ a *ₙ toℕ b)   ≡⟨ cong fromℕ (sym (toℕ*homo a b)) ⟩
  fromℕ (toℕ (a * b))      ≡⟨ fromℕ∘toℕ (a * b) ⟩
  a * b                    ∎
  where
  a    = fromℕ m;             b    = fromℕ n
  m≡aN = sym (toℕ∘fromℕ m);   n≡bN = sym (toℕ∘fromℕ n)

2*≗2B* :  2* ≗ (2B *_)
2*≗2B* x =  toℕ-injective $ begin
  toℕ (2* x)     ≡⟨ toℕ∘2* x ⟩
  2 *ₙ (toℕ x)   ≡⟨ sym (toℕ*homo 2B x) ⟩
  toℕ (2B * x)   ∎

2x≡0⇒x≡0 :  ∀ {x} → 2* x ≡ 0# → x ≡ 0#
2x≡0⇒x≡0 {x} 2x≡0 =  x≡0
  where
  2B*x≡0 =  trans (sym (2*≗2B* x)) 2x≡0

  x≡0 :  x ≡ 0#
  x≡0 with  x*y≡0⇒x≡0∨y≡0 2B 2B*x≡0
  ... | inj₁ 2≡0 =  contradiction 2≡0 2suc≢0
  ... | inj₂ eq  =  eq

x≢0⇒2x≢0 :  ∀ {x} → x ≢ 0# → 2* x ≢ 0#
x≢0⇒2x≢0 x≢0 =  x≢0 ∘ 2x≡0⇒x≡0

------------------------------------------------------------------------------
-- Commutativity and associativity for _*_, and distributivity of _*_ over +,
-- are proved by using the isomorphisms to ℕ implemented and proved earlier.
------------------------------------------------------------------------------

*-comm : Commutative _*_
*-comm a b = begin
  a * b                    ≡⟨ sym (fromℕ∘toℕ (a * b)) ⟩
  fromℕ (toℕ (a * b))      ≡⟨ cong fromℕ (toℕ*homo a b) ⟩
  fromℕ (toℕ a *ₙ toℕ b)   ≡⟨ cong fromℕ (ℕp.*-comm (toℕ a) (toℕ b)) ⟩
  fromℕ (toℕ b *ₙ toℕ a)   ≡⟨ cong fromℕ (sym (toℕ*homo b a)) ⟩
  fromℕ (toℕ (b * a))      ≡⟨ fromℕ∘toℕ (b * a) ⟩
  b * a                    ∎

*-assoc :  Associative _*_
*-assoc a b c = begin
  (a * b) * c                 ≡⟨ sym (fromℕ∘toℕ ((a * b) * c)) ⟩
  fromℕ (toℕ ((a * b) * c))   ≡⟨ cong fromℕ (toℕ*homo (a * b) c) ⟩
  fromℕ (toℕ (a * b) *ₙ cN)   ≡⟨ cong (fromℕ ∘ (_*ₙ cN)) (toℕ*homo a b) ⟩
  fromℕ ((aN *ₙ bN) *ₙ cN)    ≡⟨ cong fromℕ (ℕp.*-assoc aN bN cN) ⟩
  fromℕ (aN *ₙ (bN *ₙ cN))    ≡⟨ cong (fromℕ ∘ (aN *ₙ_))
                                                  (sym (toℕ*homo b c)) ⟩
  fromℕ (aN *ₙ toℕ (b * c))   ≡⟨ cong fromℕ (sym (toℕ*homo a (b * c))) ⟩
  fromℕ (toℕ (a * (b * c)))   ≡⟨ fromℕ∘toℕ (a * (b * c)) ⟩
  (a * (b * c))               ∎
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c

2*-*-assoc :  ∀ x y → (2* x) * y ≡ 2* (x * y)
2*-*-assoc x y = begin
  (2* x) * y     ≡⟨ cong (_* y) (2*≗2B* x) ⟩
  (2B * x) * y   ≡⟨ *-assoc 2B x y ⟩
  2B * (x * y)   ≡⟨ sym (2*≗2B* (x * y)) ⟩
  2* (x * y)     ∎


*-distribˡ-+ :  _DistributesOverˡ_ _*_ _+_
*-distribˡ-+ a b c = begin
  a * (b + c)                          ≡⟨ sym (fromℕ∘toℕ (a * (b + c))) ⟩
  fromℕ (toℕ (a * (b + c)))            ≡⟨ cong fromℕ (toℕ*homo a (b + c)) ⟩
  fromℕ (k *ₙ (toℕ (b + c)))           ≡⟨ cong (fromℕ ∘ (k *ₙ_))
                                                         (toℕ+homo b c) ⟩
  fromℕ (k *ₙ (m +ₙ n))                ≡⟨ cong fromℕ (ℕp.*-distribˡ-+ k m n) ⟩
  fromℕ (k *ₙ m +ₙ k *ₙ n)             ≡⟨ cong fromℕ $
                                          cong₂ _+ₙ_ (sym (toℕ*homo a b))
                                                     (sym (toℕ*homo a c))
                                        ⟩
  fromℕ (toℕ (a * b) +ₙ toℕ (a * c))   ≡⟨ cong fromℕ $
                                            sym (toℕ+homo (a * b) (a * c))
                                        ⟩
  fromℕ (toℕ (a * b + a * c))          ≡⟨ fromℕ∘toℕ (a * b + a * c) ⟩
  a * b + a * c                        ∎
  where
  k = toℕ a;   m = toℕ b;   n = toℕ c


*-distribʳ-+ :  _DistributesOverʳ_ _*_ _+_
*-distribʳ-+ a b c = begin
  (b + c) * a      ≡⟨ *-comm (b + c) a ⟩
  a * (b + c)      ≡⟨ *-distribˡ-+ a b c ⟩
  a * b + a * c    ≡⟨ cong₂ _+_ (*-comm a b) (*-comm a c) ⟩
  b * a + c * a    ∎

*-distrib-+ :  _DistributesOver_ _*_ _+_
*-distrib-+ =  (*-distribˡ-+ , *-distribʳ-+)

2*-distrib : ∀ x y → 2* (x + y) ≡ 2* x + 2* y
2*-distrib x y = begin
  2* (x + y)            ≡⟨ 2*≗2B* (x + y) ⟩
  2B * (x + y)          ≡⟨ *-distribˡ-+ 2B x y ⟩
  (2B * x) + (2B * y)   ≡⟨ cong₂ _+_ eq eq' ⟩
  2* x + 2* y           ∎
  where
  eq = sym (2*≗2B* x);   eq' = sym (2*≗2B* y)


*-identityˡ : LeftIdentity 1B _*_
*-identityˡ x = begin
  1B * x                 ≡⟨ sym (fromℕ∘toℕ (1B * x)) ⟩
  fromℕ (toℕ (1B * x))   ≡⟨ cong fromℕ (toℕ*homo 1B x) ⟩
  fromℕ (1 *ₙ n)         ≡⟨ cong fromℕ (ℕp.*-identityˡ n) ⟩
  fromℕ n                ≡⟨ fromℕ∘toℕ x ⟩
  x                      ∎
  where
  n = toℕ x

*-identityʳ : RightIdentity 1B _*_
*-identityʳ x =  trans (*-comm x 1B) (*-identityˡ x)

*-identity : Identity 1B _*_
*-identity = (*-identityˡ , *-identityʳ)

2B*x≡x+x :  ∀ x → 2B * x ≡ x + x
2B*x≡x+x x = begin
  2B * x            ≡⟨⟩
  (1B + 1B) * x     ≡⟨ *-distribʳ-+ x 1B 1B ⟩
  1B * x + 1B * x   ≡⟨ cong₂ _+_ (*-identityˡ x) (*-identityˡ x) ⟩
  x + x             ∎

2x≡x+x :  ∀ x → 2* x ≡ x + x
2x≡x+x x =  trans (2*≗2B* x) (2B*x≡x+x x)

[1+x]* :  ∀ x y → (1B + x) * y ≡ y + x * y
[1+x]* x y = begin
  (1B + x) * y     ≡⟨ *-distribʳ-+ y 1B x ⟩
  1B * y + x * y   ≡⟨ cong (_+ (x * y)) (*-identityˡ y) ⟩
  y + x * y        ∎

*[1+x] :  ∀ x y → y * (1B + x) ≡ y + y * x
*[1+x] x y = begin
  y * (1B + x)     ≡⟨ *-distribˡ-+ y 1B x ⟩
  y * 1B + y * x   ≡⟨ cong (_+ (y * x)) (*-identityʳ y) ⟩
  y + y * x        ∎

suc* :  ∀ x y → (suc x) * y ≡ y + x * y
suc* x y = begin
  (suc x) * y     ≡⟨ cong (_* y) (suc≗1+ x) ⟩
  (1B + x) * y    ≡⟨ [1+x]* x y ⟩
  y + x * y       ∎

*suc :  ∀ x y → x * (suc y) ≡ x + x * y
*suc x y = begin
  x * (suc y)    ≡⟨ cong (x *_) (suc≗1+ y) ⟩
  x * (1B + y)   ≡⟨ *[1+x] y x ⟩
  x + x * y      ∎

------------------------------------------------------------------------------
-- Multiplicative structure instances.
-- Instances for Bin up to CommutativeSemiring.
------------------------------------------------------------------------------

*-isMagma : IsMagma _≡_ _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _*_
  }

*-magma : Magma 0ℓ 0ℓ
*-magma = record{ isMagma = *-isMagma }

*-isSemigroup : IsSemigroup _≡_ _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record{ isSemigroup = *-isSemigroup }

*-1-isMonoid : IsMonoid _≡_ _*_ 1B
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { ε        = 1B
  ; isMonoid = *-1-isMonoid
  }

*-1-isCommutativeMonoid :  IsCommutativeMonoid _≡_ _*_ 1B
*-1-isCommutativeMonoid =  record
  { isSemigroup = *-isSemigroup
  ; identityˡ   = *-identityˡ
  ; comm        = *-comm
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record{ isCommutativeMonoid = *-1-isCommutativeMonoid
                              }

isSemiringWithoutAnnihilatingZero :
                           IsSemiringWithoutAnnihilatingZero _≡_ _+_ _*_ 0# 1B
isSemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +-0-isCommutativeMonoid
  ; *-isMonoid            = *-1-isMonoid
  ; distrib               = *-distrib-+
  }

isSemiring : IsSemiring _≡_ _+_ _*_ 0# 1B
isSemiring = record
  { isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero
  ; zero                              = *-zero
  }

semiring : Semiring 0ℓ 0ℓ
semiring = record
  { _+_        = _+_
  ; _*_        = _*_
  ; 0#         = 0#
  ; 1#         = 1B
  ; isSemiring = isSemiring
  }

isCommutativeSemiring : IsCommutativeSemiring _≡_ _+_ _*_ 0# 1B
isCommutativeSemiring = record
  { +-isCommutativeMonoid = +-0-isCommutativeMonoid
  ; *-isCommutativeMonoid = *-1-isCommutativeMonoid
  ; distribʳ              = *-distribʳ-+
  ; zeroˡ                 = *-zeroˡ
  }

commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
commutativeSemiring = record{ isCommutativeSemiring = isCommutativeSemiring }

