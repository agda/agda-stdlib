------------------------------------------------------------------------
-- The Agda standard library
--
-- Arithmetic of binary represented natural numbers. Initial part.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Bin0 where

open import Algebra using (Magma; Semigroup; Monoid; CommutativeMonoid)
import      Algebra.FunctionProperties as FuncProp
open import Algebra.Structures using (IsMagma; IsSemigroup; IsMonoid;
                                      IsCommutativeMonoid)
open import Data.Nat using (ℕ)
                     renaming (suc to 1+_; pred to pred'; _+_ to _+'_;
                               _*_ to _*'_; _∸_ to _∸'_)
     --
     -- Here renaming is applied in order to distinguish the
     -- corresponding operators from their Bin versions.
     --
open import Data.Nat.Properties as NatP using (2m≢1+2n)
     renaming (+-comm to +'-comm; +-assoc to +'-assoc;
               *-identityʳ to *'-identityʳ; *-distribˡ-+ to *'-lDistrib;
               *-cancelˡ-≡ to *'-lCancel
              )
open import Data.Product    using (_,_; proj₁; ∃)
open import Data.Sum        using (_⊎_; inj₁; inj₂)
open import Function        using (_∘_; id; const)
open import Level           using () renaming (zero to 0ℓ)
open import Relation.Binary using (Rel; Decidable; Setoid; DecSetoid;
                                                       IsDecEquivalence)
open import Relation.Binary.Core using (_←→_)
open import Relation.Binary.PropositionalEquality as PE using
                      (_≡_; _≢_; _≗_; refl; sym; cong; cong₂; isEquivalence)
open import Relation.Nullary          using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open PE.≡-Reasoning
import Algebra.Properties.Semigroup NatP.+-semigroup as Of+ℕ-semigroup


data Bin : Set
  where
  0#    : Bin
  2suc  : Bin → Bin    -- \n→ 2*(1+n)  arbitrary nonzero even
  suc2* : Bin → Bin    -- \n→ 1 + 2n   arbitrary odd
--
-- This representation is unique for each natural number.


open FuncProp (_≡_ {A = Bin}) using (Op₂; Associative; Commutative;
                                     LeftIdentity; RightIdentity;
                                     LeftZero; RightZero)

-- Decidable equality on Bin.

2suc-injective : {x y : Bin} → 2suc x ≡ 2suc y → x ≡ y

2suc-injective {0#}      {0#}      _    =  refl
2suc-injective {0#}      {2suc _}  ()
2suc-injective {0#}      {suc2* _} ()
2suc-injective {2suc _}  {0#}      ()
2suc-injective {2suc _}  {2suc _}  refl =  refl
2suc-injective {2suc _}  {suc2* _} ()
2suc-injective {suc2* _} {0#}      ()
2suc-injective {suc2* _} {2suc _}  ()
2suc-injective {suc2* _} {suc2* _} refl =  refl

suc2*-injective : {x y : Bin} → suc2* x ≡ suc2* y → x ≡ y

suc2*-injective {0#}      {0#}      _    =  refl
suc2*-injective {0#}      {2suc _}  ()
suc2*-injective {0#}      {suc2* _} ()
suc2*-injective {2suc _}  {0#}      ()
suc2*-injective {2suc _}  {2suc _}  refl =  refl
suc2*-injective {2suc _}  {suc2* _} ()
suc2*-injective {suc2* _} {0#}      ()
suc2*-injective {suc2* _} {2suc _}  ()
suc2*-injective {suc2* _} {suc2* _} refl =  refl


_≟_ :  Decidable (_≡_ {A = Bin})

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

2suc≢0 :  {x : Bin} → 2suc x ≢ 0#
2suc≢0 ()

suc2*≢0 :  {x : Bin} → suc2* x ≢ 0#
suc2*≢0 ()

size : Bin → ℕ       -- (number of constructors) - 1.
                       -- It is used in some termination proofs.
size 0#        = 0
size (2suc x)  = 1+ (size x)
size (suc2* x) = 1+ (size x)

|x|≡0⇒x≡0 :  {x : Bin} → size x ≡ 0 → x ≡ 0#
|x|≡0⇒x≡0 {0#}      _ =  refl
|x|≡0⇒x≡0 {2suc _}  ()
|x|≡0⇒x≡0 {suc2* _} ()

------------------------------------------------------------------------------
-- Arithmetic operations on Bin and their properties.
------------------------------------------------------------------------------
suc : Bin → Bin
suc 0#        =  suc2* 0#
suc (2suc x)  =  suc2* (suc x)   -- 1 + 2(1+x)
suc (suc2* x) =  2suc x          -- 1 + 1 + 2x =  2*(1+x)

1# = suc 0#;   2# = suc 1#;   3# = suc 2#;   4# = suc 3#;   5# = suc 4#

suc≢0 :  ∀ {x} → suc x ≢ 0#
suc≢0 {0#}      ()
suc≢0 {2suc _}  ()
suc≢0 {suc2* _} ()

infixl 6 _+_

_+_ : Op₂ Bin
0#        + y         =  y
x         + 0#        =  x
(2suc x)  + (2suc y)  =  2suc (suc (x + y))
                                       -- 2(1+x) + 2(1+y) =  2(1 + 1+x+y)
(2suc x)  + (suc2* y) =  suc (2suc (x + y))
                                       -- 2(1+x) + 1 + 2y =  1 + 2(1+x+y)
(suc2* x) + (2suc y)  =  suc (2suc (x + y))
(suc2* x) + (suc2* y) =  suc (suc2* (x + y))
                              -- 1+2x + 1+2y =  2 + 2(x+y) =  1 + 1 + 2(x+y)

x≢0⇒x+y≢0 :  {x : Bin} (y : Bin) → x ≢ 0# → x + y ≢ 0#
x≢0⇒x+y≢0 {2suc _} 0# _    =  λ()
x≢0⇒x+y≢0 {0#}     _  0≢0 =  contradiction refl 0≢0

2* : Bin → Bin
2* 0#        = 0#
2* (2suc x)  = 2suc (suc2* x)
                            -- 2(1+x) + 2(1+x) = 2(1+x + 1+x) =  2(1 + 1+2x)
2* (suc2* x) = 2suc (2* x)

pred : Bin → Bin
pred 0#        =  0#
pred (2suc x)  =  suc2* x   -- 2(1+x) - 1 =  1+2x
pred (suc2* x) =  2* x      -- 1 + 2x -1  =  2x

2suc-as∘ :  2suc ≗ 2* ∘ suc
2suc-as∘ 0#        =  refl
2suc-as∘ (2suc x)  =  begin
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


+-identityˡ : LeftIdentity 0# _+_
+-identityˡ _ = refl

+-identityʳ : RightIdentity 0# _+_
+-identityʳ 0#        = refl
+-identityʳ (2suc _)  = refl
+-identityʳ (suc2* _) = refl

2^ :  ℕ → Bin
2^ 0      =  1#
2^ (1+ n) =  2* (2^ n)


infixl 7 _*_

_*_ : Op₂ Bin

0#        * _         =  0#
_         * 0#        =  0#
(2suc x)  * (2suc y)  =  2* (2suc (x + (y + x * y)))
(2suc x)  * (suc2* y) =  2suc (x + y * (2suc x))
                      --
                      -- 2(1+x) * (1+2y) =  2(1 + 2y + x + 2xy)
                      --                 =  2(1 + x + y*2(1 + x))

(suc2* x) * (2suc y)  =  2suc (y + x * (2suc y))
(suc2* x) * (suc2* y) =  suc2* (x + y * (suc2* x))
            --
            -- (1 + 2x)(1 + 2y) =  1 + (2y + 2x + 4xy)
            --                     1 + 2(x + y * (1 + 2x))


infixl 8 _^_

_^_ : Bin → ℕ → Bin
_ ^ 0      =  1#
x ^ (1+ n) =  x * (x ^ n)

zeroˡ : LeftZero 0# _*_
zeroˡ _ = refl

zeroʳ : RightZero 0# _*_
zeroʳ 0#        = refl
zeroʳ (2suc _)  = refl
zeroʳ (suc2* _) = refl


x*y≡0⇒x≡0∨y≡0 :  ∀ x {y} → x * y ≡ 0# → x ≡ 0# ⊎ y ≡ 0#

x*y≡0⇒x≡0∨y≡0 0#        {_ }      _ =  inj₁ refl
x*y≡0⇒x≡0∨y≡0 _         {0#}      _ =  inj₂ refl
x*y≡0⇒x≡0∨y≡0 (2suc _)  {2suc _}  ()
x*y≡0⇒x≡0∨y≡0 (2suc _)  {suc2* _} ()
x*y≡0⇒x≡0∨y≡0 (suc2* _) {2suc _}  ()
x*y≡0⇒x≡0∨y≡0 (suc2* _) {suc2* _} ()

nz*nz :  {x y : Bin} → x ≢ 0# → y ≢ 0# → x * y ≢ 0#
nz*nz {x} {_} x≢0 y≢0 xy≡0  with x*y≡0⇒x≡0∨y≡0 x xy≡0
... | inj₁ x≡0 =  x≢0 x≡0
... | inj₂ y≡0 =  y≢0 y≡0


setoid : Setoid 0ℓ 0ℓ
setoid = PE.setoid Bin

2*≢1 :  {x : Bin} → 2* x ≢ 1#
2*≢1 {0#}      ()
2*≢1 {2suc _}  ()
2*≢1 {suc2* _} ()

suc≗1+ :  suc ≗ (1# +_)
suc≗1+ 0#        =  refl
suc≗1+ (2suc _)  =  refl
suc≗1+ (suc2* _) =  refl


suc+assoc :  (x y : Bin) → (suc x) + y ≡ suc (x + y)
suc+assoc 0# y = begin
  suc 0# + y     ≡⟨⟩
  1# + y         ≡⟨ sym (suc≗1+ y) ⟩
  suc y          ≡⟨⟩
  suc (0# + y)   ∎

suc+assoc x 0# = begin
  suc x + 0#     ≡⟨ +-identityʳ (suc x) ⟩
  suc x          ≡⟨ cong suc (sym (+-identityʳ x)) ⟩
  suc (x + 0#)   ∎

suc+assoc (2suc x) (2suc y) = begin
  (suc (2suc x)) + (2suc y)    ≡⟨⟩
  suc2* (suc x) + (2suc y)     ≡⟨⟩
  suc (2suc (suc x + y))       ≡⟨ cong (suc ∘ 2suc) (suc+assoc x y) ⟩
  suc (2suc (suc (x + y)))     ≡⟨⟩
  suc ((2suc x) + (2suc y))    ∎

suc+assoc (2suc x) (suc2* y) = begin
  (suc (2suc x)) + (suc2* y)     ≡⟨⟩
  (suc2* (suc x)) + (suc2* y)    ≡⟨⟩
  suc (suc2* (suc x + y))        ≡⟨ cong (suc ∘ suc2*) (suc+assoc x y) ⟩
  suc (suc2* (suc (x + y)))      ≡⟨⟩
  suc (suc (2suc (x + y)))       ≡⟨⟩
  suc ((2suc x) + (suc2* y))     ∎

suc+assoc (suc2* x) (2suc y)  =  refl
suc+assoc (suc2* x) (suc2* y) =  refl

1+≗suc :  (1# +_) ≗ suc
1+≗suc = suc+assoc 0#

toℕ : Bin → ℕ
toℕ 0#        =  0
toℕ (2suc x)  =  2 *' (1+ (toℕ x))
toℕ (suc2* x) =  1+ (2 *' (toℕ x))


private
  infixr 7 2*'_

  2*'_ : ℕ → ℕ
  2*'_ = (2 *'_)

toℕ∘2* :  (x : Bin) → toℕ (2* x) ≡ 2*' (toℕ x)
toℕ∘2* 0#       = refl
toℕ∘2* (2suc x) = begin
  toℕ (2* (2suc x))    ≡⟨⟩
  2*' (2 +' 2m)         ≡⟨ cong (2*'_ ∘ (_+' 2m)) (sym (*'-identityʳ 2)) ⟩
  2*' (2*' 1 +' 2m)     ≡⟨ cong 2*'_ (sym (*'-lDistrib 2 1 m)) ⟩
  2*' (2*' (1+ m))      ≡⟨⟩
  2*' (toℕ (2suc x))   ∎
  where
  m = toℕ x;  2m = 2*' m

toℕ∘2* (suc2* x) =  cong (2*'_ ∘ 1+_) (toℕ∘2* x)


toℕ∘suc :  (x : Bin) → toℕ (suc x) ≡ 1+ (toℕ x)
toℕ∘suc 0#        =  refl
toℕ∘suc (2suc x)  =  cong (1+_ ∘ (2 *'_)) (toℕ∘suc x)
toℕ∘suc (suc2* x) =  *'-lDistrib 2 1 (toℕ x)


toℕ∘pred :  (x : Bin) → toℕ (pred x) ≡ pred' (toℕ x)
toℕ∘pred x with x ≟ 0#
... | yes x≡0 = begin
  toℕ (pred x)   ≡⟨ cong (toℕ ∘ pred) x≡0 ⟩
  0               ≡⟨ sym (cong (pred' ∘ toℕ) x≡0) ⟩
  pred' (toℕ x)  ∎

... | no x≢0 = begin
  toℕ (pred x)           ≡⟨ cong (toℕ ∘ pred) (sym suc-px≡x) ⟩
  toℕ (pred (suc px))    ≡⟨ cong toℕ (pred∘suc px) ⟩
  toℕ px                 ≡⟨⟩
  pred' (1+ (toℕ px))    ≡⟨ cong pred' (sym (toℕ∘suc px)) ⟩
  pred' (toℕ (suc px))   ≡⟨ cong (pred' ∘ toℕ) suc-px≡x ⟩
  pred' (toℕ x)          ∎
  where
  px = pred x;  suc-px≡x = suc∘pred x x≢0


toℕ-x≡0←→x≡0 :  (x : Bin) → toℕ x ≡ 0 ←→ x ≡ 0#
toℕ-x≡0←→x≡0 0#        =  (const refl , const refl)
toℕ-x≡0←→x≡0 (2suc _)  =  ((λ()) , (λ()))
toℕ-x≡0←→x≡0 (suc2* _) =  ((λ()) , (λ()))


toℕ+homo :  (x y : Bin) → toℕ (x + y) ≡ toℕ x +' toℕ y
toℕ+homo 0# _  =  refl
toℕ+homo x  0# =  begin
  toℕ (x + 0#)       ≡⟨ cong toℕ (+-identityʳ x) ⟩
  toℕ x              ≡⟨ sym (+'-comm (toℕ x) 0) ⟩
  toℕ x +' 0         ≡⟨⟩
  toℕ x +' toℕ 0#   ∎

toℕ+homo (2suc x) (2suc y) = begin
  toℕ ((2suc x) + (2suc y))       ≡⟨⟩
  toℕ (2suc (suc (x + y)))        ≡⟨⟩
  2 *' (1+ (toℕ (suc (x + y))))   ≡⟨ cong (2*'_ ∘ 1+_) (toℕ∘suc (x + y)) ⟩
  2 *' (1+ (1+ toℕ (x + y)))      ≡⟨ cong (2*'_ ∘ 1+_ ∘ 1+_) (toℕ+homo x y) ⟩
  2 *' ((1+ (1+ (m +' n))))        ≡⟨ cong (2*'_ ∘ 1+_)
                                                     (sym (+'-assoc 1 m n)) ⟩
  2 *' ((1+ ((1+ m) +' n)))        ≡⟨ cong (2*'_ ∘ 1+_ ∘ (_+' n))
                                                          (+'-comm 1 m) ⟩
  2 *' ((1+ ((m +' 1) +' n)))      ≡⟨ cong (2*'_ ∘ 1+_) (+'-assoc m 1 n) ⟩
  2 *' ((1+ ((m +' (1+ n)))))      ≡⟨ cong 2*'_ (sym (+'-assoc 1 m (1+ n))) ⟩
  2 *' ((1+ m) +' (1+ n))          ≡⟨ *'-lDistrib 2 (1+ m) (1+ n) ⟩
  (2*' (1+ m)) +' (2*' (1+ n))     ≡⟨⟩
  toℕ (2suc x) +' toℕ (2suc y)   ∎
  where
  m = toℕ x;  n = toℕ y

toℕ+homo (2suc x) (suc2* y) = begin
  toℕ ((2suc x) + (suc2* y))     ≡⟨⟩
  toℕ (suc (2suc (x + y)))       ≡⟨ toℕ∘suc (2suc (x + y)) ⟩
  1+ (toℕ (2suc (x + y)))        ≡⟨⟩
  1+ (2*' (1+ (toℕ (x + y))))    ≡⟨ cong (1+_ ∘ 2*'_ ∘ 1+_) (toℕ+homo x y) ⟩
  1+ (2*' (1+ (m +' n)))          ≡⟨ cong (1+_ ∘ 2*'_) (sym (+'-assoc 1 m n)) ⟩
  1+ (2*' (1+m +' n))             ≡⟨ cong 1+_ (*'-lDistrib 2 1+m n) ⟩
  1+ ((2*' 1+m) +' 2*' n)         ≡⟨ Of+ℕ-semigroup.x∙yz≈y∙xz +'-comm
                                                            {1} {_} {2*' n} ⟩
  (2*' 1+m) +' (1+ (2*' n))       ≡⟨⟩
  toℕ (2suc x) +' toℕ (suc2* y)
  ∎
  where m = toℕ x;  n = toℕ y;  1+m = 1+ m


toℕ+homo (suc2* x) (2suc y) = begin
  toℕ ((suc2* x) + (2suc y))      ≡⟨⟩
  toℕ (suc (2suc (x + y)))        ≡⟨ toℕ∘suc (2suc (x + y)) ⟩
  1+ (toℕ (2suc (x + y)))         ≡⟨⟩
  1+ (2*' (1+ (toℕ (x + y))))     ≡⟨ cong (1+_ ∘ 2*'_ ∘ 1+_) (toℕ+homo x y)
                                    ⟩
  1+ (2*' (1+ (m +' n)))           ≡⟨ cong (1+_ ∘ 2*'_)
                                           (Of+ℕ-semigroup.x∙yz≈y∙xz +'-comm
                                                            {1} {m} {n})
                                    ⟩
  1+ (2*' (m +' 1+n))              ≡⟨ cong 1+_ (*'-lDistrib 2 m 1+n) ⟩
  1+ (2*' m +' 2*' 1+n)            ≡⟨ sym (+'-assoc 1 (2*' m) (2*' 1+n)) ⟩
  (1+ (2*' m)) +' (2*' (1+ n))     ≡⟨⟩
  toℕ (suc2* x) +' toℕ (2suc y)  ∎
  where
  m = toℕ x;  n = toℕ y;  1+n = 1+ n

toℕ+homo (suc2* x) (suc2* y) = begin
  toℕ ((suc2* x) + (suc2* y))      ≡⟨⟩
  toℕ (suc (suc2* (x + y)))        ≡⟨ toℕ∘suc (suc2* (x + y)) ⟩
  1+ (toℕ (suc2* (x + y)))         ≡⟨⟩
  1+ (1+ (2*' (toℕ (x + y))))      ≡⟨ cong (1+_ ∘ 1+_ ∘ 2*'_) (toℕ+homo x y) ⟩
  1+ (1+ (2*' (m +' n)))            ≡⟨ cong (1+_ ∘ 1+_) (*'-lDistrib 2 m n) ⟩
  1+ (1+ (2*' m +' 2*' n))          ≡⟨ cong 1+_ (sym (+'-assoc 1 (2*' m) _)) ⟩
  1+ ((1+ (2*' m) +' (2*' n)))      ≡⟨ (Of+ℕ-semigroup.x∙yz≈y∙xz +'-comm
                                                       {1} {1+ (2*' m)} {_}) ⟩
  (1+ (2*' m)) +' (1+ (2*' n))      ≡⟨⟩
  toℕ (suc2* x) +' toℕ (suc2* y)  ∎
  where
  m = toℕ x;  n = toℕ y


ext-fromℕ :  (n : ℕ) → ∃ (\x → toℕ x ≡ n)    -- Mind:  it costs O(n)
ext-fromℕ 0      =  (0# , refl)
ext-fromℕ (1+ n) =  aux (ext-fromℕ n)
  where
  aux :  ∃ (\x → toℕ x ≡ n) → ∃ (\y → toℕ y ≡ 1+ n)
  aux (x , toℕ-x≡n) =  (suc x , toℕ-suc-x≡1+n)
    where
    toℕ-suc-x≡1+n =  begin toℕ (suc x)   ≡⟨ toℕ∘suc x ⟩
                            1+ (toℕ x)    ≡⟨ cong 1+_ toℕ-x≡n ⟩
                            1+ n
                      ∎

fromℕ : ℕ → Bin
fromℕ = proj₁ ∘ ext-fromℕ

fromℕ+homo :  (m n : ℕ) → fromℕ (m +' n) ≡ fromℕ m + fromℕ n
fromℕ+homo 0      _ = refl
fromℕ+homo (1+ m) n = begin
  fromℕ ((1+ m) +' n)           ≡⟨⟩
  fromℕ (1+ (m +' n))           ≡⟨⟩
  suc (fromℕ (m +' n))          ≡⟨ cong suc (fromℕ+homo m n) ⟩
  suc (a + b)                    ≡⟨ sym (suc+assoc a b) ⟩
  (suc a) + b                    ≡⟨⟩
  (fromℕ (1+ m)) + (fromℕ n)   ∎
  where
  a = fromℕ m;  b = fromℕ n

toℕ∘fromℕ :  toℕ ∘ fromℕ ≗ id
toℕ∘fromℕ 0      = refl
toℕ∘fromℕ (1+ n) = begin
  toℕ (fromℕ (1+ n))    ≡⟨⟩
  toℕ (suc (fromℕ n))   ≡⟨ toℕ∘suc (fromℕ n) ⟩
  1+ (toℕ (fromℕ n))    ≡⟨ cong 1+_ (toℕ∘fromℕ n) ⟩
  1+ n                    ∎

toℕ-injective :  {x y : Bin} → toℕ x ≡ toℕ y → x ≡ y
toℕ-injective {0#}     {0#}      _  =  refl
toℕ-injective {0#}     {2suc _}  ()
toℕ-injective {0#}     {suc2* _} ()
toℕ-injective {2suc _} {0#}      ()
toℕ-injective {2suc x} {2suc y}  2[1+xN]≡2[1+yN] =  cong 2suc x≡y
  where
  xN        = toℕ x
  yN        = toℕ y
  1+xN≡1+yN = *'-lCancel {1+ xN} {1+ yN} 1 2[1+xN]≡2[1+yN]
  xN≡yN     = cong pred' 1+xN≡1+yN
  x≡y       = toℕ-injective xN≡yN

toℕ-injective {2suc x} {suc2* y} 2[1+xN]≡1+2yN =
                               contradiction 2[1+xN]≡1+2yN (2m≢1+2n 1+xN yN)
  where
  1+xN = 1+ (toℕ x);  yN = toℕ y

toℕ-injective {suc2* _} {0#} ()
toℕ-injective {suc2* x} {2suc y} 1+2xN≡2[1+yN] =
                         contradiction (sym 1+2xN≡2[1+yN]) (2m≢1+2n 1+yN xN)
  where
  xN = toℕ x;  1+yN = 1+ (toℕ y)

toℕ-injective {suc2* x} {suc2* y} 1+2xN≡1+2yN =  cong suc2* x≡y
  where
  xN = toℕ x;  yN = toℕ y;  2xN≡2yN = cong pred' 1+2xN≡1+2yN

  xN≡yN = *'-lCancel {xN} {yN} 1 2xN≡2yN;   x≡y = toℕ-injective xN≡yN


toℕ-surjective :  (y : ℕ) → ∃ (\x → toℕ x ≡ y)
toℕ-surjective 0      =  (0# , refl)
toℕ-surjective (1+ n) =
  let (a , toℕ-a≡n) = toℕ-surjective n
      toℕ-suc-a≡1+n = begin
        toℕ (suc a)   ≡⟨ toℕ∘suc a ⟩
        1+ (toℕ a)    ≡⟨ cong 1+_ toℕ-a≡n ⟩
        1+ n           ∎
  in
  (suc a , toℕ-suc-a≡1+n)


fromℕ∘toℕ :  fromℕ ∘ toℕ ≗ id
fromℕ∘toℕ a =
  let
    (b , toℕ-b≡toℕ-a) = ext-fromℕ (toℕ a)
  in
  begin fromℕ (toℕ a)   ≡⟨ refl ⟩
        b                 ≡⟨ toℕ-injective toℕ-b≡toℕ-a ⟩
        a
  ∎

------------------------------------------------------------------------------
-- Summary:
-- 1)  toℕ : Bin → ℕ  is an isomorphism by _+_,
-- 2)  fromℕ            is a homomorphisms by _+_ mutually inverse with toℕ.
------------------------------------------------------------------------------

fromℕ∘pred :  (n : ℕ) → fromℕ (pred' n) ≡ pred (fromℕ n)
fromℕ∘pred n =
  let (x , toℕ-x≡n) = ext-fromℕ n
  in
  begin
    fromℕ (pred' n)          ≡⟨ cong (fromℕ ∘ pred') (sym (toℕ∘fromℕ n)) ⟩
    fromℕ (pred' (toℕ x))   ≡⟨ cong fromℕ (sym (toℕ∘pred x)) ⟩
    fromℕ (toℕ (pred x))    ≡⟨ fromℕ∘toℕ (pred x) ⟩
    pred x                    ≡⟨ refl ⟩
    pred (fromℕ n)
  ∎


------------------------------------------------------------------------------
-- Commutativity and associativity for _+_ are proved by using the isomorphism
-- to ℕ.
------------------------------------------------------------------------------

+-comm :  Commutative _+_
+-comm a b = begin
  a + b                        ≡⟨ sym (fromℕ∘toℕ (a + b)) ⟩
  fromℕ (toℕ (a + b))        ≡⟨ cong fromℕ (toℕ+homo a b) ⟩
  fromℕ (toℕ a +' toℕ b)    ≡⟨ cong fromℕ (+'-comm (toℕ a) (toℕ b)) ⟩
  fromℕ (toℕ b +' toℕ a)    ≡⟨ cong fromℕ (sym (toℕ+homo b a)) ⟩
  fromℕ (toℕ (b + a))        ≡⟨ fromℕ∘toℕ (b + a) ⟩
  b + a                        ∎

+-assoc :  Associative _+_
+-assoc a b c = begin
  (a + b) + c                    ≡⟨ sym (fromℕ∘toℕ ((a + b) + c)) ⟩
  fromℕ (toℕ ((a + b) + c))    ≡⟨ cong fromℕ (toℕ+homo (a + b) c) ⟩
  fromℕ (toℕ (a + b) +' cN)    ≡⟨ cong (fromℕ ∘ (_+' cN)) (toℕ+homo a b) ⟩
  fromℕ ((aN +' bN) +' cN)      ≡⟨ cong fromℕ (+'-assoc aN bN cN) ⟩
  fromℕ (aN +' (bN +' cN))      ≡⟨ cong (fromℕ ∘ (aN +'_))
                                                  (sym (toℕ+homo b c)) ⟩
  fromℕ (aN +' toℕ (b + c))    ≡⟨ cong fromℕ (sym (toℕ+homo a (b + c))) ⟩
  fromℕ (toℕ (a + (b + c)))    ≡⟨ fromℕ∘toℕ (a + (b + c)) ⟩
  (a + (b + c))                  ∎
  where
  aN = toℕ a;   bN = toℕ b;   cN = toℕ c


+-lCancel :  ∀ x y z → x + y ≡ x + z → y ≡ z      -- the proof is via toℕ
+-lCancel x y z x+y≡x+z = begin
  y          ≡⟨ sym (fromℕ∘toℕ y) ⟩
  fromℕ m   ≡⟨ cong fromℕ m≡n ⟩
  fromℕ n   ≡⟨ fromℕ∘toℕ z ⟩
  z          ∎
  where
  k = toℕ x;  m = toℕ y;  n = toℕ z

  eq = begin
    k +' m          ≡⟨ sym (toℕ+homo x y) ⟩
    toℕ (x + y)    ≡⟨ cong toℕ x+y≡x+z ⟩
    toℕ (x + z)    ≡⟨ toℕ+homo x z ⟩
    k +' n          ∎

  m≡n = begin
    m                ≡⟨ sym (NatP.m+n∸n≡m m k)⟩
    (m +' k) ∸' k    ≡⟨ cong (_∸' k) (+'-comm m k) ⟩
    (k +' m) ∸' k    ≡⟨ cong (_∸' k) eq ⟩
    (k +' n) ∸' k    ≡⟨ cong (_∸' k) (+'-comm k n) ⟩
    (n +' k) ∸' k    ≡⟨ NatP.m+n∸n≡m n k ⟩
    n                ∎

+-rCancel :  ∀ x y z → y + x ≡ z + x → y ≡ z
+-rCancel x y z y+x≡z+x =  +-lCancel x y z x+y≡x+z
  where
  x+y≡x+z = begin
    x + y   ≡⟨ +-comm x y ⟩
    y + x   ≡⟨ y+x≡z+x ⟩
    z + x   ≡⟨ +-comm z x ⟩
    x + z   ∎

decEquivalence :  IsDecEquivalence (_≡_ {A = Bin})
decEquivalence =  record{ isEquivalence = isEquivalence;  _≟_ = _≟_ }

decSetoid : DecSetoid 0ℓ 0ℓ
decSetoid = record{ Carrier          =  Bin
                  ; _≈_              =  _≡_
                  ; isDecEquivalence =  decEquivalence }

+-isMagma :  IsMagma _≡_ _+_
+-isMagma =  record{ isEquivalence =  isEquivalence
                   ; ∙-cong        =  cong₂ _+_
                   }

+-magma :  Magma 0ℓ 0ℓ
+-magma =  record{ Carrier = Bin
                 ; _≈_     = _≡_
                 ; _∙_     = _+_
                 ; isMagma = +-isMagma
                 }

+-isSemigroup : IsSemigroup _≡_ _+_
+-isSemigroup = record{ isMagma = +-isMagma;  assoc = +-assoc }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record{ Carrier     = Bin
                    ; _≈_         = _≡_
                    ; _∙_         = _+_
                    ; isSemigroup = +-isSemigroup }

+-isMonoid : IsMonoid _≡_ _+_ 0#
+-isMonoid = record{ isSemigroup = +-isSemigroup;
                     identity    = (+-identityˡ , +-identityʳ) }

+-monoid : Monoid 0ℓ 0ℓ
+-monoid = record{ Carrier  = Bin
                 ; _≈_      = _≡_
                 ; _∙_      = _+_
                 ; ε        = 0#
                 ; isMonoid = +-isMonoid }

+-isCommutativeMonoid : IsCommutativeMonoid _≡_ _+_ 0#
+-isCommutativeMonoid = record{ isSemigroup = +-isSemigroup
                              ; identityˡ   = +-identityˡ
                              ; comm        = +-comm }

+-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-commutativeMonoid = record{ Carrier =  Bin
                            ; _≈_     =  _≡_
                            ; _∙_     =  _+_
                            ; ε       =  0#
                            ; isCommutativeMonoid = +-isCommutativeMonoid }
