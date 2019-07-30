------------------------------------------------------------------------
-- The Agda standard library
--
-- Arithmetic properties related to addition and multiplication of
-- binary represented natural numbers.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Properties where

open import Algebra
open import Algebra.Morphism
import Algebra.Morphism.RawMonoid as MonoidMorphisms
open import Algebra.FunctionProperties.Consequences.Propositional
open import Data.Bin.Base
open import Data.Nat as ℕ using (ℕ; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Solver
open import Data.Product using (_,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; _$_; id; const)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation using (contradiction)
open import Algebra.FunctionProperties {A = Bin} _≡_
open import Algebra.Structures {A = Bin} _≡_
import Algebra.Properties.CommutativeSemigroup ℕₚ.+-semigroup ℕₚ.+-comm
  as Of+ℕ-semigroup
import Algebra.Properties.CommutativeSemigroup ℕₚ.*-semigroup ℕₚ.*-comm
  as Of*ℕ-semigroup
open ≡-Reasoning
open +-*-Solver

------------------------------------------------------------------------
-- Properties of size

|x|≡0⇒x≡0 :  ∀ {x} → size x ≡ 0 → x ≡ 0B
|x|≡0⇒x≡0 {zero} refl =  refl

------------------------------------------------------------------------
-- Properties of _≡_
------------------------------------------------------------------------

2[1+x]≢0 : ∀ {x} → 2[1+ x ] ≢ 0B
2[1+x]≢0 ()

1+[2x]≢0 : ∀ {x} → 1+[2 x ] ≢ 0B
1+[2x]≢0 ()

2[1+-injective : ∀ {x y} → 2[1+ x ] ≡ 2[1+ y ] → x ≡ y
2[1+-injective refl = refl

1+[2-injective : ∀ {x y} → 1+[2 x ] ≡ 1+[2 y ] → x ≡ y
1+[2-injective refl = refl

_≟_ :  Decidable {A = Bin} _≡_
zero     ≟ zero     =  yes refl
zero     ≟ 2[1+ _ ] =  no λ()
zero     ≟ 1+[2 _ ] =  no λ()
2[1+ _ ] ≟ zero     =  no λ()
2[1+ x ] ≟ 2[1+ y ] =  Dec.map′ (cong 2[1+_]) 2[1+-injective (x ≟ y)
2[1+ _ ] ≟ 1+[2 _ ] =  no λ()
1+[2 _ ] ≟ zero     =  no λ()
1+[2 _ ] ≟ 2[1+ _ ] =  no λ()
1+[2 x ] ≟ 1+[2 y ] =  Dec.map′ (cong 1+[2_]) 1+[2-injective (x ≟ y)

≡-isDecEquivalence :  IsDecEquivalence {A = Bin} _≡_
≡-isDecEquivalence = record
  { isEquivalence = isEquivalence
  ; _≟_           = _≟_
  }

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid Bin

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = record
  {isDecEquivalence = ≡-isDecEquivalence
  }

------------------------------------------------------------------------
-- Properties of double
------------------------------------------------------------------------

2[1+_]-as∘ : 2[1+_] ≗ double ∘ suc
2[1+_]-as∘ zero     =  refl
2[1+_]-as∘ 2[1+ x ] =  cong 2[1+_] (2[1+_]-as∘ x)
2[1+_]-as∘ 1+[2 x ] =  refl

1+[2_]-as∘ : 1+[2_] ≗ suc ∘ double
1+[2_]-as∘ zero     = refl
1+[2_]-as∘ 2[1+ x ] = refl
1+[2_]-as∘ 1+[2 x ] = begin
  1+[2 1+[2 x ] ]         ≡⟨ cong 1+[2_] (1+[2_]-as∘ x) ⟩
  1+[2 (suc 2x) ]         ≡⟨⟩
  suc 2[1+ 2x ]           ≡⟨ cong suc (2[1+_]-as∘ 2x) ⟩
  suc (double (suc 2x))   ≡⟨ cong (suc ∘ double) (sym (1+[2_]-as∘ x)) ⟩
  suc (double 1+[2 x ])   ∎
  where 2x = double x

double[x]≡0⇒x≡0 : ∀ {x} → double x ≡ zero → x ≡ zero
double[x]≡0⇒x≡0 {zero} _ = refl

x≢0⇒double[x]≢0 : ∀ {x} → x ≢ zero → double x ≢ zero
x≢0⇒double[x]≢0 x≢0 = x≢0 ∘ double[x]≡0⇒x≡0

double≢1 : ∀ {x} → double x ≢ 1B
double≢1 {zero} ()

------------------------------------------------------------------------
-- Properties of suc/pred
------------------------------------------------------------------------

suc≢0 : ∀ {x} → suc x ≢ zero
suc≢0 {zero}     ()
suc≢0 {2[1+ _ ]} ()
suc≢0 {1+[2 _ ]} ()

pred-suc : pred ∘ suc ≗ id
pred-suc zero     =  refl
pred-suc 2[1+ x ] =  sym (2[1+_]-as∘ x)
pred-suc 1+[2 x ] =  refl

suc-pred : ∀ {x} → x ≢ zero → suc (pred x) ≡ x
suc-pred {zero}     0≢0 =  contradiction refl 0≢0
suc-pred {2[1+ _ ]} _   =  refl
suc-pred {1+[2 x ]} _   =  sym (1+[2_]-as∘ x)

------------------------------------------------------------------------
-- Properties of toℕ & fromℕ
------------------------------------------------------------------------

toℕ-double : ∀ x → toℕ (double x) ≡ 2 ℕ.* (toℕ x)
toℕ-double zero     =  refl
toℕ-double 1+[2 x ] =  cong ((2 ℕ.*_) ∘ ℕ.suc) (toℕ-double x)
toℕ-double 2[1+ x ] =  cong (2 ℕ.*_) (sym (ℕₚ.*-distribˡ-+ 2 1 (toℕ x)))

toℕ-suc : ∀ x → toℕ (suc x) ≡ ℕ.suc (toℕ x)
toℕ-suc zero     =  refl
toℕ-suc 2[1+ x ] =  cong (ℕ.suc ∘ (2 ℕ.*_)) (toℕ-suc x)
toℕ-suc 1+[2 x ] =  ℕₚ.*-distribˡ-+ 2 1 (toℕ x)

toℕ-pred : ∀ x → toℕ (pred x) ≡ ℕ.pred (toℕ x)
toℕ-pred zero     =  refl
toℕ-pred 2[1+ x ] =  cong ℕ.pred $ sym $ ℕₚ.*-distribˡ-+ 2 1 (toℕ x)
toℕ-pred 1+[2 x ] =  toℕ-double x

toℕ-fromℕ : toℕ ∘ fromℕ ≗ id
toℕ-fromℕ 0         = refl
toℕ-fromℕ (ℕ.suc n) = begin
  toℕ (fromℕ (ℕ.suc n))   ≡⟨⟩
  toℕ (suc (fromℕ n))     ≡⟨ toℕ-suc (fromℕ n) ⟩
  ℕ.suc (toℕ (fromℕ n))   ≡⟨ cong ℕ.suc (toℕ-fromℕ n) ⟩
  ℕ.suc n                 ∎

toℕ-injective :  ∀ {x y} → toℕ x ≡ toℕ y → x ≡ y
toℕ-injective {zero}     {zero}     _               =  refl
toℕ-injective {2[1+ x ]} {2[1+ y ]} 2[1+xN]≡2[1+yN] =  cong 2[1+_] x≡y
  where
  1+xN≡1+yN = ℕₚ.*-cancelˡ-≡ {ℕ.suc (toℕ x)} {ℕ.suc (toℕ y)} 1 2[1+xN]≡2[1+yN]
  xN≡yN     = cong ℕ.pred 1+xN≡1+yN
  x≡y       = toℕ-injective xN≡yN

toℕ-injective {2[1+ x ]} {1+[2 y ]} 2[1+xN]≡1+2yN =
  contradiction 2[1+xN]≡1+2yN (ℕₚ.even≢odd (ℕ.suc (toℕ x)) (toℕ y))

toℕ-injective {1+[2 x ]} {2[1+ y ]} 1+2xN≡2[1+yN] =
  contradiction (sym 1+2xN≡2[1+yN]) (ℕₚ.even≢odd (ℕ.suc (toℕ y)) (toℕ x))

toℕ-injective {1+[2 x ]} {1+[2 y ]} 1+2xN≡1+2yN =  cong 1+[2_] x≡y
  where
  2xN≡2yN = cong ℕ.pred 1+2xN≡1+2yN
  xN≡yN   = ℕₚ.*-cancelˡ-≡ 1 2xN≡2yN
  x≡y     = toℕ-injective xN≡yN

toℕ-surjective :  ∀ n → ∃ (λ x → toℕ x ≡ n)
toℕ-surjective n =  (fromℕ n , toℕ-fromℕ n)

fromℕ-toℕ :  fromℕ ∘ toℕ ≗ id
fromℕ-toℕ =  toℕ-injective ∘ toℕ-fromℕ ∘ toℕ

fromℕ-pred : ∀ n → fromℕ (ℕ.pred n) ≡ pred (fromℕ n)
fromℕ-pred n = begin
  fromℕ (ℕ.pred n)        ≡⟨ cong (fromℕ ∘ ℕ.pred) (sym (toℕ-fromℕ n)) ⟩
  fromℕ (ℕ.pred (toℕ x))  ≡⟨ cong fromℕ (sym (toℕ-pred x)) ⟩
  fromℕ (toℕ (pred x))    ≡⟨ fromℕ-toℕ (pred x) ⟩
  pred x                  ≡⟨ refl ⟩
  pred (fromℕ n)          ∎
  where x = fromℕ n

x≡0⇒toℕ[x]≡0 :  ∀ {x} → x ≡ zero → toℕ x ≡ 0
x≡0⇒toℕ[x]≡0 {zero} _ = refl

toℕ[x]≡0⇒x≡0 :  ∀ {x} → toℕ x ≡ 0 → x ≡ zero
toℕ[x]≡0⇒x≡0 {zero} _ = refl

------------------------------------------------------------------------
-- Properties of _+_
------------------------------------------------------------------------

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  }

+-0-rawMonoid : RawMonoid 0ℓ 0ℓ
+-0-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε   = 0B
  }

------------------------------------------------------------------------
-- toℕ/fromℕ are homomorphisms for _+_

toℕ-homo-+ :  ∀ x y → toℕ (x + y) ≡ toℕ x ℕ.+ toℕ y
toℕ-homo-+ zero     _        = refl
toℕ-homo-+ 2[1+ x ] zero     = cong ℕ.suc (sym (ℕₚ.+-identityʳ _))
toℕ-homo-+ 1+[2 x ] zero     = cong ℕ.suc (sym (ℕₚ.+-identityʳ _))
toℕ-homo-+ 2[1+ x ] 2[1+ y ] = begin
  toℕ (2[1+ x ] + 2[1+ y ])          ≡⟨⟩
  toℕ 2[1+ (suc (x + y)) ]           ≡⟨⟩
  2 ℕ.* (1 ℕ.+ (toℕ (suc (x + y))))  ≡⟨ cong ((2 ℕ.*_) ∘ ℕ.suc) (toℕ-suc (x + y)) ⟩
  2 ℕ.* (2 ℕ.+ toℕ (x + y))          ≡⟨ cong ((2 ℕ.*_) ∘ (2 ℕ.+_)) (toℕ-homo-+ x y) ⟩
  2 ℕ.* (2 ℕ.+ (toℕ x ℕ.+ toℕ y))    ≡⟨ solve 2 (λ m n → con 2 :* (con 2 :+ (m :+ n))  :=
                                          con 2 :* (con 1 :+ m) :+ con 2 :* (con 1 :+ n))
                                          refl (toℕ x) (toℕ y) ⟩
  toℕ 2[1+ x ] ℕ.+ toℕ 2[1+ y ]      ∎

toℕ-homo-+ 2[1+ x ] 1+[2 y ] = begin
  toℕ (2[1+ x ] + 1+[2 y ])             ≡⟨⟩
  toℕ (suc 2[1+ (x + y) ])              ≡⟨ toℕ-suc 2[1+ (x + y) ] ⟩
  ℕ.suc (toℕ 2[1+ (x + y) ])            ≡⟨⟩
  ℕ.suc (2 ℕ.* (ℕ.suc (toℕ (x + y))))   ≡⟨ cong (λ v → ℕ.suc (2 ℕ.* ℕ.suc v)) (toℕ-homo-+ x y) ⟩
  ℕ.suc (2 ℕ.* (ℕ.suc (m ℕ.+ n)))       ≡⟨ solve 2 (λ m n → con 1 :+ (con 2 :* (con 1 :+ (m :+ n))) :=
                                             con 2 :* (con 1 :+ m) :+ (con 1 :+ (con 2 :* n)))
                                             refl m n ⟩
  (2 ℕ.* ℕ.suc m) ℕ.+ (ℕ.suc (2 ℕ.* n)) ≡⟨⟩
  toℕ 2[1+ x ] ℕ.+ toℕ 1+[2 y ]         ∎
  where m = toℕ x; n = toℕ y

toℕ-homo-+ 1+[2 x ] 2[1+ y ] = begin
  toℕ (1+[2 x ] + 2[1+ y ])                 ≡⟨⟩
  toℕ (suc 2[1+ (x + y) ])                  ≡⟨ toℕ-suc 2[1+ (x + y) ] ⟩
  ℕ.suc (toℕ 2[1+ (x + y) ])                ≡⟨⟩
  ℕ.suc (2 ℕ.* (ℕ.suc (toℕ (x + y))))       ≡⟨ cong (ℕ.suc ∘ (2 ℕ.*_) ∘ ℕ.suc) (toℕ-homo-+ x y) ⟩
  ℕ.suc (2 ℕ.* (ℕ.suc (m ℕ.+ n)))           ≡⟨ solve 2 (λ m n → con 1 :+ (con 2 :* (con 1 :+ (m :+ n))) :=
                                                 (con 1 :+ (con 2 :* m)) :+ (con 2 :* (con 1 :+ n)))
                                                 refl m n ⟩
  (ℕ.suc (2 ℕ.* m)) ℕ.+ (2 ℕ.* (ℕ.suc n))   ≡⟨⟩
  toℕ 1+[2 x ] ℕ.+ toℕ 2[1+ y ]             ∎
  where m = toℕ x;  n = toℕ y

toℕ-homo-+ 1+[2 x ] 1+[2 y ] = begin
  toℕ (1+[2 x ] + 1+[2 y ])               ≡⟨⟩
  toℕ (suc 1+[2 (x + y) ])                ≡⟨ toℕ-suc 1+[2 (x + y) ] ⟩
  ℕ.suc (toℕ 1+[2 (x + y) ])              ≡⟨⟩
  ℕ.suc (ℕ.suc (2 ℕ.* (toℕ (x + y))))     ≡⟨ cong (ℕ.suc ∘ ℕ.suc ∘ (2 ℕ.*_)) (toℕ-homo-+ x y) ⟩
  ℕ.suc (ℕ.suc (2 ℕ.* (m ℕ.+ n)))         ≡⟨ solve 2 (λ m n → con 1 :+ (con 1 :+ (con 2 :* (m :+ n))) :=
                                               (con 1 :+ (con 2 :* m)) :+ (con 1 :+ (con 2 :* n)))
                                               refl m n ⟩
  (ℕ.suc (2 ℕ.* m)) ℕ.+ (ℕ.suc (2 ℕ.* n)) ≡⟨⟩
  toℕ 1+[2 x ] ℕ.+ toℕ 1+[2 y ]           ∎
  where m = toℕ x;  n = toℕ y

toℕ-+-isRawMagmaMorphism : IsRawMagmaMorphism +-rawMagma ℕₚ.+-rawMagma toℕ
toℕ-+-isRawMagmaMorphism = record
  { F-isMagma = isMagma _+_
  ; T-isMagma = ℕₚ.+-isMagma
  ; ⟦⟧-cong   = cong toℕ
  ; ∙-homo    = toℕ-homo-+
  }

toℕ-+-isRawMonoidMorphism : IsRawMonoidMorphism +-0-rawMonoid ℕₚ.+-0-rawMonoid toℕ
toℕ-+-isRawMonoidMorphism = record
  { magma-homo = toℕ-+-isRawMagmaMorphism
  ; ε-homo     = refl
  }

suc≗1+ : suc ≗ 1B +_
suc≗1+ zero     = refl
suc≗1+ 2[1+ _ ] = refl
suc≗1+ 1+[2 _ ] = refl

suc-+ : ∀ x y → suc x + y ≡ suc (x + y)
suc-+ zero        y     =  sym (suc≗1+ y)
suc-+ 2[1+ x ] zero     =  refl
suc-+ 1+[2 x ] zero     =  refl
suc-+ 2[1+ x ] 2[1+ y ] =  cong (suc ∘ 2[1+_]) (suc-+ x y)
suc-+ 2[1+ x ] 1+[2 y ] =  cong (suc ∘ 1+[2_]) (suc-+ x y)
suc-+ 1+[2 x ] 2[1+ y ] =  refl
suc-+ 1+[2 x ] 1+[2 y ] =  refl

1+≗suc : (1B +_) ≗ suc
1+≗suc = suc-+ zero

fromℕ-homo-+ : ∀ m n → fromℕ (m ℕ.+ n) ≡ fromℕ m + fromℕ n
fromℕ-homo-+ 0         _ = refl
fromℕ-homo-+ (ℕ.suc m) n = begin
  fromℕ ((ℕ.suc m) ℕ.+ n)          ≡⟨⟩
  suc (fromℕ (m ℕ.+ n))            ≡⟨ cong suc (fromℕ-homo-+ m n) ⟩
  suc (a + b)                      ≡⟨ sym (suc-+ a b) ⟩
  (suc a) + b                      ≡⟨⟩
  (fromℕ (ℕ.suc m)) + (fromℕ n)    ∎
  where a = fromℕ m;  b = fromℕ n

------------------------------------------------------------------------
-- Algebraic properties of _+_

-- Mostly proved by using the isomorphism between `ℕ` and `Bin` provided
-- by `toℕ`/`fromℕ`.

module _ where

  open MonoidMorphisms toℕ-+-isRawMonoidMorphism toℕ-injective

  +-assoc :  Associative _+_
  +-assoc = assoc-homo ℕₚ.+-assoc

  +-comm :  Commutative _+_
  +-comm = comm-homo ℕₚ.+-comm

  +-identityˡ : LeftIdentity zero _+_
  +-identityˡ _ = refl

  +-identityʳ : RightIdentity zero _+_
  +-identityʳ = identityʳ-homo ℕₚ.+-identityʳ

  +-identity : Identity zero _+_
  +-identity = +-identityˡ , +-identityʳ

  +-cancelˡ-≡ : LeftCancellative _+_
  +-cancelˡ-≡ = cancelˡ-homo ℕₚ.+-cancelˡ-≡

  +-cancelʳ-≡ : RightCancellative _+_
  +-cancelʳ-≡ = cancelʳ-homo ℕₚ.+-cancelʳ-≡

------------------------------------------------------------------------
-- Structures

  +-isMagma : IsMagma _+_
  +-isMagma = isMagma _+_

  +-isSemigroup : IsSemigroup _+_
  +-isSemigroup = isSemigroup-homo ℕₚ.+-isSemigroup

  +-0-isMonoid : IsMonoid _+_ 0B
  +-0-isMonoid = isMonoid-homo ℕₚ.+-0-isMonoid

  +-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0B
  +-0-isCommutativeMonoid = isCommutativeMonoid-homo ℕₚ.+-0-isCommutativeMonoid

------------------------------------------------------------------------
-- Packages

+-magma : Magma 0ℓ 0ℓ
+-magma = magma _+_

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { ε        = zero
  ; isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

------------------------------------------------------------------------
-- Other properties

x≢0⇒x+y≢0 : ∀ {x} (y : Bin) → x ≢ zero → x + y ≢ zero
x≢0⇒x+y≢0 {2[1+ _ ]} zero _   =  λ()
x≢0⇒x+y≢0 {zero}     _    0≢0 =  contradiction refl 0≢0

------------------------------------------------------------------------
-- Properties of _*_
------------------------------------------------------------------------

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  }

*-1-rawMonoid : RawMonoid 0ℓ 0ℓ
*-1-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  ; ε   = 1B
  }

------------------------------------------------------------------------
-- toℕ/fromℕ are homomorphisms for _*_

private  2*ₙ2*ₙ =  (2 ℕ.*_) ∘ (2 ℕ.*_)

toℕ-homo-* :  ∀ x y → toℕ (x * y) ≡ toℕ x ℕ.* toℕ y
toℕ-homo-* x y = aux x y (size x ℕ.+ size y) ℕₚ.≤-refl
  where
  aux :  (x y : Bin) → (cnt : ℕ) → (size x ℕ.+ size y ℕ.≤ cnt) →
         toℕ (x * y) ≡ toℕ x ℕ.* toℕ y

  aux zero     _        _ _ = refl
  aux 2[1+ x ] zero     _ _ = sym (ℕₚ.*-zeroʳ (toℕ x ℕ.+ (ℕ.suc (toℕ x ℕ.+ 0))))
  aux 1+[2 x ] zero     _ _ = sym (ℕₚ.*-zeroʳ (toℕ x ℕ.+ (toℕ x ℕ.+ 0)))
  aux 2[1+ x ] 2[1+ y ] (ℕ.suc cnt) (s≤s |x|+1+|y|≤cnt) = begin
    toℕ (2[1+ x ] * 2[1+ y ])                ≡⟨⟩
    toℕ (double 2[1+ (x + (y + xy)) ])       ≡⟨ toℕ-double 2[1+ (x + (y + xy)) ] ⟩
    2 ℕ.* (toℕ 2[1+ (x + (y + xy)) ])        ≡⟨⟩
    2*ₙ2*ₙ (ℕ.suc (toℕ (x + (y + xy))))      ≡⟨ cong (2*ₙ2*ₙ ∘ ℕ.suc) (toℕ-homo-+ x (y + xy)) ⟩
    2*ₙ2*ₙ (ℕ.suc (m ℕ.+ (toℕ (y + xy))))    ≡⟨ cong (2*ₙ2*ₙ ∘ ℕ.suc ∘ (m ℕ.+_)) (toℕ-homo-+ y xy) ⟩
    2*ₙ2*ₙ (ℕ.suc (m ℕ.+ (n ℕ.+ toℕ xy)))    ≡⟨ cong (2*ₙ2*ₙ ∘ ℕ.suc ∘ (m ℕ.+_) ∘ (n ℕ.+_))
                                                  (aux x y cnt |x|+|y|≤cnt) ⟩
    2*ₙ2*ₙ (ℕ.suc (m ℕ.+ (n ℕ.+ (m ℕ.* n)))) ≡⟨ solve 2 (λ m n → con 2 :* (con 2 :* (con 1 :+ (m :+ (n :+ m :* n)))) :=
                                                  (con 2 :* (con 1 :+ m)) :* (con 2 :* (con 1 :+ n)))
                                                  refl m n ⟩
    (2 ℕ.* (1 ℕ.+ m)) ℕ.* (2 ℕ.* (1 ℕ.+ n))  ≡⟨⟩
    toℕ 2[1+ x ] ℕ.* toℕ 2[1+ y ]            ∎
    where
    m = toℕ x;  n = toℕ y;  xy = x * y

    |x|+|y|≤cnt = ℕₚ.≤-trans (ℕₚ.+-monoʳ-≤ (size x) (ℕₚ.n≤1+n (size y))) |x|+1+|y|≤cnt

  aux 2[1+ x ] 1+[2 y ] (ℕ.suc cnt) (s≤s |x|+1+|y|≤cnt) = begin
    toℕ (2[1+ x ] * 1+[2 y ])                  ≡⟨⟩
    toℕ (2[1+ (x + y * 2[1+ x ]) ])            ≡⟨⟩
    2 ℕ.* (ℕ.suc (toℕ (x + y * 2[1+ x ])))     ≡⟨ cong ((2 ℕ.*_) ∘ ℕ.suc) (toℕ-homo-+ x _) ⟩
    2 ℕ.* (ℕ.suc (m ℕ.+ (toℕ (y * 2[1+ x ])))) ≡⟨ cong ((2 ℕ.*_) ∘ ℕ.suc ∘ (m ℕ.+_))
                                                    (aux y 2[1+ x ] cnt |y|+1+|x|≤cnt) ⟩
    2 ℕ.* (1+m ℕ.+ (n ℕ.* (toℕ 2[1+ x ])))     ≡⟨⟩
    2 ℕ.* (1+m ℕ.+ (n ℕ.* 2[1+m]))             ≡⟨ solve 2 (λ m n →
                                                    con 2 :* ((con 1 :+ m) :+ (n :* (con 2 :* (con 1 :+ m)))) :=
                                                    (con 2 :* (con 1 :+ m)) :* (con 1 :+ con 2 :* n))
                                                    refl m n ⟩
    2[1+m] ℕ.* (ℕ.suc (2 ℕ.* n))               ≡⟨⟩
    toℕ 2[1+ x ] ℕ.* toℕ 1+[2 y ]              ∎
    where
    m = toℕ x;   n = toℕ y;   1+m = ℕ.suc m;   2[1+m] = 2 ℕ.* (ℕ.suc m)

    eq : size x ℕ.+ (ℕ.suc (size y)) ≡ size y ℕ.+ (ℕ.suc (size x))
    eq = Of+ℕ-semigroup.x∙yz≈z∙yx (size x) 1 _

    |y|+1+|x|≤cnt =  subst (ℕ._≤ cnt) eq |x|+1+|y|≤cnt

  aux 1+[2 x ] 2[1+ y ] (ℕ.suc cnt) (s≤s |x|+1+|y|≤cnt) = begin
    toℕ (1+[2 x ] * 2[1+ y ])                  ≡⟨⟩
    toℕ 2[1+ (y + x * 2[1+ y ]) ]              ≡⟨⟩
    2 ℕ.* (ℕ.suc (toℕ (y + x * 2[1+ y ])))     ≡⟨ cong ((2 ℕ.*_) ∘ ℕ.suc)
                                                    (toℕ-homo-+ y (x * 2[1+ y ])) ⟩
    2 ℕ.* (ℕ.suc (n ℕ.+ (toℕ (x * 2[1+ y ])))) ≡⟨ cong ((2 ℕ.*_) ∘ ℕ.suc ∘ (n ℕ.+_))
                                                    (aux x 2[1+ y ] cnt |x|+1+|y|≤cnt) ⟩
    2 ℕ.* (1+n ℕ.+ (m ℕ.* toℕ 2[1+ y ]))       ≡⟨⟩
    2 ℕ.* (1+n ℕ.+ (m ℕ.* 2[1+n]))             ≡⟨ solve 2 (λ m n →
                                                    con 2 :* ((con 1 :+ n) :+ (m :* (con 2 :* (con 1 :+ n)))) :=
                                                    (con 1 :+ (con 2 :* m)) :* (con 2 :* (con 1 :+ n)))
                                                    refl m n ⟩
    (ℕ.suc 2m) ℕ.* 2[1+n]                      ≡⟨⟩
    toℕ 1+[2 x ] ℕ.* toℕ 2[1+ y ]              ∎
    where
    m  = toℕ x;     n      = toℕ y;            1+n = ℕ.suc n
    2m = 2 ℕ.* m;   2[1+n] = 2 ℕ.* (ℕ.suc n)


  aux 1+[2 x ] 1+[2 y ] (ℕ.suc cnt) (s≤s |x|+1+|y|≤cnt) = begin
    toℕ (1+[2 x ] * 1+[2 y ])               ≡⟨⟩
    toℕ 1+[2 (x + y * 1+2x) ]               ≡⟨⟩
    ℕ.suc (2 ℕ.* (toℕ (x + y * 1+2x)))      ≡⟨ cong (ℕ.suc ∘ (2 ℕ.*_)) (toℕ-homo-+ x (y * 1+2x)) ⟩
    ℕ.suc (2 ℕ.* (m ℕ.+ (toℕ (y * 1+2x))))  ≡⟨ cong (ℕ.suc ∘ (2 ℕ.*_) ∘ (m ℕ.+_))
                                                 (aux y 1+2x cnt |y|+1+|x|≤cnt) ⟩
    ℕ.suc (2 ℕ.* (m ℕ.+ (n ℕ.* [1+2x]')))   ≡⟨ cong ℕ.suc $ ℕₚ.*-distribˡ-+ 2 m (n ℕ.* [1+2x]') ⟩
    ℕ.suc (2m ℕ.+ (2 ℕ.* (n ℕ.* [1+2x]')))  ≡⟨ cong (ℕ.suc ∘ (2m ℕ.+_)) (sym (ℕₚ.*-assoc 2 n _)) ⟩
    (ℕ.suc 2m) ℕ.+ 2n ℕ.* [1+2x]'           ≡⟨⟩
    [1+2x]' ℕ.+ 2n ℕ.* [1+2x]'              ≡⟨ cong (ℕ._+ (2n ℕ.* [1+2x]')) $
                                                    sym (ℕₚ.*-identityˡ [1+2x]') ⟩
    1 ℕ.* [1+2x]' ℕ.+ 2n ℕ.* [1+2x]'        ≡⟨ sym (ℕₚ.*-distribʳ-+ [1+2x]' 1 2n) ⟩
    (ℕ.suc 2n) ℕ.* [1+2x]'                  ≡⟨ ℕₚ.*-comm (ℕ.suc 2n) [1+2x]' ⟩
    toℕ 1+[2 x ] ℕ.* toℕ 1+[2 y ]           ∎
    where
    m    = toℕ x;      n       = toℕ y;     2m = 2 ℕ.* m;    2n = 2 ℕ.* n
    1+2x = 1+[2 x ];   [1+2x]' = toℕ 1+2x

    eq : size x ℕ.+ (ℕ.suc (size y)) ≡ size y ℕ.+ (ℕ.suc (size x))
    eq = Of+ℕ-semigroup.x∙yz≈z∙yx (size x) 1 _

    |y|+1+|x|≤cnt = subst (ℕ._≤ cnt) eq |x|+1+|y|≤cnt

toℕ-*-isRawMagmaMorphism : IsRawMagmaMorphism *-rawMagma ℕₚ.*-rawMagma toℕ
toℕ-*-isRawMagmaMorphism = record
  { F-isMagma = isMagma _*_
  ; T-isMagma = ℕₚ.*-isMagma
  ; ⟦⟧-cong   = cong toℕ
  ; ∙-homo    = toℕ-homo-*
  }

toℕ-*-isRawMonoidMorphism : IsRawMonoidMorphism *-1-rawMonoid ℕₚ.*-1-rawMonoid toℕ
toℕ-*-isRawMonoidMorphism = record
  { magma-homo = toℕ-*-isRawMagmaMorphism
  ; ε-homo     = refl
  }

fromℕ-homo-* :  ∀ m n → fromℕ (m ℕ.* n) ≡ fromℕ m * fromℕ n
fromℕ-homo-* m n = begin
  fromℕ (m ℕ.* n)           ≡⟨ cong fromℕ (cong₂ ℕ._*_ m≡aN n≡bN) ⟩
  fromℕ (toℕ a ℕ.* toℕ b)   ≡⟨ cong fromℕ (sym (toℕ-homo-* a b)) ⟩
  fromℕ (toℕ (a * b))       ≡⟨ fromℕ-toℕ (a * b) ⟩
  a * b                     ∎
  where
  a    = fromℕ m;             b    = fromℕ n
  m≡aN = sym (toℕ-fromℕ m);   n≡bN = sym (toℕ-fromℕ n)

------------------------------------------------------------------------
-- Classical algebraic properties for _*_.

-- Mostly proved by using the isomorphism between `ℕ` and `Bin` provided
-- by `toℕ`/`fromℕ`.

module _ where
  open MonoidMorphisms toℕ-*-isRawMonoidMorphism toℕ-injective

  *-assoc :  Associative _*_
  *-assoc = assoc-homo ℕₚ.*-assoc

  *-comm : Commutative _*_
  *-comm = comm-homo ℕₚ.*-comm

  *-identityˡ : LeftIdentity 1B _*_
  *-identityˡ = identityˡ-homo ℕₚ.*-identityˡ

  *-identityʳ : RightIdentity 1B _*_
  *-identityʳ x =  trans (*-comm x 1B) (*-identityˡ x)

  *-identity : Identity 1B _*_
  *-identity = (*-identityˡ , *-identityʳ)

*-zeroˡ : LeftZero zero _*_
*-zeroˡ _ = refl

*-zeroʳ : RightZero zero _*_
*-zeroʳ zero     = refl
*-zeroʳ 2[1+ _ ] = refl
*-zeroʳ 1+[2 _ ] = refl

*-zero : Zero zero _*_
*-zero = *-zeroˡ , *-zeroʳ

*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ a b c = begin
  a * (b + c)                          ≡⟨ sym (fromℕ-toℕ (a * (b + c))) ⟩
  fromℕ (toℕ (a * (b + c)))            ≡⟨ cong fromℕ (toℕ-homo-* a (b + c)) ⟩
  fromℕ (k ℕ.* (toℕ (b + c)))          ≡⟨ cong (fromℕ ∘ (k ℕ.*_)) (toℕ-homo-+ b c) ⟩
  fromℕ (k ℕ.* (m ℕ.+ n))              ≡⟨ cong fromℕ (ℕₚ.*-distribˡ-+ k m n) ⟩
  fromℕ (k ℕ.* m ℕ.+ k ℕ.* n)          ≡⟨ cong fromℕ $ sym $
                                            cong₂ ℕ._+_ (toℕ-homo-* a b) (toℕ-homo-* a c) ⟩
  fromℕ (toℕ (a * b) ℕ.+ toℕ (a * c))  ≡⟨ cong fromℕ (sym (toℕ-homo-+ (a * b) (a * c))) ⟩
  fromℕ (toℕ (a * b + a * c))          ≡⟨ fromℕ-toℕ (a * b + a * c) ⟩
  a * b + a * c                        ∎
  where k = toℕ a;  m = toℕ b;  n = toℕ c

*-distribʳ-+ : _*_ DistributesOverʳ _+_
*-distribʳ-+ = comm+distrˡ⇒distrʳ *-comm *-distribˡ-+

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

------------------------------------------------------------------------
-- Structures

module _ where
  open MonoidMorphisms toℕ-*-isRawMonoidMorphism toℕ-injective

  *-isMagma : IsMagma _*_
  *-isMagma = isMagma _*_

  *-isSemigroup : IsSemigroup _*_
  *-isSemigroup = isSemigroup-homo ℕₚ.*-isSemigroup

  *-1-isMonoid : IsMonoid _*_ 1B
  *-1-isMonoid = isMonoid-homo ℕₚ.*-1-isMonoid

  *-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1B
  *-1-isCommutativeMonoid = isCommutativeMonoid-homo ℕₚ.*-1-isCommutativeMonoid

*-+-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _+_ _*_ zero 1B
*-+-isSemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +-0-isCommutativeMonoid
  ; *-isMonoid            = *-1-isMonoid
  ; distrib               = *-distrib-+
  }

*-+-isSemiring : IsSemiring _+_ _*_ zero 1B
*-+-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = *-+-isSemiringWithoutAnnihilatingZero
  ; zero                              = *-zero
  }

*-+-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ zero 1B
*-+-isCommutativeSemiring = record
  { +-isCommutativeMonoid = +-0-isCommutativeMonoid
  ; *-isCommutativeMonoid = *-1-isCommutativeMonoid
  ; distribʳ              = *-distribʳ-+
  ; zeroˡ                 = *-zeroˡ
  }

------------------------------------------------------------------------
-- Packages

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

*-+-semiring : Semiring 0ℓ 0ℓ
*-+-semiring = record
  { isSemiring = *-+-isSemiring
  }

*-+-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
*-+-commutativeSemiring = record
  { isCommutativeSemiring = *-+-isCommutativeSemiring
  }

------------------------------------------------------------------------
-- Other properties

x*y≡0⇒x≡0∨y≡0 :  ∀ x {y} → x * y ≡ zero → x ≡ zero ⊎ y ≡ zero
x*y≡0⇒x≡0∨y≡0 zero {_}    _ =  inj₁ refl
x*y≡0⇒x≡0∨y≡0 _    {zero} _ =  inj₂ refl

x≢0∧y≢0⇒x*y≢0 :  ∀ {x y} → x ≢ zero → y ≢ zero → x * y ≢ zero
x≢0∧y≢0⇒x*y≢0 {x} {_} x≢0 y≢0 xy≡0  with x*y≡0⇒x≡0∨y≡0 x xy≡0
... | inj₁ x≡0 =  x≢0 x≡0
... | inj₂ y≡0 =  y≢0 y≡0

2B*x≡x+x :  ∀ x → 2B * x ≡ x + x
2B*x≡x+x x = begin
  2B * x            ≡⟨⟩
  (1B + 1B) * x     ≡⟨ *-distribʳ-+ x 1B 1B ⟩
  1B * x + 1B * x   ≡⟨ cong₂ _+_ (*-identityˡ x) (*-identityˡ x) ⟩
  x + x             ∎

1+-* :  ∀ x y → (1B + x) * y ≡ y + x * y
1+-* x y = begin
  (1B + x) * y     ≡⟨ *-distribʳ-+ y 1B x ⟩
  1B * y + x * y   ≡⟨ cong (_+ (x * y)) (*-identityˡ y) ⟩
  y + x * y        ∎

*-1+ :  ∀ x y → y * (1B + x) ≡ y + y * x
*-1+ x y = begin
  y * (1B + x)     ≡⟨ *-distribˡ-+ y 1B x ⟩
  y * 1B + y * x   ≡⟨ cong (_+ (y * x)) (*-identityʳ y) ⟩
  y + y * x        ∎

suc-* :  ∀ x y → (suc x) * y ≡ y + x * y
suc-* x y = begin
  (suc x) * y     ≡⟨ cong (_* y) (suc≗1+ x) ⟩
  (1B + x) * y    ≡⟨ 1+-* x y ⟩
  y + x * y       ∎

*-suc :  ∀ x y → x * (suc y) ≡ x + x * y
*-suc x y = begin
  x * (suc y)    ≡⟨ cong (x *_) (suc≗1+ y) ⟩
  x * (1B + y)   ≡⟨ *-1+ y x ⟩
  x + x * y      ∎

double≗2B* :  double ≗ 2B *_
double≗2B* x =  toℕ-injective $ begin
  toℕ (double x)  ≡⟨ toℕ-double x ⟩
  2 ℕ.* (toℕ x)   ≡⟨ sym (toℕ-homo-* 2B x) ⟩
  toℕ (2B * x)    ∎

double-*-assoc :  ∀ x y → (double x) * y ≡ double (x * y)
double-*-assoc x y = begin
  (double x) * y     ≡⟨ cong (_* y) (double≗2B* x) ⟩
  (2B * x) * y       ≡⟨ *-assoc 2B x y ⟩
  2B * (x * y)       ≡⟨ sym (double≗2B* (x * y)) ⟩
  double (x * y)     ∎

double[x]≡x+x :  ∀ x → double x ≡ x + x
double[x]≡x+x x =  trans (double≗2B* x) (2B*x≡x+x x)

double-distrib-+ : ∀ x y → double (x + y) ≡ double x + double y
double-distrib-+ x y = begin
  double (x + y)         ≡⟨ double≗2B* (x + y) ⟩
  2B * (x + y)           ≡⟨ *-distribˡ-+ 2B x y ⟩
  (2B * x) + (2B * y)    ≡⟨ cong₂ _+_ eq eq' ⟩
  double x + double y    ∎
  where eq = sym (double≗2B* x);   eq' = sym (double≗2B* y)
