------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to addition, multiplication and ordering of
-- binary represented natural numbers.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bin.Properties where

open import Algebra
open import Algebra.Morphism
import Algebra.Morphism.RawMonoid as MonoidMorphisms
open import Algebra.FunctionProperties.Consequences.Propositional
open import Data.Bin.Base
open import Data.Nat as ℕ using (ℕ; z≤n; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Solver
open import Data.Product using (_,_; proj₁; proj₂; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; _$_; id; const)
open import Function.Definitions using (Injective)
open import Function.Definitions.Core2 using (Surjective)
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Base.Triple as InequalityReasoning
open import Relation.Nullary using (¬_; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation using (contradiction)
open import Algebra.FunctionProperties {A = Bin} _≡_
open import Algebra.Structures {A = Bin} _≡_
import Algebra.Properties.CommutativeSemigroup ℕₚ.+-semigroup ℕₚ.+-comm as Of+ℕ
import Relation.Binary.Construct.StrictToNonStrict _≡_ _<_ as ToNonstrict
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

2[1+_]-injective : Injective {A = Bin} {B = Bin} _≡_ _≡_ 2[1+_]
2[1+_]-injective refl = refl

1+[2_]-injective : Injective {A = Bin} {B = Bin} _≡_ _≡_ 1+[2_]
1+[2_]-injective refl = refl

_≟_ :  Decidable {A = Bin} _≡_
zero     ≟ zero     =  yes refl
zero     ≟ 2[1+ _ ] =  no λ()
zero     ≟ 1+[2 _ ] =  no λ()
2[1+ _ ] ≟ zero     =  no λ()
2[1+ x ] ≟ 2[1+ y ] =  Dec.map′ (cong 2[1+_]) 2[1+_]-injective (x ≟ y)
2[1+ _ ] ≟ 1+[2 _ ] =  no λ()
1+[2 _ ] ≟ zero     =  no λ()
1+[2 _ ] ≟ 2[1+ _ ] =  no λ()
1+[2 x ] ≟ 1+[2 y ] =  Dec.map′ (cong 1+[2_]) 1+[2_]-injective (x ≟ y)

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
  where open ≡-Reasoning;  2x = double x

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
  where open ≡-Reasoning

toℕ-injective :  Injective {A = Bin} {B = ℕ} _≡_ _≡_ toℕ
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

toℕ-surjective :  Surjective {B = ℕ} _≡_ toℕ
toℕ-surjective n =  (fromℕ n , sym (toℕ-fromℕ n))

fromℕ-toℕ :  fromℕ ∘ toℕ ≗ id
fromℕ-toℕ =  toℕ-injective ∘ toℕ-fromℕ ∘ toℕ

fromℕ-pred : ∀ n → fromℕ (ℕ.pred n) ≡ pred (fromℕ n)
fromℕ-pred n = begin
  fromℕ (ℕ.pred n)        ≡⟨ cong (fromℕ ∘ ℕ.pred) (sym (toℕ-fromℕ n)) ⟩
  fromℕ (ℕ.pred (toℕ x))  ≡⟨ cong fromℕ (sym (toℕ-pred x)) ⟩
  fromℕ (toℕ (pred x))    ≡⟨ fromℕ-toℕ (pred x) ⟩
  pred x                  ≡⟨ refl ⟩
  pred (fromℕ n)          ∎
  where open ≡-Reasoning;  x = fromℕ n

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
  where open ≡-Reasoning

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
  where open ≡-Reasoning;  m = toℕ x; n = toℕ y

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
  where open ≡-Reasoning;  m = toℕ x;  n = toℕ y

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
  where open ≡-Reasoning;  m = toℕ x;  n = toℕ y

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
  where open ≡-Reasoning;  a = fromℕ m;  b = fromℕ n

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
toℕ-homo-* x y =  aux x y (size x ℕ.+ size y) ℕₚ.≤-refl
  where
  aux :  (x y : Bin) → (cnt : ℕ) → (size x ℕ.+ size y ℕ.≤ cnt) →  toℕ (x * y) ≡ toℕ x ℕ.* toℕ y
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
    open ≡-Reasoning;  m = toℕ x;  n = toℕ y;  xy = x * y

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
    open ≡-Reasoning;   m = toℕ x;  n = toℕ y;  1+m = ℕ.suc m;  2[1+m] = 2 ℕ.* (ℕ.suc m)

    eq : size x ℕ.+ (ℕ.suc (size y)) ≡ size y ℕ.+ (ℕ.suc (size x))
    eq = Of+ℕ.x∙yz≈z∙yx (size x) 1 _

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
    open ≡-Reasoning
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
    open ≡-Reasoning
    m    = toℕ x;      n       = toℕ y;     2m = 2 ℕ.* m;    2n = 2 ℕ.* n
    1+2x = 1+[2 x ];   [1+2x]' = toℕ 1+2x

    eq : size x ℕ.+ (ℕ.suc (size y)) ≡ size y ℕ.+ (ℕ.suc (size x))
    eq = Of+ℕ.x∙yz≈z∙yx (size x) 1 _

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
  open ≡-Reasoning
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
  where open ≡-Reasoning;  k = toℕ a;  m = toℕ b;  n = toℕ c

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
  where open ≡-Reasoning

1+-* :  ∀ x y → (1B + x) * y ≡ y + x * y
1+-* x y = begin
  (1B + x) * y     ≡⟨ *-distribʳ-+ y 1B x ⟩
  1B * y + x * y   ≡⟨ cong (_+ (x * y)) (*-identityˡ y) ⟩
  y + x * y        ∎
  where open ≡-Reasoning

*-1+ :  ∀ x y → y * (1B + x) ≡ y + y * x
*-1+ x y = begin
  y * (1B + x)     ≡⟨ *-distribˡ-+ y 1B x ⟩
  y * 1B + y * x   ≡⟨ cong (_+ (y * x)) (*-identityʳ y) ⟩
  y + y * x        ∎
  where open ≡-Reasoning

suc-* :  ∀ x y → (suc x) * y ≡ y + x * y
suc-* x y = begin
  (suc x) * y     ≡⟨ cong (_* y) (suc≗1+ x) ⟩
  (1B + x) * y    ≡⟨ 1+-* x y ⟩
  y + x * y       ∎
  where open ≡-Reasoning

*-suc :  ∀ x y → x * (suc y) ≡ x + x * y
*-suc x y = begin
  x * (suc y)    ≡⟨ cong (x *_) (suc≗1+ y) ⟩
  x * (1B + y)   ≡⟨ *-1+ y x ⟩
  x + x * y      ∎
  where open ≡-Reasoning

double≗2B* :  double ≗ 2B *_
double≗2B* x =  toℕ-injective $ begin
  toℕ (double x)  ≡⟨ toℕ-double x ⟩
  2 ℕ.* (toℕ x)   ≡⟨ sym (toℕ-homo-* 2B x) ⟩
  toℕ (2B * x)    ∎
  where open ≡-Reasoning

double-*-assoc :  ∀ x y → (double x) * y ≡ double (x * y)
double-*-assoc x y = begin
  (double x) * y     ≡⟨ cong (_* y) (double≗2B* x) ⟩
  (2B * x) * y       ≡⟨ *-assoc 2B x y ⟩
  2B * (x * y)       ≡⟨ sym (double≗2B* (x * y)) ⟩
  double (x * y)     ∎
  where open ≡-Reasoning

double[x]≡x+x :  ∀ x → double x ≡ x + x
double[x]≡x+x x =  trans (double≗2B* x) (2B*x≡x+x x)

double-distrib-+ : ∀ x y → double (x + y) ≡ double x + double y
double-distrib-+ x y = begin
  double (x + y)         ≡⟨ double≗2B* (x + y) ⟩
  2B * (x + y)           ≡⟨ *-distribˡ-+ 2B x y ⟩
  (2B * x) + (2B * y)    ≡⟨ cong₂ _+_ eq eq' ⟩
  double x + double y    ∎
  where open ≡-Reasoning;  eq = sym (double≗2B* x);  eq' = sym (double≗2B* y)


------------------------------------------------------------------------
-- Properties of ordering

x≮0 : ∀ {x} → x ≮ zero    -- to use instead of λ()
x≮0 ()

1+[2x]<2[1+x] :  ∀ x → 1+[2 x ] < 2[1+ x ]
1+[2x]<2[1+x] x =  odd<even (inj₂ refl)

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (even<even x<x) =  <-irrefl refl x<x
<-irrefl refl (odd<odd x<x)   =  <-irrefl refl x<x

<⇒≢ :  _<_ ⇒ _≢_
<⇒≢ x<x refl =  <-irrefl refl x<x

>⇒≢ :  _>_ ⇒ _≢_
>⇒≢ y<x =  ≢-sym (<⇒≢ y<x)

≡⇒≮ :  _≡_ ⇒ _≮_
≡⇒≮ x≡y x<y =  <⇒≢ x<y x≡y

≡⇒≯ :  _≡_ ⇒ _≯_
≡⇒≯ x≡y x>y =  >⇒≢ x>y x≡y

<-trans : Transitive _<_
<-trans {zero}          {_}      {2[1+ _ ]} _  _  =  0<even
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
  ℕ.suc (ℕ.suc (2 ℕ.* xN))    ≡⟨⟩
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
  open ≡-Reasoning
  x       = fromℕ m;      y       = fromℕ n
  toℕ-x≡m = toℕ-fromℕ m;  toℕ-y≡n = toℕ-fromℕ n

  aux : Tri (x < y) (x ≡ y) (x > y) → x < y
  aux (tri< x<y _   _) =  x<y
  aux (tri≈ _   x≡y _) =  contradiction m≡n (ℕₚ.<⇒≢ m<n)
    where
    open ≡-Reasoning
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

<⇒<ℕ :  ∀ {x y} → x < y → x <ℕ y
<⇒<ℕ x<y =  toℕ-mono-< x<y

<ℕ⇒< :  ∀ {x y} → x <ℕ y → x < y
<ℕ⇒< {x} {y} xN<yN =  subst₂ _<_ (fromℕ-toℕ x) (fromℕ-toℕ y) xN'<yN'
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
≤-trans = ToNonstrict.trans isEquivalence (resp₂ _<_) <-trans

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym = ToNonstrict.antisym isEquivalence <-trans <-irrefl

≤-total : Total _≤_
≤-total x y  with <-cmp x y
... | tri< le _  _  =  inj₁ (<⇒≤ le)
... | tri≈ _  eq _  =  inj₁ (≤-reflexive eq)
... | tri> _  _  gt =  inj₂ (<⇒≤ gt)

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

private
  module ≤-Reasoning = InequalityReasoning {A = Bin} {_≈_ = _≡_} ≤-isPreorder
                                 <-trans (resp₂ _<_) <⇒≤ <-≤-trans ≤-<-trans

------------------------------------------------------------------------------
-- Several monotonicity proofs for _+_, suc
------------------------------------------------------------------------------

+-mono-≤ :  _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' =  begin
  x + y                 ≡⟨ sym $ cong₂ _+_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m + fromℕ n     ≡⟨ sym (fromℕ-homo-+ m n) ⟩
  fromℕ (m ℕ.+ n)       ≤⟨ fromℕ-mono-≤ (ℕₚ.+-mono-≤ m≤m' n≤n') ⟩
  fromℕ (m' ℕ.+ n')     ≡⟨ fromℕ-homo-+ m' n' ⟩
  fromℕ m' + fromℕ n'   ≡⟨ cong₂ _+_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' + y'               ∎
  where
  open ≤-Reasoning
  m    = toℕ x;             m'   = toℕ x'
  n    = toℕ y;             n'   = toℕ y'
  m≤m' = toℕ-mono-≤ x≤x';   n≤n' = toℕ-mono-≤ y≤y'

+-monoˡ-≤ :  ∀ x → (_+ x) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ x y≤z =  +-mono-≤ y≤z (≤-refl {x})

+-monoʳ-≤ :  ∀ x → (x +_) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ x y≤z =  +-mono-≤ (≤-refl {x}) y≤z

+-mono-<-≤ :  _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
+-mono-<-≤ {x} {x'} {y} {y'} x<x' y≤y' =  begin-strict
  x + y                  ≡⟨ sym $ cong₂ _+_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m + fromℕ n      ≡⟨ sym (fromℕ-homo-+ m n) ⟩
  fromℕ (m ℕ.+ n)        <⟨ fromℕ-mono-< (ℕₚ.+-mono-<-≤ m<m' n≤n') ⟩
  fromℕ (m' ℕ.+ n')      ≡⟨ fromℕ-homo-+ m' n' ⟩
  fromℕ m' + fromℕ n'    ≡⟨ cong₂ _+_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' + y'                ∎
  where
  open ≤-Reasoning
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
  suc x     ≡⟨ suc≗1+ x ⟩
  1B + x    ≤⟨ +-monoʳ-≤ 1B x≤y ⟩
  1B + y    ≡⟨ sym (suc≗1+ y) ⟩
  suc y     ∎
  where open ≤-Reasoning

------------------------------------------------------------------------------
-- Some more properties for _<_, _≤_.
------------------------------------------------------------------------------

x≤y+x :  ∀ (x y) → x ≤ y + x
x≤y+x x y =  begin
  x          ≡⟨ sym (+-identityˡ x) ⟩
  zero + x   ≤⟨ +-monoˡ-≤ x (0≤x y) ⟩
  y + x      ∎
  where open ≤-Reasoning

x≤x+y :  ∀ (x y) → x ≤ x + y
x≤x+y x y =  begin
  x        ≤⟨ x≤y+x x y ⟩
  y + x    ≡⟨ +-comm y x ⟩
  x + y    ∎
  where open ≤-Reasoning

x<1+x :  ∀ x → x < 1B + x
x<1+x x = begin-strict
  x                 ≡⟨ sym (fromℕ-toℕ x) ⟩
  fromℕ n           <⟨ fromℕ-mono-< (ℕₚ.n<1+n {n}) ⟩
  fromℕ (ℕ.suc n)   ≡⟨ fromℕ-homo-+ 1 n ⟩
  1B + fromℕ n      ≡⟨ cong (1B +_) (fromℕ-toℕ x) ⟩
  1B + x            ∎
  where open ≤-Reasoning;  n = toℕ x

x<x+1 :  ∀ x → x < x + 1B
x<x+1 x =  begin-strict
  x        <⟨ x<1+x x ⟩
  1B + x   ≡⟨ +-comm 1B x ⟩
  x + 1B   ∎
  where open ≤-Reasoning

x<suc[x] :  ∀ x → x < suc x
x<suc[x] x =  begin-strict
  x        <⟨ x<1+x x ⟩
  1B + x   ≡⟨ sym (suc≗1+ x) ⟩
  suc x    ∎
  where open ≤-Reasoning

x≤suc[x] :  ∀ x → x ≤ suc x
x≤suc[x] x =  <⇒≤ {x} {suc x} (x<suc[x] x)

x≢suc[x] :  ∀ x → x ≢ suc x
x≢suc[x] =  <⇒≢ ∘ x<suc[x]

pred[x]<x :  ∀ {x} → x ≢ zero → pred x < x
pred[x]<x {x} x≢0 =  begin-strict
  pred x          <⟨ x<suc[x] (pred x) ⟩
  suc (pred x)    ≡⟨ suc-pred x≢0 ⟩
  x               ∎
  where open ≤-Reasoning

------------------------------------------------------------------------------
-- Monotonicity proofs for _*_, double.
------------------------------------------------------------------------------

*-mono-≤ :  _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
*-mono-≤ {x} {x'} {y} {y'} x≤x' y≤y' =  begin
  x * y                  ≡⟨ sym $ cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m * fromℕ n      ≡⟨ sym (fromℕ-homo-* m n) ⟩
  fromℕ (m ℕ.* n)        ≤⟨ fromℕ-mono-≤ (ℕₚ.*-mono-≤ m≤m' n≤n') ⟩
  fromℕ (m' ℕ.* n')      ≡⟨ fromℕ-homo-* m' n' ⟩
  fromℕ m' * fromℕ n'    ≡⟨ cong₂ _*_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' * y'                ∎
  where
  open ≤-Reasoning
  m    = toℕ x;              m'   = toℕ x'
  n    = toℕ y;              n'   = toℕ y'
  m≤m' = toℕ-mono-≤ x≤x';    n≤n' = toℕ-mono-≤ y≤y'

*-monoʳ-≤ :  ∀ x → (x *_) Preserves _≤_ ⟶ _≤_
*-monoʳ-≤ x y≤y' =  *-mono-≤ (≤-refl {x}) y≤y'

*-monoˡ-≤ :  ∀ x → (_* x) Preserves _≤_ ⟶ _≤_
*-monoˡ-≤ x y≤y' =  *-mono-≤ y≤y' (≤-refl {x})

*-mono-< :  _*_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
*-mono-< {x} {x'} {y} {y'} x<x' y<y' =  begin-strict
  x * y                  ≡⟨ sym $ cong₂ _*_ (fromℕ-toℕ x) (fromℕ-toℕ y) ⟩
  fromℕ m * fromℕ n      ≡⟨ sym (fromℕ-homo-* m n) ⟩
  fromℕ (m ℕ.* n)        <⟨ fromℕ-mono-< (ℕₚ.*-mono-< m<m' n<n') ⟩
  fromℕ (m' ℕ.* n')      ≡⟨ fromℕ-homo-* m' n' ⟩
  fromℕ m' * fromℕ n'    ≡⟨ cong₂ _*_ (fromℕ-toℕ x') (fromℕ-toℕ y') ⟩
  x' * y'                ∎
  where
  open ≤-Reasoning
  m    = toℕ x;              m'   = toℕ x'
  n    = toℕ y;              n'   = toℕ y'
  m<m' = toℕ-mono-< x<x';    n<n' = toℕ-mono-< y<y'

*-monoʳ-< :  ∀ x → ((suc x) *_) Preserves _<_ ⟶ _<_
*-monoʳ-< x {y} {z} y<z =  begin-strict
  (suc x) * y      ≡⟨ suc-* x y ⟩
  y + xy           <⟨ +-mono-<-≤ y<z xy≤xz ⟩
  z + xz           ≡⟨ sym (suc-* x z) ⟩
  (suc x) * z      ∎
  where
  open ≤-Reasoning
  xy = x * y;  xz = x * z;  xy≤xz = *-monoʳ-≤ x (<⇒≤ {y} {z} y<z)

*-monoˡ-< :  ∀ x → (_* (suc x)) Preserves _<_ ⟶ _<_
*-monoˡ-< x {y} {z} y<z = begin-strict
  y * (suc x)   ≡⟨ *-comm y (suc x) ⟩
  (suc x) * y   <⟨ *-monoʳ-< x y<z ⟩
  (suc x) * z   ≡⟨ *-comm (suc x) z ⟩
  z * (suc x)   ∎
  where open ≤-Reasoning

double-mono-≤ :  double Preserves _≤_ ⟶ _≤_
double-mono-≤ {x} {y} x≤y =  begin
  double x   ≡⟨ double≗2B* x ⟩
  2B * x     ≤⟨ *-monoʳ-≤ 2B x≤y ⟩
  2B * y     ≡⟨ sym (double≗2B* y) ⟩
  double y   ∎
  where open ≤-Reasoning

double-mono-< :  double Preserves _<_ ⟶ _<_
double-mono-< {x} {y} x<y =  begin-strict
  double x   ≡⟨ double≗2B* x ⟩
  2B * x     <⟨ *-monoʳ-< 1B x<y ⟩
  2B * y     ≡⟨ sym (double≗2B* y) ⟩
  double y   ∎
  where open ≤-Reasoning

double-back-mono-≤ :  ∀ {x y} → double x ≤ double y → x ≤ y
double-back-mono-≤ {x} {y} 2x≤2y  with <-cmp x y
... | tri< x<y _   _   =  <⇒≤ x<y
... | tri≈ _   x≡y _   =  ≤-reflexive x≡y
... | tri> _   _   x>y =  contradiction 2x≤2y (<⇒≱ 2x>2y)  where 2x>2y = double-mono-< x>y

double-back-mono-< :  ∀ {x y} → double x < double y → x < y
double-back-mono-< {x} {y} 2x<2y  with <-cmp x y
... | tri< x<y _    _   =  x<y
... | tri≈ _   refl _   =  contradiction 2x<2y (<-irrefl refl)
... | tri> _   _    x>y =  contradiction 2x>2y (<⇒≯ 2x<2y)  where 2x>2y = double-mono-< x>y

------------------------------------------------------------------------------
-- Some more properties for _<_, _≤_.
------------------------------------------------------------------------------

x<double[x] :  ∀ x → x ≢ zero → x < double x
x<double[x] x x≢0 =  begin-strict
  x                 ≡⟨ sym (suc-pred x≢0) ⟩
  suc px            ≡⟨ sym (*-identityʳ (suc px)) ⟩
  suc px * 1B       <⟨ *-monoʳ-< px (x<1+x 1B) ⟩
  suc px * 2B       ≡⟨ *-comm (suc px) 2B ⟩
  2B * suc px       ≡⟨ sym (double≗2B* (suc px)) ⟩
  double (suc px)   ≡⟨ cong double (suc-pred x≢0) ⟩
  double x          ∎
  where open ≤-Reasoning;  px = pred x

suc[x]≤y⇒x<y :  ∀ {x y} → suc x ≤ y → x < y
suc[x]≤y⇒x<y {x} {_} (inj₁ sx<y) =  <-trans (x<suc[x] x) sx<y
suc[x]≤y⇒x<y {x} {_} (inj₂ sx≡y) =  subst (x <_) sx≡y (x<suc[x] x)

x<y⇒suc[x]≤y :  ∀ {x y} → x < y → suc x ≤ y
x<y⇒suc[x]≤y {x} {y} x<y =  begin
  suc x                  ≡⟨ sym (fromℕ-toℕ (suc x)) ⟩
  fromℕ (toℕ (suc x))    ≡⟨ cong fromℕ (toℕ-suc x) ⟩
  fromℕ (ℕ.suc m)        ≤⟨ fromℕ-mono-≤ 1+m≤n ⟩
  fromℕ n                ≡⟨ fromℕ-toℕ y ⟩
  y                      ∎
  where open ≤-Reasoning;  m = toℕ x;  n = toℕ y;  1+m≤n = toℕ-mono-< x<y

suc[x]≤double[x] :  ∀ x → x ≢ zero → suc x ≤ double x
suc[x]≤double[x] x =  x<y⇒suc[x]≤y {x} {double x} ∘ x<double[x] x

x≤suc[y]*x :  ∀ (x y) → x ≤ (suc y) * x
x≤suc[y]*x x y =  begin
  x             ≤⟨ x≤x+y x (y * x) ⟩
  x + y * x     ≡⟨ sym (suc-* y x) ⟩
  (suc y) * x   ∎
  where open ≤-Reasoning

x≤double[x] :  ∀ x → x ≤ double x
x≤double[x] x =  begin
  x         ≤⟨ x≤x+y x x ⟩
  x + x     ≡⟨ sym (double[x]≡x+x x) ⟩
  double x  ∎
  where open ≤-Reasoning

suc[x]<2[1+x] :  ∀ x → suc x < 2[1+ x ]
suc[x]<2[1+x] x =  begin-strict
  suc x           <⟨ x<double[x] (suc x) suc≢0  ⟩
  double (suc x)  ≡⟨ sym (2[1+_]-as∘ x) ⟩
  2[1+ x ]        ∎
  where open ≤-Reasoning

x<2[1+x] :  ∀ x → x < 2[1+ x ]
x<2[1+x] x =  <-trans (x<suc[x] x) (suc[x]<2[1+x] x)

x<1+[2x] :  ∀ x → x < 1+[2 x ]
x<1+[2x] x =  begin-strict
  x               <⟨ x<suc[x] x ⟩
  suc x           ≤⟨ suc-mono-≤ (x≤double[x] x) ⟩
  suc (double x)  ≡⟨ sym (1+[2_]-as∘ x) ⟩
  1+[2 x ]        ∎
  where open ≤-Reasoning

double[x]<1+[2x] :  ∀ x → double x < 1+[2 x ]
double[x]<1+[2x] x =  begin-strict
  double x         <⟨ x<suc[x] (double x) ⟩
  suc (double x)   ≡⟨ sym (1+[2_]-as∘ x) ⟩
  1+[2 x ]         ∎
  where open ≤-Reasoning

pred-mono-≤ :  pred Preserves _≤_ ⟶ _≤_
pred-mono-≤ {x} {y} x≤y =  begin
  pred x             ≡⟨ cong pred (sym (fromℕ-toℕ x)) ⟩
  pred (fromℕ m)     ≡⟨ sym (fromℕ-pred m) ⟩
  fromℕ (ℕ.pred m)   ≤⟨ fromℕ-mono-≤ (ℕₚ.pred-mono m≤n) ⟩
  fromℕ (ℕ.pred n)   ≡⟨ fromℕ-pred n ⟩
  pred (fromℕ n)     ≡⟨ cong pred (fromℕ-toℕ y) ⟩
  pred y             ∎
  where
  open ≤-Reasoning;  m = toℕ x;  n = toℕ y;  m≤n = toℕ-mono-≤ x≤y

x<1⇒x≡0 :  ∀ {x} → x < 1B → x ≡ zero
x<1⇒x≡0 {x} x<1 =  x≤0⇒x≡0 $ begin
  x             ≡⟨ sym (pred-suc x) ⟩
  pred (suc x)  ≤⟨ pred-mono-≤ suc[x]≤1 ⟩
  pred 1B       ≡⟨ refl ⟩
  zero          ∎
  where open ≤-Reasoning;  suc[x]≤1 = x<y⇒suc[x]≤y {x} {1B} x<1


------------------------------------------------------------------------------
-- StrictTotalOrder and DecTotalOrder instances for Bin.
------------------------------------------------------------------------------

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence =  isEquivalence
  ; trans         =  <-trans
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
