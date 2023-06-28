------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about parities
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Parity.Properties where

open import Algebra.Bundles
open import Data.Empty
open import Data.Nat.Base as ℕ using (zero; suc; parity)
open import Data.Parity.Base as ℙ using (Parity; 0ℙ; 1ℙ; _⁻¹; toSign; fromSign)
open import Data.Product using (_,_)
open import Data.Sign.Base as 𝕊
open import Function.Base using (_$_; id)
open import Function.Definitions using (Injective; Surjective)
open import Level using (0ℓ)
open import Relation.Binary
  using (Decidable; DecidableEquality; Setoid; DecSetoid; IsDecEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; module ≡-Reasoning
        ; setoid; isEquivalence; decSetoid; isDecEquivalence)
open import Relation.Nullary using (yes; no)

open import Algebra.Structures {A = Parity} _≡_
open import Algebra.Definitions {A = Parity} _≡_
open import Algebra.Consequences.Propositional
  using (selfInverse⇒involutive; selfInverse⇒injective; comm+distrˡ⇒distrʳ)
open import Algebra.Morphism.Structures

------------------------------------------------------------------------
-- Equality

infix 4 _≟_

_≟_ : DecidableEquality Parity
1ℙ ≟ 1ℙ = yes refl
1ℙ ≟ 0ℙ = no λ()
0ℙ ≟ 1ℙ = no λ()
0ℙ ≟ 0ℙ = yes refl

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid Parity

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_

≡-isDecEquivalence : IsDecEquivalence _≡_
≡-isDecEquivalence = isDecEquivalence _≟_

------------------------------------------------------------------------
-- _⁻¹

-- Algebraic properties of _⁻¹

⁻¹-selfInverse : SelfInverse _⁻¹
⁻¹-selfInverse { 1ℙ } { 0ℙ } refl = refl
⁻¹-selfInverse { 0ℙ } { 1ℙ } refl = refl

⁻¹-involutive : Involutive _⁻¹
⁻¹-involutive = selfInverse⇒involutive ⁻¹-selfInverse

⁻¹-injective : Injective _≡_ _≡_ _⁻¹
⁻¹-injective = selfInverse⇒injective ⁻¹-selfInverse

------------------------------------------------------------------------
-- other properties of _⁻¹

p≢p⁻¹ : ∀ p → p ≢ p ⁻¹
p≢p⁻¹ 1ℙ ()
p≢p⁻¹ 0ℙ ()

------------------------------------------------------------------------
-- ⁻¹ and _+_

p+p⁻¹≡1ℙ : ∀ p → p ℙ.+ p ⁻¹ ≡ 1ℙ
p+p⁻¹≡1ℙ 0ℙ = refl
p+p⁻¹≡1ℙ 1ℙ = refl

p⁻¹+p≡1ℙ : ∀ p → p ⁻¹ ℙ.+ p ≡ 1ℙ
p⁻¹+p≡1ℙ 0ℙ = refl
p⁻¹+p≡1ℙ 1ℙ = refl

------------------------------------------------------------------------
-- ⁻¹ and _*_

p*p⁻¹≡0ℙ : ∀ p → p ℙ.* p ⁻¹ ≡ 0ℙ
p*p⁻¹≡0ℙ 0ℙ = refl
p*p⁻¹≡0ℙ 1ℙ = refl

p⁻¹*p≡0ℙ : ∀ p → p ⁻¹ ℙ.* p ≡ 0ℙ
p⁻¹*p≡0ℙ 0ℙ = refl
p⁻¹*p≡0ℙ 1ℙ = refl

------------------------------------------------------------------------
-- _+_

-- Algebraic properties of _+_

p+p≡0ℙ : ∀ p → p ℙ.+ p ≡ 0ℙ
p+p≡0ℙ 0ℙ = refl
p+p≡0ℙ 1ℙ = refl

+-identityˡ : LeftIdentity 0ℙ ℙ._+_
+-identityˡ _ = refl

+-identityʳ : RightIdentity 0ℙ ℙ._+_
+-identityʳ 1ℙ = refl
+-identityʳ 0ℙ = refl

+-identity : Identity 0ℙ ℙ._+_
+-identity = +-identityˡ  , +-identityʳ

+-comm : Commutative ℙ._+_
+-comm 0ℙ 0ℙ = refl
+-comm 0ℙ 1ℙ = refl
+-comm 1ℙ 0ℙ = refl
+-comm 1ℙ 1ℙ = refl

+-assoc : Associative ℙ._+_
+-assoc 0ℙ 0ℙ _ = refl
+-assoc 0ℙ 1ℙ _ = refl
+-assoc 1ℙ 0ℙ _ = refl
+-assoc 1ℙ 1ℙ 0ℙ = refl
+-assoc 1ℙ 1ℙ 1ℙ = refl

+-cancelʳ-≡ : RightCancellative ℙ._+_
+-cancelʳ-≡ _ 1ℙ 1ℙ _  = refl
+-cancelʳ-≡ _ 1ℙ 0ℙ eq = ⊥-elim (p≢p⁻¹ _ $ sym eq)
+-cancelʳ-≡ _ 0ℙ 1ℙ eq = ⊥-elim (p≢p⁻¹ _ eq)
+-cancelʳ-≡ _ 0ℙ 0ℙ _  = refl

+-cancelˡ-≡ : LeftCancellative ℙ._+_
+-cancelˡ-≡ 1ℙ _ _ eq = ⁻¹-injective eq
+-cancelˡ-≡ 0ℙ _ _ eq = eq

+-cancel-≡ : Cancellative ℙ._+_
+-cancel-≡ = +-cancelˡ-≡ , +-cancelʳ-≡

+-inverse : Inverse 0ℙ id ℙ._+_
+-inverse = p+p≡0ℙ , p+p≡0ℙ

------------------------------------------------------------------------
-- Bundles

+-isMagma : IsMagma ℙ._+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ ℙ._+_
  }

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-isSemigroup : IsSemigroup ℙ._+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-isCommutativeSemigroup : IsCommutativeSemigroup ℙ._+_
+-isCommutativeSemigroup = record
  { isSemigroup = +-isSemigroup
  ; comm = +-comm
  }

+-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
+-commutativeSemigroup = record
  { isCommutativeSemigroup = +-isCommutativeSemigroup
  }

+-0-isMonoid : IsMonoid ℙ._+_ 0ℙ
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid ℙ._+_ 0ℙ
+-0-isCommutativeMonoid = record
   { isMonoid = +-0-isMonoid
   ; comm = +-comm
   }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-isGroup : IsGroup ℙ._+_ 0ℙ id
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse = +-inverse
  ; ⁻¹-cong = id
  }

+-0-group : Group 0ℓ 0ℓ
+-0-group = record
  { isGroup = +-0-isGroup
  }

+-0-isAbelianGroup : IsAbelianGroup ℙ._+_ 0ℙ id
+-0-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm = +-comm
  }

+-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-0-isAbelianGroup
  }

------------------------------------------------------------------------
-- _*_

-- Algebraic properties of _*_

*-idem : Idempotent ℙ._*_
*-idem 0ℙ = refl
*-idem 1ℙ = refl

*-comm : Commutative ℙ._*_
*-comm 0ℙ 0ℙ = refl
*-comm 0ℙ 1ℙ = refl
*-comm 1ℙ 0ℙ = refl
*-comm 1ℙ 1ℙ = refl

*-assoc : Associative ℙ._*_
*-assoc 0ℙ 0ℙ _ = refl
*-assoc 0ℙ 1ℙ _ = refl
*-assoc 1ℙ 0ℙ _ = refl
*-assoc 1ℙ 1ℙ 0ℙ = refl
*-assoc 1ℙ 1ℙ 1ℙ = refl

*-distribˡ-+ : ℙ._*_ DistributesOverˡ ℙ._+_
*-distribˡ-+ 0ℙ q r = refl
*-distribˡ-+ 1ℙ 0ℙ 0ℙ = refl
*-distribˡ-+ 1ℙ 0ℙ 1ℙ = refl
*-distribˡ-+ 1ℙ 1ℙ 0ℙ = refl
*-distribˡ-+ 1ℙ 1ℙ 1ℙ = refl

*-distribʳ-+ : ℙ._*_ DistributesOverʳ ℙ._+_
*-distribʳ-+ = comm+distrˡ⇒distrʳ *-comm *-distribˡ-+

*-distrib-+ : ℙ._*_ DistributesOver ℙ._+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-zeroˡ : LeftZero 0ℙ ℙ._*_
*-zeroˡ p = refl

*-zeroʳ : RightZero 0ℙ ℙ._*_
*-zeroʳ p = *-comm p 0ℙ

*-zero : Zero 0ℙ ℙ._*_
*-zero = *-zeroˡ , *-zeroʳ

*-identityˡ : LeftIdentity 1ℙ ℙ._*_
*-identityˡ _ = refl

*-identityʳ : RightIdentity 1ℙ ℙ._*_
*-identityʳ 1ℙ = refl
*-identityʳ 0ℙ = refl

*-identity : Identity 1ℙ ℙ._*_
*-identity = *-identityˡ  , *-identityʳ

------------------------------------------------------------------------
-- Structures and Bundles

*-isMagma : IsMagma ℙ._*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ ℙ._*_
  }

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-isSemigroup : IsSemigroup ℙ._*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-isCommutativeSemigroup : IsCommutativeSemigroup ℙ._*_
*-isCommutativeSemigroup = record
  { isSemigroup = *-isSemigroup
  ; comm = *-comm
  }

*-commutativeSemigroup : CommutativeSemigroup 0ℓ 0ℓ
*-commutativeSemigroup = record
  { isCommutativeSemigroup = *-isCommutativeSemigroup
  }

*-1-isMonoid : IsMonoid ℙ._*_ 1ℙ
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid ℙ._*_ 1ℙ
*-1-isCommutativeMonoid = record
   { isMonoid = *-1-isMonoid
   ; comm = *-comm
   }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

+-*-isSemiring : IsSemiring ℙ._+_ ℙ._*_ 0ℙ 1ℙ
+-*-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = record
    { +-isCommutativeMonoid = +-0-isCommutativeMonoid
    ; *-cong = cong₂ ℙ._*_
    ; *-assoc = *-assoc
    ; *-identity = *-identity
    ; distrib = *-distrib-+
    }
  ; zero = *-zero
  }

+-*-semiring : Semiring 0ℓ 0ℓ
+-*-semiring = record
  { isSemiring = +-*-isSemiring
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring ℙ._+_ ℙ._*_ 0ℙ 1ℙ
+-*-isCommutativeSemiring = record
  { isSemiring = +-*-isSemiring
  ; *-comm = *-comm
  }

+-*-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
+-*-commutativeSemiring = record
  { isCommutativeSemiring = +-*-isCommutativeSemiring
  }

+-*-isRing : IsRing ℙ._+_ ℙ._*_ id 0ℙ 1ℙ
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-cong           = cong₂ ℙ._*_
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  ; zero             = *-zero
  }

+-*-ring : Ring 0ℓ 0ℓ
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-isCommutativeRing : IsCommutativeRing ℙ._+_ ℙ._*_ id 0ℙ 1ℙ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }

------------------------------------------------------------------------
-- relating Parity and Sign

+-homo-* : ∀ p q → toSign (p ℙ.+ q) ≡ (toSign p) 𝕊.* (toSign q)
+-homo-* 0ℙ 0ℙ = refl
+-homo-* 0ℙ 1ℙ = refl
+-homo-* 1ℙ 0ℙ = refl
+-homo-* 1ℙ 1ℙ = refl

⁻¹-homo-opposite : ∀ p → toSign (p ⁻¹) ≡ 𝕊.opposite (toSign p)
⁻¹-homo-opposite 0ℙ = refl
⁻¹-homo-opposite 1ℙ = refl

toSign-inverts-fromSign : ∀ {p s} → toSign p ≡ s → fromSign s ≡ p
toSign-inverts-fromSign {0ℙ} refl = refl
toSign-inverts-fromSign {1ℙ} refl = refl

fromSign-inverts-toSign : ∀ {s p} → fromSign s ≡ p → toSign p ≡ s
fromSign-inverts-toSign { + }  refl = refl
fromSign-inverts-toSign { - } refl = refl

toSign-injective : Injective _≡_ _≡_ toSign
toSign-injective {p} {q} eq = begin
  p                   ≡⟨ sym (toSign-inverts-fromSign {p} refl) ⟩
  fromSign (toSign p) ≡⟨ cong fromSign eq ⟩
  fromSign (toSign q) ≡⟨ toSign-inverts-fromSign {q} refl ⟩
  q ∎ where open ≡-Reasoning

toSign-surjective : Surjective _≡_ _≡_ toSign
toSign-surjective s = (fromSign s) , fromSign-inverts-toSign {s} refl

toSign-isMagmaHomomorphism : IsMagmaHomomorphism ℙ.+-rawMagma 𝕊.*-rawMagma toSign
toSign-isMagmaHomomorphism = record
  { isRelHomomorphism = record
    { cong = cong toSign }
  ; homo = +-homo-*
  }

toSign-isMagmaMonomorphism : IsMagmaMonomorphism ℙ.+-rawMagma 𝕊.*-rawMagma toSign
toSign-isMagmaMonomorphism = record
  { isMagmaHomomorphism = toSign-isMagmaHomomorphism
  ; injective = toSign-injective
  }

toSign-isMagmaIsomorphism : IsMagmaIsomorphism ℙ.+-rawMagma 𝕊.*-rawMagma toSign
toSign-isMagmaIsomorphism = record
  { isMagmaMonomorphism = toSign-isMagmaMonomorphism
  ; surjective = toSign-surjective
  }

toSign-isMonoidHomomorphism : IsMonoidHomomorphism ℙ.+-0-rawMonoid 𝕊.*-1-rawMonoid toSign
toSign-isMonoidHomomorphism = record
  { isMagmaHomomorphism = toSign-isMagmaHomomorphism
  ; ε-homo = refl
  }

toSign-isMonoidMonomorphism : IsMonoidMonomorphism ℙ.+-0-rawMonoid 𝕊.*-1-rawMonoid toSign
toSign-isMonoidMonomorphism = record
  { isMonoidHomomorphism = toSign-isMonoidHomomorphism
  ; injective = toSign-injective
  }

toSign-isMonoidIsomorphism : IsMonoidIsomorphism ℙ.+-0-rawMonoid 𝕊.*-1-rawMonoid toSign
toSign-isMonoidIsomorphism = record
  { isMonoidMonomorphism = toSign-isMonoidMonomorphism
  ; surjective = toSign-surjective
  }

toSign-isGroupHomomorphism : IsGroupHomomorphism ℙ.+-0-rawGroup 𝕊.*-1-rawGroup toSign
toSign-isGroupHomomorphism = record
  { isMonoidHomomorphism = toSign-isMonoidHomomorphism
  ; ⁻¹-homo = ⁻¹-homo-opposite
  }

toSign-isGroupMonomorphism : IsGroupMonomorphism ℙ.+-0-rawGroup 𝕊.*-1-rawGroup toSign
toSign-isGroupMonomorphism = record
  { isGroupHomomorphism = toSign-isGroupHomomorphism
  ; injective = toSign-injective
  }

toSign-isGroupIsomorphism : IsGroupIsomorphism ℙ.+-0-rawGroup 𝕊.*-1-rawGroup toSign
toSign-isGroupIsomorphism = record
  { isGroupMonomorphism = toSign-isGroupMonomorphism
  ; surjective = toSign-surjective
  }


------------------------------------------------------------------------
-- relating Nat and Parity

-- successor and (_⁻¹)

suc-homo-⁻¹ : ∀ n → (parity (suc n)) ⁻¹ ≡ parity n
suc-homo-⁻¹ zero    = refl
suc-homo-⁻¹ (suc n) = ⁻¹-selfInverse (suc-homo-⁻¹ n)

-- parity is a _+_ homomorphism

+-homo-+      : ∀ m n → parity (m ℕ.+ n) ≡ parity m ℙ.+ parity n
+-homo-+ zero    n = refl
+-homo-+ (suc m) n = begin
  parity (suc m ℕ.+ n)         ≡⟨ suc-+-homo-⁻¹ m n ⟩
  (parity m) ⁻¹ ℙ.+ parity n   ≡⟨ cong (ℙ._+ parity n) (suc-homo-⁻¹ (suc m)) ⟩
  parity (suc m) ℙ.+ parity n  ∎
  where
    open ≡-Reasoning
    suc-+-homo-⁻¹ : ∀ m n → parity (suc m ℕ.+ n) ≡ (parity m) ⁻¹ ℙ.+ parity n
    suc-+-homo-⁻¹ zero    n = sym (suc-homo-⁻¹ (suc n))
    suc-+-homo-⁻¹ (suc m) n = begin
      parity (suc (suc m) ℕ.+ n)        ≡⟨⟩
      parity (m ℕ.+ n)                  ≡⟨ +-homo-+ m n ⟩
      parity m ℙ.+ parity n             ≡⟨ cong (ℙ._+ parity n) (sym (suc-homo-⁻¹ m)) ⟩
      (parity (suc m)) ⁻¹ ℙ.+ parity n  ∎

-- parity is a _*_ homomorphism

*-homo-*      : ∀ m n → parity (m ℕ.* n) ≡ parity m ℙ.* parity n
*-homo-* zero    n = refl
*-homo-* (suc m) n = begin
  parity (suc m ℕ.* n)        ≡⟨⟩
  parity (n ℕ.+ m ℕ.* n)      ≡⟨ +-homo-+ n (m ℕ.* n) ⟩
  q ℙ.+ parity (m ℕ.* n)      ≡⟨ cong (q ℙ.+_) (*-homo-* m n) ⟩
  q ℙ.+ (p ℙ.* q)             ≡⟨ lemma p q ⟩
  (p ⁻¹) ℙ.* q                ≡⟨⟩
  (parity m) ⁻¹ ℙ.* q         ≡⟨ cong (ℙ._* q) (suc-homo-⁻¹ (suc m)) ⟩
  parity (suc m) ℙ.* q        ≡⟨⟩
  parity (suc m) ℙ.* parity n ∎
  where
    open ≡-Reasoning
    p = parity m
    q = parity n
    -- this lemma simplifies things a lot
    lemma : ∀ p q → q ℙ.+ (p ℙ.* q) ≡ (p ⁻¹) ℙ.* q
    lemma 0ℙ 0ℙ = refl
    lemma 0ℙ 1ℙ = refl
    lemma 1ℙ 0ℙ = refl
    lemma 1ℙ 1ℙ = refl

------------------------------------------------------------------------
-- parity is a Semiring homomorphism from Nat to Parity

parity-isMagmaHomomorphism : IsMagmaHomomorphism ℕ.+-rawMagma ℙ.+-rawMagma parity
parity-isMagmaHomomorphism = record
  { isRelHomomorphism = record
    { cong = cong parity }
  ; homo = +-homo-+
  }

parity-isMonoidHomomorphism : IsMonoidHomomorphism ℕ.+-0-rawMonoid ℙ.+-0-rawMonoid parity
parity-isMonoidHomomorphism = record
  { isMagmaHomomorphism = parity-isMagmaHomomorphism
  ; ε-homo = refl
  }

parity-isNearSemiringHomomorphism : IsNearSemiringHomomorphism ℕ.+-*-rawNearSemiring ℙ.+-*-rawNearSemiring parity
parity-isNearSemiringHomomorphism = record
  { +-isMonoidHomomorphism = parity-isMonoidHomomorphism
  ; *-homo = *-homo-*
  }

parity-isSemiringHomomorphism : IsSemiringHomomorphism ℕ.+-*-rawSemiring ℙ.+-*-rawSemiring parity
parity-isSemiringHomomorphism = record
  { isNearSemiringHomomorphism = parity-isNearSemiringHomomorphism
  ; 1#-homo = refl
  }
