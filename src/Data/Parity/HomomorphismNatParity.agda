------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about parities
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.HomomorphismNatParity where

open import Data.Nat.Base as ℕ using (zero; suc; parity)
open import Data.Parity.Base as ℙ using (0ℙ; 1ℙ; _⁻¹)
open import Data.Parity.Properties using (⁻¹-inverts)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning)

open import Algebra.Morphism.Structures
{-
open import Algebra.Morphism.Structures
  using (IsMagmaHomomorphism; IsMonoidHomomorphism
  ; IsNearSemiringHomomorphism; IsSemiringHomomorphism)
-}
------------------------------------------------------------------------
-- relating Nat and Parity

-- successor and (_⁻¹)

suc-homo-⁻¹ : ∀ n → (parity (suc n)) ⁻¹ ≡ parity n
suc-homo-⁻¹ zero    = refl
suc-homo-⁻¹ (suc n) = ⁻¹-inverts (suc-homo-⁻¹ n)

-- parity is a _+_ homomorphism

+-homo-+      : ∀ m n → parity (m ℕ.+ n) ≡ parity m ℙ.+ parity n
+-homo-+ zero    n = refl
+-homo-+ (suc m) n = begin
  parity (suc m ℕ.+ n)        ≡⟨ suc-+-homo-⁻¹ m n ⟩
  (parity m) ⁻¹ ℙ.+ parity n   ≡⟨ cong (ℙ._+ parity n) (suc-homo-⁻¹ (suc m)) ⟩
  parity (suc m) ℙ.+ parity n  ∎
  where
    open ≡-Reasoning
    suc-+-homo-⁻¹ : ∀ m n → parity (suc m ℕ.+ n) ≡ (parity m) ⁻¹ ℙ.+ parity n
    suc-+-homo-⁻¹ zero    n = sym (suc-homo-⁻¹ (suc n))
    suc-+-homo-⁻¹ (suc m) n = begin
      parity (suc (suc m) ℕ.+ n)        ≡⟨⟩
      parity (m ℕ.+ n)                  ≡⟨ +-homo-+ m n ⟩
      parity m ℙ.+ parity n              ≡⟨ cong (ℙ._+ parity n) (sym (suc-homo-⁻¹ m)) ⟩
      (parity (suc m)) ⁻¹ ℙ.+ (parity n) ∎

-- parity is a _*_ homomorphism

*-homo-*      : ∀ m n → parity (m ℕ.* n) ≡ parity m ℙ.* parity n
*-homo-* zero    n = refl
*-homo-* (suc m) n = begin
  parity (suc m ℕ.* n)       ≡⟨⟩
  parity (n ℕ.+ m ℕ.* n)    ≡⟨ +-homo-+ n (m ℕ.* n) ⟩
  q ℙ.+ parity (m ℕ.* n)     ≡⟨ cong (q ℙ.+_) (*-homo-* m n) ⟩
  q ℙ.+ (p ℙ.* q)             ≡⟨ lemma p q ⟩
  ((p ⁻¹) ℙ.* q)              ≡⟨⟩
  ((parity m) ⁻¹ ℙ.* q)       ≡⟨ cong (ℙ._* q) (suc-homo-⁻¹ (suc m)) ⟩
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
-- parity is a Semiring homomorphism

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
