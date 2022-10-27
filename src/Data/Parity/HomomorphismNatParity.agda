------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about parities
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.HomomorphismNatParity where

open import Data.Empty
open import Data.Nat.Base
open import Data.Parity.Base using (Parity; 0ℙ; 1ℙ; _⁻¹)
  renaming (_+_ to _+ℙ_; _*_ to _*ℙ_
  ; +-rawMagma to ℙ+-rawMagma; +-0-rawMonoid to ℙ+-0-rawMonoid
  ; +-*-rawNearSemiring to ℙ+-*-rawNearSemiring; +-*-rawSemiring to ℙ+-*-rawSemiring)
open import Data.Parity.Properties using (⁻¹-inverts)
open import Relation.Binary.PropositionalEquality

open import Algebra.Morphism.Structures
  using (IsMagmaHomomorphism; IsMonoidHomomorphism
  ; IsNearSemiringHomomorphism; IsSemiringHomomorphism)

------------------------------------------------------------------------
-- relating Nat and Parity

suc-homo-⁻¹ : ∀ n → (parity (suc n)) ⁻¹ ≡ parity n
suc-homo-⁻¹ zero    = refl
suc-homo-⁻¹ (suc n) = ⁻¹-inverts (suc-homo-⁻¹ n)

+-homo-+      : ∀ m n → parity (m + n) ≡ (parity m) +ℙ (parity n)
suc-+-homo-⁻¹ : ∀ m n → parity (suc m + n) ≡ (parity m) ⁻¹ +ℙ (parity n)

suc-+-homo-⁻¹ zero    n = sym (⁻¹-inverts (suc-homo-⁻¹ n))
suc-+-homo-⁻¹ (suc m) n = begin
  parity (suc (suc m) + n)          ≡⟨⟩
  parity (m + n)                    ≡⟨ +-homo-+ m n ⟩
  (parity m) +ℙ (parity n)          ≡⟨ cong (_+ℙ (parity n)) (sym (suc-homo-⁻¹ m)) ⟩
  (parity (suc m)) ⁻¹ +ℙ (parity n) ∎  where open ≡-Reasoning

+-homo-+ zero    n = refl
+-homo-+ (suc m) n = begin
  parity (suc m + n)           ≡⟨ suc-+-homo-⁻¹ m n ⟩
  (parity m) ⁻¹ +ℙ (parity n) ≡⟨ cong (_+ℙ (parity n)) (⁻¹-inverts (suc-homo-⁻¹ m)) ⟩
  parity (suc m) +ℙ parity n  ∎ where open ≡-Reasoning

*-homo-*      : ∀ m n → parity (m * n) ≡ (parity m) *ℙ (parity n)
*-homo-* zero    n = refl
*-homo-* (suc m) n with parity m in m≡p | parity n in n≡q
... | p | q = begin
  parity (suc m * n)                  ≡⟨⟩
  parity (n + m * n)                  ≡⟨ +-homo-+ n (m * n) ⟩
  parity n +ℙ parity (m * n)          ≡⟨ cong ((parity n) +ℙ_) (*-homo-* m n) ⟩
  parity n +ℙ (parity m *ℙ parity n) ≡⟨ cong (_+ℙ (parity m *ℙ parity n)) n≡q ⟩
  q +ℙ (parity m *ℙ parity n)        ≡⟨ cong (q +ℙ_) (cong₂ _*ℙ_ m≡p n≡q) ⟩
  q +ℙ (p *ℙ q)                      ≡⟨ lemma p q ⟩
  ((p ⁻¹) *ℙ q)                       ≡⟨ cong (_*ℙ q) (cong _⁻¹ (sym m≡p)) ⟩
  ((parity m) ⁻¹ *ℙ q)                ≡⟨ cong (_*ℙ q) (⁻¹-inverts (suc-homo-⁻¹ m)) ⟩
  parity (suc m) *ℙ q ∎ where
    open ≡-Reasoning
    lemma : ∀ p q → q +ℙ (p *ℙ q) ≡ (p ⁻¹) *ℙ q
    lemma 0ℙ 0ℙ = refl
    lemma 0ℙ 1ℙ = refl
    lemma 1ℙ 0ℙ = refl
    lemma 1ℙ 1ℙ = refl

parity-isMagmaHomomorphism : IsMagmaHomomorphism +-rawMagma ℙ+-rawMagma parity
parity-isMagmaHomomorphism = record
  { isRelHomomorphism = record
    { cong = cong parity }
  ; homo = +-homo-+
  }

parity-isMonoidHomomorphism : IsMonoidHomomorphism +-0-rawMonoid ℙ+-0-rawMonoid parity
parity-isMonoidHomomorphism = record
  { isMagmaHomomorphism = parity-isMagmaHomomorphism
  ; ε-homo = refl
  }

parity-isNearSemiringHomomorphism : IsNearSemiringHomomorphism +-*-rawNearSemiring ℙ+-*-rawNearSemiring parity
parity-isNearSemiringHomomorphism = record
  { +-isMonoidHomomorphism = parity-isMonoidHomomorphism
  ; *-homo = *-homo-*
  }

parity-isSemiringHomomorphism : IsSemiringHomomorphism +-*-rawSemiring ℙ+-*-rawSemiring parity
parity-isSemiringHomomorphism = record
  { isNearSemiringHomomorphism = parity-isNearSemiringHomomorphism
  ; 1#-homo = refl
  }
