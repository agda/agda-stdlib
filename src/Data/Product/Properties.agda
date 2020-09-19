------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Properties where

open import Axiom.UniquenessOfIdentityProofs
open import Data.Product
open import Function
open import Level using (Level)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Product
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary using (Dec; yes; no)

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Equality (dependent)

module _ {B : A → Set b} where

  ,-injectiveˡ : ∀ {a c} {b : B a} {d : B c} → (a , b) ≡ (c , d) → a ≡ c
  ,-injectiveˡ refl = refl

  ,-injectiveʳ-≡ : ∀ {a b} {c : B a} {d : B b} → UIP A → (a , c) ≡ (b , d) → (q : a ≡ b) → subst B q c ≡ d
  ,-injectiveʳ-≡ {c = c} u refl q = cong (λ x → subst B x c) (u q refl)

  ,-injectiveʳ-UIP : ∀ {a} {b c : B a} → UIP A → (Σ A B ∋ (a , b)) ≡ (a , c) → b ≡ c
  ,-injectiveʳ-UIP u p = ,-injectiveʳ-≡ u p refl

  ≡-dec : DecidableEquality A → (∀ {a} → DecidableEquality (B a)) →
          DecidableEquality (Σ A B)
  ≡-dec dec₁ dec₂ (a , x) (b , y) with dec₁ a b
  ... | no [a≢b] = no ([a≢b] ∘ ,-injectiveˡ)
  ... | yes refl = Dec.map′ (cong (a ,_)) (,-injectiveʳ-UIP (Decidable⇒UIP.≡-irrelevant dec₁)) (dec₂ x y)

------------------------------------------------------------------------
-- Equality (non-dependent)

,-injectiveʳ : ∀ {a c : A} {b d : B} → (a , b) ≡ (c , d) → b ≡ d
,-injectiveʳ refl = refl

,-injective : ∀ {a c : A} {b d : B} → (a , b) ≡ (c , d) → a ≡ c × b ≡ d
,-injective refl = refl , refl

-- The following properties are definitionally true (because of η)
-- but for symmetry with ⊎ it is convenient to define and name them.

swap-involutive : swap {A = A} {B = B} ∘ swap ≗ id
swap-involutive _ = refl

------------------------------------------------------------------------
-- Equality between pairs can be expressed as a pair of equalities

Σ-≡,≡↔≡ : {A : Set a} {B : A → Set b} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A B} →
          (∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂) ↔ (p₁ ≡ p₂)
Σ-≡,≡↔≡ {A = A} {B = B} = mk↔ {f = to} (right-inverse-of , left-inverse-of)
  where
  to : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A B} →
       Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂) → p₁ ≡ p₂
  to (refl , refl) = refl

  from : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A B} →
         p₁ ≡ p₂ → Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)
  from refl = refl , refl

  left-inverse-of : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A B} →
                    (p : Σ (a₁ ≡ a₂) (λ x → subst B x b₁ ≡ b₂)) →
                    from (to p) ≡ p
  left-inverse-of (refl , refl) = refl

  right-inverse-of : {p₁ p₂ : Σ A B} (p : p₁ ≡ p₂) → to (from p) ≡ p
  right-inverse-of refl = refl

-- the non-dependent case. Proofs are exactly as above, and straightforward.
×-≡,≡↔≡ : {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : A × B} → (a₁ ≡ a₂ × b₁ ≡ b₂) ↔ p₁ ≡ p₂
×-≡,≡↔≡ = mk↔′
  (λ {(refl , refl) → refl})
  (λ { refl         → refl , refl})
  (λ {refl → refl})
  (λ {(refl , refl) → refl})

------------------------------------------------------------------------
-- The order of ∃₂ can be swapped

∃∃↔∃∃ : (R : A → B → Set ℓ) → (∃₂ λ x y → R x y) ↔ (∃₂ λ y x → R x y)
∃∃↔∃∃ R = mk↔′ to from cong′ cong′
  where
  to : (∃₂ λ x y → R x y) → (∃₂ λ y x → R x y)
  to (x , y , Rxy) = (y , x , Rxy)

  from : (∃₂ λ y x → R x y) → (∃₂ λ x y → R x y)
  from (y , x , Rxy) = (x , y , Rxy)
