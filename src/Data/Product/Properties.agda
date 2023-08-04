------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of products
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Properties where

open import Axiom.UniquenessOfIdentityProofs
open import Data.Product.Base
open import Function.Base using (_∋_; _∘_; id)
open import Function.Bundles using (_↔_; mk↔′)
open import Level using (Level)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable as Dec using (Dec; yes; no)

private
  variable
    a b c d ℓ : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

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

map-cong : ∀ {f g : A → C} {h i : B → D} → f ≗ g → h ≗ i → map f h ≗ map g i
map-cong f≗g h≗i (x , y) = cong₂ _,_ (f≗g x) (h≗i y)

-- The following properties are definitionally true (because of η)
-- but for symmetry with ⊎ it is convenient to define and name them.

swap-involutive : swap {A = A} {B = B} ∘ swap ≗ id
swap-involutive _ = refl

------------------------------------------------------------------------
-- Equality between pairs can be expressed as a pair of equalities

module _ {A : Set a} {B : A → Set b} {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : Σ A B} where
  Σ-≡,≡→≡ : Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂) → p₁ ≡ p₂
  Σ-≡,≡→≡ (refl , refl) = refl

  Σ-≡,≡←≡ : p₁ ≡ p₂ → Σ (a₁ ≡ a₂) (λ p → subst B p b₁ ≡ b₂)
  Σ-≡,≡←≡ refl = refl , refl

  private
    left-inverse-of : (p : Σ (a₁ ≡ a₂) (λ x → subst B x b₁ ≡ b₂)) →
                      Σ-≡,≡←≡ (Σ-≡,≡→≡ p) ≡ p
    left-inverse-of (refl , refl) = refl

    right-inverse-of : (p : p₁ ≡ p₂) → Σ-≡,≡→≡ (Σ-≡,≡←≡ p) ≡ p
    right-inverse-of refl = refl

  Σ-≡,≡↔≡ : (∃ λ (p : a₁ ≡ a₂) → subst B p b₁ ≡ b₂) ↔ p₁ ≡ p₂
  Σ-≡,≡↔≡ = mk↔′ Σ-≡,≡→≡ Σ-≡,≡←≡ right-inverse-of left-inverse-of

-- the non-dependent case. Proofs are exactly as above, and straightforward.
module _ {p₁@(a₁ , b₁) p₂@(a₂ , b₂) : A × B} where
  ×-≡,≡→≡ : (a₁ ≡ a₂ × b₁ ≡ b₂) → p₁ ≡ p₂
  ×-≡,≡→≡ (refl , refl) = refl

  ×-≡,≡←≡ : p₁ ≡ p₂ → (a₁ ≡ a₂ × b₁ ≡ b₂)
  ×-≡,≡←≡ refl = refl , refl

  ×-≡,≡↔≡ : (a₁ ≡ a₂ × b₁ ≡ b₂) ↔ p₁ ≡ p₂
  ×-≡,≡↔≡ = mk↔′
    ×-≡,≡→≡
    ×-≡,≡←≡
    (λ { refl          → refl        })
    (λ { (refl , refl) → refl        })

------------------------------------------------------------------------
-- The order of ∃₂ can be swapped

∃∃↔∃∃ : (R : A → B → Set ℓ) → (∃₂ λ x y → R x y) ↔ (∃₂ λ y x → R x y)
∃∃↔∃∃ R = mk↔′ to from cong′ cong′
  where
  to : (∃₂ λ x y → R x y) → (∃₂ λ y x → R x y)
  to (x , y , Rxy) = (y , x , Rxy)

  from : (∃₂ λ y x → R x y) → (∃₂ λ x y → R x y)
  from (y , x , Rxy) = (x , y , Rxy)
