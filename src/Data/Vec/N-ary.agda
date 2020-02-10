------------------------------------------------------------------------
-- The Agda standard library
--
-- Code for converting Vec A n → B to and from n-ary functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.N-ary where

open import Data.Nat.Base hiding (_⊔_)
open import Data.Product as Prod
open import Data.Vec.Base
open import Function.Base
open import Function.Equivalence using (_⇔_; equivalence)
open import Level using (Level; _⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

private
  variable
    a b c ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- N-ary functions

N-ary-level : Level → Level → ℕ → Level
N-ary-level ℓ₁ ℓ₂ zero    = ℓ₂
N-ary-level ℓ₁ ℓ₂ (suc n) = ℓ₁ ⊔ N-ary-level ℓ₁ ℓ₂ n

N-ary : ∀ (n : ℕ) → Set ℓ₁ → Set ℓ₂ → Set (N-ary-level ℓ₁ ℓ₂ n)
N-ary zero    A B = B
N-ary (suc n) A B = A → N-ary n A B

------------------------------------------------------------------------
-- Conversion

curryⁿ : ∀ {n} → (Vec A n → B) → N-ary n A B
curryⁿ {n = zero}  f = f []
curryⁿ {n = suc n} f = λ x → curryⁿ (f ∘ _∷_ x)

_$ⁿ_ : ∀ {n} → N-ary n A B → (Vec A n → B)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

------------------------------------------------------------------------
-- Quantifiers

module _ {A : Set a} where

  -- Universal quantifier.

  ∀ⁿ : ∀ n → N-ary n A (Set ℓ) → Set (N-ary-level a ℓ n)
  ∀ⁿ zero    P = P
  ∀ⁿ (suc n) P = ∀ x → ∀ⁿ n (P x)

  -- Universal quantifier with implicit (hidden) arguments.

  ∀ⁿʰ : ∀ n → N-ary n A (Set ℓ) → Set (N-ary-level a ℓ n)
  ∀ⁿʰ zero    P = P
  ∀ⁿʰ (suc n) P = ∀ {x} → ∀ⁿʰ n (P x)

  -- Existential quantifier.

  ∃ⁿ : ∀ n → N-ary n A (Set ℓ) → Set (N-ary-level a ℓ n)
  ∃ⁿ zero    P = P
  ∃ⁿ (suc n) P = ∃ λ x → ∃ⁿ n (P x)

------------------------------------------------------------------------
-- N-ary function equality

Eq : ∀ {A : Set a} {B : Set b} {C : Set c} n →
     REL B C ℓ → REL (N-ary n A B) (N-ary n A C) (N-ary-level a ℓ n)
Eq n _∼_ f g = ∀ⁿ n (curryⁿ {n = n} λ xs → (f $ⁿ xs) ∼ (g $ⁿ xs))

-- A variant where all the arguments are implicit (hidden).

Eqʰ : ∀ {A : Set a} {B : Set b} {C : Set c} n →
      REL B C ℓ → REL (N-ary n A B) (N-ary n A C) (N-ary-level a ℓ n)
Eqʰ n _∼_ f g = ∀ⁿʰ n (curryⁿ {n = n} λ xs → (f $ⁿ xs) ∼ (g $ⁿ xs))

------------------------------------------------------------------------
-- Some lemmas

-- The functions curryⁿ and _$ⁿ_ are inverses.

left-inverse : ∀ {n} (f : Vec A n → B) →
               ∀ xs → (curryⁿ f $ⁿ xs) ≡ f xs
left-inverse f []       = refl
left-inverse f (x ∷ xs) = left-inverse (f ∘ _∷_ x) xs

right-inverse : ∀ n (f : N-ary n A B) →
                Eq n _≡_ (curryⁿ (_$ⁿ_ {n = n} f)) f
right-inverse zero    f = refl
right-inverse (suc n) f = λ x → right-inverse n (f x)

-- ∀ⁿ can be expressed in an "uncurried" way.

uncurry-∀ⁿ : ∀ n {P : N-ary n A (Set ℓ)} →
             ∀ⁿ n P ⇔ (∀ (xs : Vec A n) → P $ⁿ xs)
uncurry-∀ⁿ {a} {A} {ℓ} n = equivalence (⇒ n) (⇐ n)
  where
  ⇒ : ∀ n {P : N-ary n A (Set ℓ)} →
      ∀ⁿ n P → (∀ (xs : Vec A n) → P $ⁿ xs)
  ⇒ zero    p []       = p
  ⇒ (suc n) p (x ∷ xs) = ⇒ n (p x) xs

  ⇐ : ∀ n {P : N-ary n A (Set ℓ)} →
      (∀ (xs : Vec A n) → P $ⁿ xs) → ∀ⁿ n P
  ⇐ zero    p = p []
  ⇐ (suc n) p = λ x → ⇐ n (p ∘ _∷_ x)

-- ∃ⁿ can be expressed in an "uncurried" way.

uncurry-∃ⁿ : ∀ n {P : N-ary n A (Set ℓ)} →
             ∃ⁿ n P ⇔ (∃ λ (xs : Vec A n) → P $ⁿ xs)
uncurry-∃ⁿ {a} {A} {ℓ} n = equivalence (⇒ n) (⇐ n)
  where
  ⇒ : ∀ n {P : N-ary n A (Set ℓ)} →
      ∃ⁿ n P → (∃ λ (xs : Vec A n) → P $ⁿ xs)
  ⇒ zero    p       = ([] , p)
  ⇒ (suc n) (x , p) = Prod.map (_∷_ x) id (⇒ n p)

  ⇐ : ∀ n {P : N-ary n A (Set ℓ)} →
      (∃ λ (xs : Vec A n) → P $ⁿ xs) → ∃ⁿ n P
  ⇐ zero    ([] , p)     = p
  ⇐ (suc n) (x ∷ xs , p) = (x , ⇐ n (xs , p))

-- Conversion preserves equality.

module _ (_∼_ : REL B C ℓ) where

  curryⁿ-cong : ∀ {n} (f : Vec A n → B) (g : Vec A n → C) →
                (∀ xs → f xs ∼ g xs) →
                Eq n _∼_ (curryⁿ f) (curryⁿ g)
  curryⁿ-cong {n = zero}  f g hyp = hyp []
  curryⁿ-cong {n = suc n} f g hyp = λ x →
    curryⁿ-cong (f ∘ _∷_ x) (g ∘ _∷_ x) (λ xs → hyp (x ∷ xs))

  curryⁿ-cong⁻¹ : ∀ {n} (f : Vec A n → B) (g : Vec A n → C) →
                  Eq n _∼_ (curryⁿ f) (curryⁿ g) →
                  ∀ xs → f xs ∼ g xs
  curryⁿ-cong⁻¹ f g hyp []       = hyp
  curryⁿ-cong⁻¹ f g hyp (x ∷ xs) =
    curryⁿ-cong⁻¹ (f ∘ _∷_ x) (g ∘ _∷_ x) (hyp x) xs

  appⁿ-cong : ∀ {n} (f : N-ary n A B) (g : N-ary n A C) →
              Eq n _∼_ f g →
              (xs : Vec A n) → (f $ⁿ xs) ∼ (g $ⁿ xs)
  appⁿ-cong f g hyp []       = hyp
  appⁿ-cong f g hyp (x ∷ xs) = appⁿ-cong (f x) (g x) (hyp x) xs

  appⁿ-cong⁻¹ : ∀ {n} (f : N-ary n A B) (g : N-ary n A C) →
                ((xs : Vec A n) → (f $ⁿ xs) ∼ (g $ⁿ xs)) →
                Eq n _∼_ f g
  appⁿ-cong⁻¹ {n = zero}  f g hyp = hyp []
  appⁿ-cong⁻¹ {n = suc n} f g hyp = λ x →
    appⁿ-cong⁻¹ (f x) (g x) (λ xs → hyp (x ∷ xs))

-- Eq and Eqʰ are equivalent.

Eq-to-Eqʰ : ∀ n (_∼_ : REL B C ℓ) {f : N-ary n A B} {g : N-ary n A C} →
            Eq n _∼_ f g → Eqʰ n _∼_ f g
Eq-to-Eqʰ zero    _∼_ eq = eq
Eq-to-Eqʰ (suc n) _∼_ eq = Eq-to-Eqʰ n _∼_ (eq _)

Eqʰ-to-Eq : ∀ n (_∼_ : REL B C ℓ) {f : N-ary n A B} {g : N-ary n A C} →
            Eqʰ n _∼_ f g → Eq n _∼_ f g
Eqʰ-to-Eq zero    _∼_ eq = eq
Eqʰ-to-Eq (suc n) _∼_ eq = λ _ → Eqʰ-to-Eq n _∼_ eq
