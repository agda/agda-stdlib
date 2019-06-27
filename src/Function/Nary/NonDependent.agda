------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous N-ary Functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Nary.NonDependent where

------------------------------------------------------------------------
-- Concrete examples can be found in README.Nary. This file's comments
-- are more focused on the implementation details and the motivations
-- behind the design decisions.
------------------------------------------------------------------------

open import Level using (Level; 0ℓ; _⊔_; Lift)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Product.Nary.NonDependent
open import Function using (_∘′_; _$′_; const; flip)
open import Relation.Unary using (IUniversal)
open import Relation.Binary.PropositionalEquality

private
  variable
    r : Level

------------------------------------------------------------------------
-- Re-exporting the basic operations

open import Function.Nary.NonDependent.Base public

------------------------------------------------------------------------
-- Additional operations on Levels

ltabulate : ∀ n → (Fin n → Level) → Levels n
ltabulate zero    f = _
ltabulate (suc n) f = f zero , ltabulate n (f ∘′ suc)

lreplicate : ∀ n → Level → Levels n
lreplicate n ℓ = ltabulate n (const ℓ)

0ℓs : ∀[ Levels ]
0ℓs = lreplicate _ 0ℓ

------------------------------------------------------------------------
-- Congruence

module _ n {ls} {as : Sets n ls} {R : Set r} (f : as ⇉ R) where

-- Congruentₙ : ∀ n. ∀ a₁₁ a₁₂ ⋯ aₙ₁ aₙ₂ →
--                   a₁₁ ≡ a₁₂ → ⋯ → aₙ₁ ≡ aₙ₂ →
--                   f a₁₁ ⋯ aₙ₁ ≡ f a₁₂ ⋯ aₙ₂

  Congruentₙ : Set (r Level.⊔ ⨆ n ls)
  Congruentₙ = ∀ {l r} → Equalₙ n l r ⇉ (uncurryₙ n f l ≡ uncurryₙ n f r)

  congₙ : Congruentₙ
  congₙ = curryₙ n (cong (uncurryₙ n f) ∘′ fromEqualₙ n)

------------------------------------------------------------------------
-- Injectivitiy

module _ n {ls} {as : Sets n ls} {R : Set r} (con : as ⇉ R) where

-- Injectiveₙ : ∀ n. ∀ a₁₁ a₁₂ ⋯ aₙ₁ aₙ₂ →
--                   con a₁₁ ⋯ aₙ₁ ≡ con a₁₂ ⋯ aₙ₂ →
--                   a₁₁ ≡ a₁₂ × ⋯ × aₙ₁ ≡ aₙ₂

  Injectiveₙ : Set (r Level.⊔ ⨆ n ls)
  Injectiveₙ = ∀ {l r} → uncurryₙ n con l ≡ uncurryₙ n con r → Product n (Equalₙ n l r)

  injectiveₙ : (∀ {l r} → uncurryₙ n con l ≡ uncurryₙ n con r → l ≡ r) →
               Injectiveₙ
  injectiveₙ con-inj eq = toEqualₙ n (con-inj eq)
