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
open import Function.Core using (_∘′_; _$′_; const; flip)
open import Relation.Unary using (IUniversal)
open import Relation.Binary.PropositionalEquality

private
  variable
    a b r : Level
    A : Set a
    B : Set b

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

  private
    g : Product n as → R
    g = uncurryₙ n f

-- Congruentₙ : ∀ n. ∀ a₁₁ a₁₂ ⋯ aₙ₁ aₙ₂ →
--                   a₁₁ ≡ a₁₂ → ⋯ → aₙ₁ ≡ aₙ₂ →
--                   f a₁₁ ⋯ aₙ₁ ≡ f a₁₂ ⋯ aₙ₂

  Congruentₙ : Set (r Level.⊔ ⨆ n ls)
  Congruentₙ = ∀ {l r} → Equalₙ n l r ⇉ (g l ≡ g r)

  congₙ : Congruentₙ
  congₙ = curryₙ n (cong g ∘′ fromEqualₙ n)

-- Congruence at a specific location

module _ m n {ls ls'} {as : Sets m ls} {bs : Sets n ls'}
         (f : as ⇉ (A → bs ⇉ B)) where

  private
    g : Product m as → A → Product n bs → B
    g vs a ws = uncurryₙ n (uncurryₙ m f vs a) ws

  congAt : ∀ {vs ws a₁ a₂} → a₁ ≡ a₂ → g vs a₁ ws ≡ g vs a₂ ws
  congAt {vs} {ws} = cong (λ a → g vs a ws)

------------------------------------------------------------------------
-- Injectivity

module _ n {ls} {as : Sets n ls} {R : Set r} (con : as ⇉ R) where

-- Injectiveₙ : ∀ n. ∀ a₁₁ a₁₂ ⋯ aₙ₁ aₙ₂ →
--                   con a₁₁ ⋯ aₙ₁ ≡ con a₁₂ ⋯ aₙ₂ →
--                   a₁₁ ≡ a₁₂ × ⋯ × aₙ₁ ≡ aₙ₂

  private
    c : Product n as → R
    c = uncurryₙ n con

  Injectiveₙ : Set (r Level.⊔ ⨆ n ls)
  Injectiveₙ = ∀ {l r} → c l ≡ c r → Product n (Equalₙ n l r)

  injectiveₙ : (∀ {l r} → c l ≡ c r → l ≡ r) → Injectiveₙ
  injectiveₙ con-inj eq = toEqualₙ n (con-inj eq)
