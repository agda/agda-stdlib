------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Algebra where

open import Agda.Builtin.Sigma
open import Algebra.Definitions
open import Data.Empty using (⊥)
open import Data.Sum.Base
open import Data.Sum.Properties
open import Function.Base using (id)
open import Level

open import Function.Bundles using (_↔_; Inverse; mk↔)
import Function.Definitions as FuncDef

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

------------------------------------------------------------------------

module _ {a b : Level} {A : Set a} {B : Set b} where
  open FuncDef {A = A} {B} _≡_ _≡_

  -- mk↔ is a bit of a pain to use because here f and f⁻¹ need to always
  -- be specified.
  inverse : (f : A → B) (f⁻¹ : B → A) → Inverseˡ f f⁻¹ → Inverseʳ f f⁻¹ → A ↔ B
  inverse f f⁻¹ left right = mk↔ {f = f} {f⁻¹} (left , right)

private
  -- convenient abbreviations
  refl₁ : {a b : Level} {A : Set a} {B : Set b} {f : A → B} (x : A) → f x ≡ f x
  refl₁ _ = refl

  ♯ : {a b : Level} {B : Lift a ⊥ → Set b} → (w : Lift a ⊥) → B w
  ♯ ()

------------------------------------------------------------------------
-- Properties of ⊎

-- ⊎ is associative

⊎-assoc : ∀ ℓ → Associative {ℓ = ℓ} _↔_ _⊎_
⊎-assoc ℓ _ _ _ = inverse assocʳ assocˡ [ refl₁ , [ refl₁ , refl₁ ] ] [ [ refl₁ , refl₁ ] , refl₁ ]

-- ⊎ is commutative.
-- We don't use Commutative because it isn't polymorphic enough.

⊎-comm : {a b : Level} (A : Set a) (B : Set b) → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm _ _ = inverse swap swap swap-involutive swap-involutive

-- ⊥ is both left and right identity for ⊎
⊎-identityˡ : ∀ ℓ → LeftIdentity _↔_ (Lift ℓ ⊥) _⊎_
⊎-identityˡ _ _ = inverse [ ♯ , id ]′ inj₂ refl₁ [ ♯ , refl₁ ]

⊎-identityʳ : ∀ ℓ → RightIdentity _↔_ (Lift ℓ ⊥) _⊎_
⊎-identityʳ _ _ = inverse [ id , ♯ ] inj₁ refl₁ [ refl₁ , ♯ ]

⊎-identity : ∀ ℓ → Identity _↔_ (Lift ℓ ⊥) _⊎_
⊎-identity ℓ = ⊎-identityˡ ℓ , ⊎-identityʳ ℓ
