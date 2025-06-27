------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Decidable unary predicates on Fin
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Relation.Unary.Base where

open import Data.Fin.Base
open import Data.Nat.Base as ℕ
  using (ℕ; zero; suc)
open import Data.Product.Base as Product
  using (∃; ∃-syntax; ∃₂; _×_; _,_; map; proj₁; proj₂; uncurry; <_,_>)
open import Data.Product.Properties using (,-injective)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Function.Base using (_∘_; id; _$_; flip; const; _$-; λ-)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level)
open import Relation.Unary
  using (Pred; _⊆_; Satisfiable; Universal)

private
  variable
    f p : Level
    n : ℕ


------------------------------------------------------------------------
-- Quantification
------------------------------------------------------------------------

module _ {P : Pred (Fin (suc n)) p} where

  ∀-cons : P zero → Π[ P ∘ suc ] → Π[ P ]
  ∀-cons z s zero    = z
  ∀-cons z s (suc i) = s i

  ∀-cons-⇔ : (P zero × Π[ P ∘ suc ]) ⇔ Π[ P ]
  ∀-cons-⇔ = mk⇔ (uncurry ∀-cons) < _$ zero , _∘ suc >

  ∃-here : P zero → ∃⟨ P ⟩
  ∃-here = zero ,_

  ∃-there : ∃⟨ P ∘ suc ⟩ → ∃⟨ P ⟩
  ∃-there = map suc id

  ∃-toSum : ∃⟨ P ⟩ → P zero ⊎ ∃⟨ P ∘ suc ⟩
  ∃-toSum ( zero , P₀ ) = inj₁ P₀
  ∃-toSum (suc f , P₁₊) = inj₂ (f , P₁₊)

  ⊎⇔∃ : (P zero ⊎ ∃⟨ P ∘ suc ⟩) ⇔ ∃⟨ P ⟩
  ⊎⇔∃ = mk⇔ [ ∃-here , ∃-there ] ∃-toSum

------------------------------------------------------------------------
-- Effectful
------------------------------------------------------------------------

module _ {F : Set f → Set f} (RA : RawApplicative F) where

  open RawApplicative RA

  sequence : ∀ {P : Pred (Fin n) f} →
             (∀ i → F (P i)) → F (∀ i → P i)
  sequence {n = zero}  ∀iPi = pure λ()
  sequence {n = suc _} ∀iPi = ∀-cons <$> ∀iPi zero <*> sequence (∀iPi ∘ suc)

module _ {F : Set f → Set f} (RF : RawFunctor F) where

  open RawFunctor RF

  sequence⁻¹ : ∀ {A : Set f} {P : Pred A f} →
               F (∀ i → P i) → (∀ i → F (P i))
  sequence⁻¹ F∀iPi i = (λ f → f i) <$> F∀iPi

