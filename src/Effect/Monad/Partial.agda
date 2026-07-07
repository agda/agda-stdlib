------------------------------------------------------------------------
-- The Agda standard library
--
-- The partial monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Partial where

open import Level using (Level; suc; zero;_⊔_)
open import Data.Product using (_×_; Σ; Σ-syntax; _,_)
open import Data.Empty.Polymorphic using (⊥-elim; ⊥)
open import Data.Unit.Polymorphic using (⊤)

private
  variable
    a ℓ ℓ' : Level
    A B : Set a

------------------------------------------------------------------------
-- Object part: type definition

record ↯ (A : Set a) (ℓ : Level) : Set (a ⊔ suc ℓ) where
  field
    Dom : Set ℓ
    dom : Dom → A

open ↯

------------------------------------------------------------------------
-- Arrow part: Functor, Applicative, Monad component definition

↯-map : (A → B) → ↯ A ℓ → ↯ B ℓ
↯-map f a↯ .Dom = a↯ .Dom
↯-map f a↯ .dom d = f (a↯ .dom d)

↯-ap : ↯ (A → B) ℓ → ↯ A ℓ' → ↯ B (ℓ ⊔ ℓ')
↯-ap a→b↯ a↯ .Dom = a→b↯ .Dom × a↯ .Dom
↯-ap a→b↯ a↯ .dom (f↓ , a↓) = a→b↯ .dom f↓ (a↯ .dom a↓)

↯-bind : ↯ A ℓ → (A → ↯ B ℓ') → ↯ B (ℓ ⊔ ℓ')
↯-bind a↯ f .Dom = Σ[ a↓ ∈ a↯ .Dom ] f (a↯ .dom a↓) .Dom
↯-bind a↯ f .dom (a↓ , fa↓) = f (a↯ .dom a↓) .dom fa↓

------------------------------------------------------------------------
-- Specific constructions

never : ↯ A ℓ
never {ℓ = ℓ} .Dom = ⊥ {ℓ = ℓ}
never .dom = ⊥-elim

always : A → ↯ A ℓ
always {ℓ = ℓ} a .Dom = ⊤ {ℓ = ℓ}
always a .dom _ = a

