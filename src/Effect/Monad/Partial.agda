------------------------------------------------------------------------
-- The Agda standard library
--
-- The partial monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Partial where

open import Level using (Level; suc; zero;_⊔_)
open import Data.Product using (_×_; Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥-elim; ⊥)
open import Data.Unit using (⊤)

private  
  variable
    ℓ ℓ' : Level
    A B : Set ℓ

------------------------------------------------------------------------
-- The partial monad

record ↯ {ℓ} (A : Set ℓ) (ℓ' : Level) : Set (ℓ ⊔ suc ℓ') where
  field
    Dom : Set ℓ'
    elt : Dom → A

open ↯

never : ↯ A zero
never .Dom = ⊥
never .elt = ⊥-elim

always : A → ↯ A zero
always a .Dom = ⊤
always a .elt _ = a

↯-bind : ↯ A ℓ → (A → ↯ B ℓ') → ↯ B (ℓ ⊔ ℓ')
↯-bind a↯ f .Dom = Σ[ a↓ ∈ a↯ .Dom ] f (a↯ .elt a↓) .Dom
↯-bind a↯ f .elt (a↓ , fa↓) = f (a↯ .elt a↓) .elt fa↓

↯-map : (A → B) → ↯ A ℓ → ↯ B ℓ
↯-map f a↯ .Dom = a↯ .Dom
↯-map f a↯ .elt d = f (a↯ .elt d)

↯-ap : ↯ (A → B) ℓ → ↯ A ℓ' → ↯ B (ℓ ⊔ ℓ')
↯-ap a→b↯ a↯ .Dom = a→b↯ .Dom × a↯ .Dom
↯-ap a→b↯ a↯ .elt (f↓ , a↓) = a→b↯ .elt f↓ (a↯ .elt a↓)


