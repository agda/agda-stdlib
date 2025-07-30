module Effect.Monad.Partial where

open import Level

open import Data.Product
open import Data.Empty
open import Data.Unit

-- The type of partial elements
record ↯ {ℓ} (A : Set ℓ) (ℓ' : Level) : Set (ℓ ⊔ suc ℓ') where
  field
    Dom : Set ℓ'
    elt : Dom → A

open ↯

private variable
  ℓ ℓ' : Level
  A B : Set ℓ


-- 
never : ↯ A zero
never .Dom = ⊥
never .elt = ⊥-elim

always : A → ↯ A zero
always a .Dom = ⊤
always a .elt _ = a

----------------------- 
↯-bind : ↯ A ℓ → (A → ↯ B ℓ') → ↯ B (ℓ ⊔ ℓ')
↯-bind a↯ f .Dom = Σ[ a↓ ∈ a↯ .Dom ] f (a↯ .elt a↓) .Dom
↯-bind a↯ f .elt (a↓ , fa↓) = f (a↯ .elt a↓) .elt fa↓

-----------------------
↯-map : (A → B) → ↯ A ℓ → ↯ B ℓ
↯-map f a↯ .Dom = a↯ .Dom
↯-map f a↯ .elt d = f (a↯ .elt d)

-----------------------
↯-ap : ↯ (A → B) ℓ → ↯ A ℓ' → ↯ B (ℓ ⊔ ℓ')
↯-ap a→b↯ a↯ .Dom = a→b↯ .Dom × a↯ .Dom
↯-ap a→b↯ a↯ .elt (f↓ , a↓) = a→b↯ .elt f↓ (a↯ .elt a↓)


