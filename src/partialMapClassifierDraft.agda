module partialMapClassifierDraft where

open import Level

open import Data.Product
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Function.Bundles using (_↔_; Inverse)

-- The type of partial elements
record ↯ {ℓ} (A : Set ℓ) (ℓ' : Level) : Set (ℓ ⊔ suc ℓ') where
  field
    Dom : Set ℓ'
    elt : Dom → A

open ↯

private variable
  ℓ ℓ' : Level
  A B : Set ℓ


-- Examples : 
never : ↯ A zero
never .Dom = ⊥
never .elt = ⊥-elim

always : A → ↯ A zero
always a .Dom = ⊤
always a .elt _ = a

-- The bind propertie
bind : ↯ A ℓ → (A → ↯ B ℓ') → ↯ B (ℓ ⊔ ℓ')
bind a↯ f .Dom = Σ[ a↓ ∈ a↯ .Dom ] f (a↯ .elt a↓) .Dom
bind a↯ f .elt (a↓ , fa↓) = f (a↯ .elt a↓) .elt fa↓

--
part-map : (A → B) → ↯ A ℓ → ↯ B ℓ
part-map f a↯ .Dom = a↯ .Dom
part-map f a↯ .elt d = f (a↯ .elt d)

-- 
part-ap : ↯ (A → B) ℓ → ↯ A ℓ → ↯ B ℓ
part-ap a→b↯ a↯ .Dom = a→b↯ .Dom × a↯ .Dom
part-ap a→b↯ a↯ .elt (f↓ , a↓) = a→b↯ .elt f↓ (a↯ .elt a↓)

-- With different level : 
part-ap-diff : ↯ (A → B) ℓ → ↯ A ℓ' → ↯ B (ℓ ⊔ ℓ')
part-ap-diff a→b↯ a↯ .Dom = a→b↯ .Dom × a↯ .Dom
part-ap-diff a→b↯ a↯ .elt (f↓ , a↓) = a→b↯ .elt f↓ (a↯ .elt a↓)

------------------------------------------------------------------------

-- Extensionality for partial maps
part-ext : {A : Set ℓ} {x y : ↯ A ℓ'} 
         → (iso : x .Dom ↔  y .Dom)
         → (∀ (xd : x .Dom) → x .elt xd ≡ y .elt (Inverse.to iso xd))
         → x ≡ y
part-ext = {!   !}



