------------------------------------------------------------------------
-- The Agda standard library
--
-- The partial monad cf. https://1lab.dev/Data.Partial.Base.html
--
-- Modulo proof-relevance, this defines the free pointed DCPO,
-- whereas delay-like monads, as in `Effect.Monad.Partiality`,
-- are aiming to define the free ωCPO.
-- NB. in each case, there are additional 'up to' considerations
-- wrt 'appropriate' setoid equality/quotient/bisimilarity.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Effect.Monad.Partial where

open import Data.Empty.Polymorphic using (⊥-elim; ⊥)
open import Data.Product.Base using (_×_; Σ; Σ-syntax; _,_)
open import Data.Sum.Base using (_⊎_; [_,_]′)
open import Data.Unit.Polymorphic using (⊤)

open import Function.Base using (id)

open import Level using (Level; suc; zero;_⊔_)

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
-- Arrow part: Functor, Applicative, Alternative, Monad

map : (A → B) → ↯ A ℓ → ↯ B ℓ
map f a↯ .Dom = a↯ .Dom
map f a↯ .dom d = f (a↯ .dom d)

pure : A → ↯ A ℓ
pure {ℓ = ℓ} a .Dom = ⊤ {ℓ = ℓ}
pure a .dom _ = a

ap : ↯ (A → B) ℓ → ↯ A ℓ' → ↯ B (ℓ ⊔ ℓ')
ap a→b↯ a↯ .Dom = a→b↯ .Dom × a↯ .Dom
ap a→b↯ a↯ .dom (f↓ , a↓) = a→b↯ .dom f↓ (a↯ .dom a↓)

empty : ↯ A ℓ
empty {ℓ = ℓ} .Dom = ⊥ {ℓ = ℓ}
empty .dom = ⊥-elim

_<|>_ : ↯ A ℓ → ↯ A ℓ' → ↯ A (ℓ ⊔ ℓ')
(l↯ <|> r↯) .Dom = l↯ .Dom ⊎ r↯ .Dom
(l↯ <|> r↯) .dom = [ l↯ .dom , r↯ .dom ]′

bind : ↯ A ℓ → (A → ↯ B ℓ') → ↯ B (ℓ ⊔ ℓ')
bind a↯ f .Dom = Σ[ a↓ ∈ a↯ .Dom ] f (a↯ .dom a↓) .Dom
bind a↯ f .dom (a↓ , fa↓) = f (a↯ .dom a↓) .dom fa↓

------------------------------------------------------------------------
-- Specific constructions

-- the 'always defined' partial element
always = pure

-- the 'never defined' partial element
never = empty

-- The following definition lets you add an assumption that you will
-- need to discharge later. This is very useful when programming in
-- the partiality/multimap monad; it's basically a proof-relevant,
-- witness providing form of guard :: Bool -> m () or assert.

-- 'guarding' an element of A

guard : ↯ A _
guard {A = A} .Dom = A
guard .dom = id
