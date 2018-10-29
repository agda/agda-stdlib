------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type
------------------------------------------------------------------------

module Data.Maybe where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Bool.Base using (T)
open import Data.Maybe.All
open import Data.Maybe.Any

------------------------------------------------------------------------
-- The base type and some operations

open import Data.Maybe.Base public

------------------------------------------------------------------------
-- Using Any and All to define Is-just and Is-nothing

Is-just : ∀ {a} {A : Set a} → Maybe A → Set
Is-just = Any (λ _ → ⊤)

Is-nothing : ∀ {a} {A : Set a} → Maybe A → Set
Is-nothing = All (λ _ → ⊥)

to-witness : ∀ {p} {P : Set p} {m : Maybe P} → Is-just m → P
to-witness (just {x = p} _) = p

to-witness-T : ∀ {p} {P : Set p} (m : Maybe P) → T (is-just m) → P
to-witness-T (just p) _  = p
to-witness-T nothing  ()
