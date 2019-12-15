------------------------------------------------------------------------
-- The Agda standard library
--
-- Fancy display functions for List
------------------------------------------------------------------------

module Data.List.Show where

open import Data.String using (String; rectangleʳ)
open import Data.List.Base
open import Data.Product using (-,_; proj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Vec.Bounded.Base as Vec≤ using (Vec≤)
import Data.Vec.Show as Show
open import Function.Base
open import Agda.Builtin.Equality

table : List (List String) → String
table rows = Show.table rectangle where

  rectangle : Vec (Vec String _) _
  rectangle = Vec.fromList
            $ map (Vec≤.padRight "")
            $ proj₂
            $ Vec≤.rectangle
            $ map (λ row → -, Vec≤.fromList row) rows

_ : table ( ("foo" ∷ "bar" ∷ [])
          ∷ ("partial" ∷ [])
          ∷ ("3" ∷ "2" ∷ "1" ∷ "⋯" ∷ "surprise!" ∷ [])
          ∷ [])
  ≡ "┌───────┬───┬─┬─┬─────────┐
\   \│    foo│bar│ │ │         │
\   \├───────┼───┼─┼─┼─────────┤
\   \│partial│   │ │ │         │
\   \├───────┼───┼─┼─┼─────────┤
\   \│      3│  2│1│⋯│surprise!│
\   \└───────┴───┴─┴─┴─────────┘"
_ = refl
