------------------------------------------------------------------------
-- The Agda standard library
--
-- Notation for freely adding extrema to any set
------------------------------------------------------------------------

module Relation.Nullary.Construct.Add.Extrema where

open import Relation.Nullary.Construct.Add.Infimum  as Infimum  using (_₋)
open import Relation.Nullary.Construct.Add.Supremum as Supremum using (_⁺)

_± : ∀ {a} → Set a → Set a
A ± = A ₋ ⁺

pattern ⊥±    = Supremum.[ Infimum.⊥₋ ]
pattern [_] k = Supremum.[ Infimum.[ k ] ]
pattern ⊤±    = Supremum.⊤⁺
