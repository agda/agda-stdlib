------------------------------------------------------------------------
-- The Agda standard library
--
-- Freely adding Extrema to any Set
------------------------------------------------------------------------

module Relation.Binary.Construction.Free.Extrema where

open import Relation.Binary.Construction.Free.Infimum as Infimum   using (_₋)
open import Relation.Binary.Construction.Free.Supremum as Supremum using (_⁺)

_± : ∀ {a} → Set a → Set a
A ± = A ₋ ⁺

pattern ⊥⁺    = Supremum.[ Infimum.⊥⁺ ]
pattern [_] k = Supremum.[ Infimum.[ k ] ]
pattern ⊤⁺    = Supremum.⊤⁺
