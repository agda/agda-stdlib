------------------------------------------------------------------------
-- The Agda standard library
--
-- Freely adding Extrema to any Set
------------------------------------------------------------------------

module Relation.Binary.Construction.Extrema where

open import Relation.Binary.Construction.Infimum as Infimum   using (_₋)
open import Relation.Binary.Construction.Supremum as Supremum using (_⁺)

_± : ∀ {a} → Set a → Set a
A ± = A ₋ ⁺

pattern ⊥⁺    = Supremum.[ Infimum.⊥⁺ ]
pattern [_] k = Supremum.[ Infimum.[ k ] ]
pattern ⊤⁺    = Supremum.⊤⁺
