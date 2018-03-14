------------------------------------------------------------------------
-- The Agda standard library
--
-- Data.List.Any.Membership instantiated with propositional equality,
-- along with some additional definitions.
------------------------------------------------------------------------

module Data.List.Membership.Propositional {a} {A : Set a} where

open import Data.List.Any using (Any)
import Data.List.Membership.Setoid as SetoidMembership
open import Relation.Binary.PropositionalEquality using (setoid; subst)

------------------------------------------------------------------------
-- Re-export contents of setoid membership

open SetoidMembership (setoid A) public hiding (lose)

------------------------------------------------------------------------
-- Other operations

lose : ∀ {p} {P : A → Set p} {x xs} → x ∈ xs → P x → Any P xs
lose = SetoidMembership.lose (setoid A) (subst _)
