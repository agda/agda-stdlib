------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for subset relations over `List`s
------------------------------------------------------------------------

module README.Data.List.Relation.Binary.Subset where

open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List using (List; _∷_; [])

------------------------------------------------------------------------
-- Subset Relation

-- The Subset relation is a wrapper over `Any` and so is parameterized over an
-- equality relation. Thus to use the subset relation we must tell agda which
-- equality relation to use.

import Data.List.Membership.DecPropositional as DecPropMembership

open import Data.String using (_≟_) -- Decidable equality over Strings
open DecPropMembership _≟_          -- Open the decidable membership module
                                    -- using Decidable ≡ over Strings


-- Simple cases are just inductive proofs

open import Data.List.Relation.Unary.Any using (there)

lem₁ : ∀ {x : Set} {xs : List x} → xs ⊆ xs
lem₁ p = p

lem₂ : "A" ∷ [] ⊆ "B" ∷ "A" ∷ []
lem₂ p = there p

-- For anything more complicated then basic use cases see
-- `Data.List.Membership.Propositional.Properties` for useful properties

lem₃ : "A" ∷  [] ⊆ "B" ∷ "A" ∷ "C" ∷ []
lem₃ p = ∈-++⁺ˡ (there p)

lem₄ : "A" ∷  [] ⊆ "A" ∷ "B" ∷ "C" ∷ []
lem₄ p = ∈-++⁺ˡ p
