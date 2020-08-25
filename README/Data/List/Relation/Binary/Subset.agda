------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for subset relations over `List`s
------------------------------------------------------------------------

module README.Data.List.Relation.Binary.Subset where


open import Relation.Binary
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-insert)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Membership.Setoid as S using (_∈_)
open import Data.List.Relation.Binary.Subset.Setoid using (_|>_)
open import Data.List.Membership.Setoid.Properties using (∈-resp-≈)
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------
-- Subset Relation

-- The Subset relation is a wrapper over `Any` and so is parameterized over an
-- equality relation. Thus to use the subset relation we must tell Agda which
-- equality relation to use.

import Data.List.Membership.DecPropositional as DecPropMembership

open import Data.String using (_≟_) -- Decidable equality over Strings
open DecPropMembership _≟_          -- Open the decidable membership module
                                    -- using Decidable ≡ over Strings


-- Simple cases are inductive proofs

open import Data.List.Relation.Unary.Any using (here; there)

lem₁ : ∀ {x : Set} {xs : List x} → xs ⊆ xs
lem₁ p = p

lem₂ : "A" ∷ [] ⊆ "B" ∷ "A" ∷ []
lem₂ p = there p

-- Or directly use the definition of subsets

lem₃₀ : "E" ∷ "S" ∷ "B" ∷ [] ⊆ "S" ∷ "U" ∷ "B" ∷ "S" ∷ "E" ∷ "T" ∷ []
lem₃₀ (here refl) = there (there (there (there (here refl))))  -- the "E" case
lem₃₀ (there (here refl)) = here refl                          -- "S"
lem₃₀ (there (there (here refl))) = there (there (here refl))  -- "B"

-- Or use the properties from `Data.List.Membership.Propositional.Properties`

lem₄ : "A" ∷  [] ⊆ "B" ∷ "A" ∷ "C" ∷ []
lem₄ p = ∈-++⁺ˡ (there p)

lem₅ : "B" ∷ "S" ∷ "E" ∷ [] ⊆ "S" ∷ "U" ∷ "B" ∷ "S" ∷ "E" ∷ "T" ∷ []
lem₅ p = ∈-++⁺ˡ (there (there p))

lem₃₁ : "E" ∷ "S" ∷ "B" ∷ [] ⊆ "S" ∷ "U" ∷ "B" ∷ "S" ∷ "E" ∷ "T" ∷ []
lem₃₁ (here refl) = ∈-insert ("S" ∷ "U" ∷ "B" ∷ "S" ∷ [])
lem₃₁ (there (here refl)) = here refl
lem₃₁ (there (there (here refl))) = ∈-insert ("S" ∷ "U" ∷ [])

-- the _|>_ operator from Data.List.Relation.Binary.Subset.Setoid is useful for
-- writing more elegant proofs

lem₃₂ : "E" ∷ "S" ∷ "B" ∷ [] ⊆ "S" ∷ "U" ∷ "B" ∷ "S" ∷ "E" ∷ "T" ∷ []
lem₃₂ = ∈-insert ("S" ∷ "U" ∷ "B" ∷ "S" ∷ [])
        |> here refl
        |> ∈-insert ("S" ∷ "U" ∷ []) |> λ ()
