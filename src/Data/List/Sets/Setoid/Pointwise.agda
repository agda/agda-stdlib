------------------------------------------------------------------------
-- The Agda standard library
--
-- a sublist relation by instantiating subset structures using setoid over pointwise equality.
------------------------------------------------------------------------

open import Relation.Binary hiding (Decidable)

module Data.List.Sets.Setoid.Pointwise {a ℓ} (S : Setoid a ℓ) where

open import Data.List.Sets.Setoid S
open Setoid S renaming (Carrier to A)

open import Data.List.Base using (List ; [] ; _∷_ ; filter)
open import Data.List.Relation.Pointwise as PW using (Pointwise ; [] ; _∷_)
open import Data.List.Relation.Equality.Setoid S using (_≋_ ; ≋-isEquivalence) public

open import Data.List.All
open import Data.List.Any

open import Data.List.Membership.Setoid.Properties
open import Data.List.Sets.Setoid.Structures
open import Data.List.Sets.Setoid.Properties

import Data.List.Membership.Setoid as Membership

open Membership S

⊆-reflexive : _≋_ ⇒ _⊆_
⊆-reflexive xs≋ys = ∈-resp-≋ S xs≋ys

⊆′-reflexive : _≋_ ⇒ _⊆′_
⊆′-reflexive []            = []
⊆′-reflexive (x∼y ∷ xs≋ys) = here x∼y ∷ ⊆′-growʳ S (⊆′-reflexive xs≋ys)

open ⊆-Structs S ≋-isEquivalence ⊆-reflexive public
open ⊆′-Structs S ≋-isEquivalence ⊆′-reflexive public

------------------------------------------------------------------------
-- filter

open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Decidable)

module _ {p} {P : A → Set p} (P? : Decidable P) where

  filter⁺ : ∀ xs → filter P? xs ⊆ xs
  filter⁺ []       ()
  filter⁺ (x ∷ xs) y∈f[x∷xs] with P? x
  ... | no  _ = there (filter⁺ xs y∈f[x∷xs])
  ... | yes _ with y∈f[x∷xs]
  ...   | here  y≈x     = here y≈x
  ...   | there y∈f[xs] = there (filter⁺ xs y∈f[xs])
