------------------------------------------------------------------------
-- The Agda standard library
--
-- A subset relation defined over induced equivalence relation over _⊆_ and _⊆′_
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Sets.Setoid.Subset {a ℓ} (S : Setoid a ℓ) where

open import Data.List
open import Data.Product

open import Data.List.Sets.Setoid.Structures
open import Data.List.Sets.Setoid.Properties

open import Relation.Binary.InducedStructures

open import Data.List.Sets.Setoid S
open Setoid S renaming (Carrier to A)

-- induced from _⊆_

≋-setoid : Setoid _ _
≋-setoid = InducedSetoid _⊆_ (⊆-refl S) (⊆-trans S)

-- set equivalence relation
open Setoid ≋-setoid using ()
  renaming (_≈_ to _≋_ ; isEquivalence to ≋-isEquivalence) public

∈-resp-≋ : ∀ {x} → (x ∈_) Respects _≋_
∈-resp-≋ (xs⊆ys , _) x∈xs = ∈-resp-⊆ S xs⊆ys x∈xs

private
  ⊆-preorder : Preorder _ _ _
  ⊆-preorder = InducedPreorder _⊆_ (⊆-refl S) (⊆-trans S)

open Preorder ⊆-preorder using () renaming (reflexive to ⊆-reflexive) public
open ⊆-Structs S ≋-isEquivalence ⊆-reflexive public

⊆-poset : Poset _ _ _
⊆-poset = InducedPoset _⊆_ (⊆-refl S) (⊆-trans S)

⊂-strictPartialOrder : StrictPartialOrder _ _ _
⊂-strictPartialOrder = InducedStrictPartialOrder _⊆_ (⊆-refl S) (⊆-trans S)

-- induced from _⊆′_

≋′-setoid : Setoid _ _
≋′-setoid = InducedSetoid _⊆′_ (⊆′-refl S) (⊆′-trans S)

-- set equivalence relation
open Setoid ≋′-setoid using ()
  renaming (_≈_ to _≋′_ ; isEquivalence to ≋′-isEquivalence) public

∈-resp-≋′ : ∀ {x} → (x ∈_) Respects _≋′_
∈-resp-≋′ (xs⊆ys , _) x∈xs = ∈-resp-⊆′ S xs⊆ys x∈xs

private
  ⊆′-preorder′ : Preorder _ _ _
  ⊆′-preorder′ = InducedPreorder _⊆′_ (⊆′-refl S) (⊆′-trans S)

open Preorder ⊆′-preorder′ using () renaming (reflexive to ⊆′-reflexive) public
open ⊆′-Structs S ≋′-isEquivalence ⊆′-reflexive public

⊆′-poset : Poset _ _ _
⊆′-poset = InducedPoset _⊆′_ (⊆′-refl S) (⊆′-trans S)

⊂′-strictPartialOrder : StrictPartialOrder _ _ _
⊂′-strictPartialOrder = InducedStrictPartialOrder _⊆′_ (⊆′-refl S) (⊆′-trans S)
