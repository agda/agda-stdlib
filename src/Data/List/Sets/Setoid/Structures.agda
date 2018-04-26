------------------------------------------------------------------------
-- The Agda standard library
--
-- there are a number of relations that can be derived froom ⊆ and an equivalence
-- relation that is defined over List of the Carrier of the setoid, as long as they
-- are compatible.
------------------------------------------------------------------------

module Data.List.Sets.Setoid.Structures where

open import Relation.Binary
open import Relation.Nullary using (¬_)

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.List.Sets.Setoid.Properties

open import Data.List.Any using (Any; here; there)
open import Data.List.All
open import Data.Product

import Data.List.Sets.Setoid as Sets
import Relation.Binary.PreorderReasoning as PreorderReasoning

module _ {c ℓ} (S : Setoid c ℓ) where
  open Sets S
  open Setoid S

  module ⊆-Structs {ℓ′}
    {_≋_     : Rel (List Carrier) ℓ′} -- the equivalence relation
    (≋-equiv : IsEquivalence _≋_)
    (⊆-reflexive : _≋_ ⇒ _⊆_) -- we need _≋_ is compatible, up to reflexivity of _⊆_
    where

    infix 4 _⊂_ _⊄_

    _⊂_ : Rel (List Carrier) _
    xs ⊂ ys = xs ⊆ ys × ¬ xs ≋ ys

    _⊄_ : Rel (List Carrier) _
    xs ⊄ ys = ¬ xs ⊂ ys

    ⊆-isPreorder : IsPreorder _≋_ _⊆_
    ⊆-isPreorder = record
      { isEquivalence = ≋-equiv
      ; reflexive     = ⊆-reflexive
      ; trans         = ⊆-trans S
      }

    ⊆-preorder : Preorder _ _ _
    ⊆-preorder = record
      { isPreorder = ⊆-isPreorder
      }

    -- Reasoning over subsets
    module ⊆-Reasoning where
      open PreorderReasoning ⊆-preorder public renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

      infix 1 _∈⟨_⟩_
      _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
      x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs


  -- very similar to above, but just defined over _⊆_
  module ⊆′-Structs {ℓ′}
    {_≋_     : Rel (List Carrier) ℓ′} -- the equivalence relation
    (≋-equiv : IsEquivalence _≋_)
    (⊆′-reflexive : _≋_ ⇒ _⊆′_) -- we need _≋_ is compatible, up to reflexivity of _⊆′_
    where

    infix 4 _⊂′_ _⊄′_

    _⊂′_ : Rel (List Carrier) _
    xs ⊂′ ys = xs ⊆′ ys × ¬ xs ≋ ys

    _⊄′_ : Rel (List Carrier) _
    xs ⊄′ ys = ¬ xs ⊂′ ys

    ⊆′-isPreorder : IsPreorder _≋_ _⊆′_
    ⊆′-isPreorder = record
      { isEquivalence = ≋-equiv
      ; reflexive     = ⊆′-reflexive
      ; trans         = ⊆′-trans S
      }

    ⊆′-preorder : Preorder _ _ _
    ⊆′-preorder = record
      { isPreorder = ⊆′-isPreorder
      }

    -- Reasoning over subsets
    module ⊆′-Reasoning where
      open PreorderReasoning ⊆′-preorder public renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

      infix 1 _∈⟨_⟩_
      _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
      x ∈⟨ x∈xs ⟩ xs⊆ys = ∈-resp-⊆′ S (begin xs⊆ys) x∈xs
