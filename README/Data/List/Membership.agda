------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for List membership
------------------------------------------------------------------------

module README.Data.List.Membership where

open import Data.Char.Base using (Char; fromℕ)
open import Data.Char.Properties as CharProp hiding (setoid)
open import Data.Nat as ℕ using (ℕ; _+_; _<_; s≤s; z≤n; _*_; _∸_; _≤_)
open import Data.List.Base using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; setoid)

------------------------------------------------------------------------
-- Membership

-- Membership of a list is simply a special case of `Any` where
-- `x ∈ xs` is defined as `Any (x ≈_) xs`.

-- Just like pointwise equality of lists, the exact membership module
-- that should be used depends on whether the equality on the
-- underlying elements of the list is i) propositional or setoid-based
-- and ii) decidable.

import Data.List.Membership.Setoid as SetoidMembership
import Data.List.Membership.DecSetoid as DecSetoidMembership
import Data.List.Membership.Propositional as PropMembership
import Data.List.Membership.DecPropositional as DecPropMembership

-- For example if we want to reason about membership for `List ℕ`
-- then you would use the `DecSetoidMembership` as we use
-- propositional equality over `ℕ` and it is also decidable. Therefore
-- the module `DecPropMembership` should be opened as follows:

open DecPropMembership ℕ._≟_

-- As membership is just an instance of `Any` we also need to import
-- the constructors `here` and `there`. (See issue #553 on Github for
-- why we're struggling to have `here` and `there` automatically
-- re-exported by the membership modules).

open import Data.List.Relation.Unary.Any using (here; there)

-- These modules provide the infix notation `_∈_` which can be used
-- as follows:

lem₁ : 1 ∈ 2 ∷ 1 ∷ 3 ∷ []
lem₁ = there (here refl)

-- Properties of the membership relation can be found in the following
-- two files:

import Data.List.Membership.Setoid.Properties as SetoidProperties
import Data.List.Membership.Propositional.Properties as PropProperties

-- As of yet there are no corresponding files for properties of
-- membership for decidable versions of setoid and propositional
-- equality as we have no properties that only hold when equality is
-- decidable.

-- These `Properties` modules are NOT parameterised in the same way as
-- the main membership modules as some of the properties relate
-- membership proofs for lists of different types. For example in the
-- following the first `∈` refers to lists of type `List ℕ` whereas
-- the second `∈` refers to lists of type `List Char`.

open DecPropMembership CharProp._≟_ renaming (_∈_ to _∈ᶜ_)
open SetoidProperties using (∈-map⁺)

lem₂ : {v : ℕ} {xs : List ℕ} → v ∈ xs → fromℕ v ∈ᶜ map fromℕ xs
lem₂ = ∈-map⁺ (setoid ℕ) (setoid Char) (cong fromℕ)
