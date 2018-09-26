------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional sublist-related properties
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Inductive.Propositional.Properties where

import Data.List.Base as List
open import Data.List.Any using (here; there)
open import Data.List.Any.Properties using (here-injective; there-injective)
open import Data.List.Membership.Propositional
import Data.List.Relation.Sublist.Inductive.Setoid as Sublist
import Data.List.Relation.Sublist.Inductive.Setoid.Properties as SublistProp
import Function.Injection as Inj
import Function.Bijection as Bij
open import Relation.Binary.PropositionalEquality

private open module S {a} {A : Set a} = Sublist (setoid A)

-- We re-exports all the properties obtained for setoids except for the ones which
-- can be specialized further.

open module SProp {a} {A : Set a} = SublistProp (setoid A)
  hiding (map⁺; map⁻)
  public

-- We provide specialized versions of the properties we can simplify

module _ {a b} {A : Set a} {B : Set b} where

  map⁺ : ∀ {xs ys} (f : A → B) → xs ⊆ ys → List.map f xs ⊆ List.map f ys
  map⁺ f = SProp.map⁺ (setoid _) (cong f)

  open Inj.Injection

  map⁻ : ∀ {xs ys} (inj : A Inj.↣ B) →
         List.map (inj ⟨$⟩_) xs ⊆ List.map (inj ⟨$⟩_) ys → xs ⊆ ys
  map⁻ = SProp.map⁻ (setoid _)

-- We provide additional properties we can't handle (yet) in the general
-- setoid case


------------------------------------------------------------------------
-- The `loookup` function induced by a proof that `xs ⊆ ys` is injective

module _ {a} {A : Set a} where

  lookup-injective : ∀ {x : A} {xs ys} {p : xs ⊆ ys} {v w : x ∈ xs} →
                     lookup p v ≡ lookup p w → v ≡ w
  lookup-injective {p = skip p} {v} {w} eq =
    lookup-injective (there-injective eq)
  lookup-injective {p = keep refl p} {here px} {here qx} eq =
    cong here (≡-irrelevance _ _)
  lookup-injective {p = keep refl p} {there v} {there w} eq =
    cong there (lookup-injective (there-injective eq))
  -- impossible cases
  lookup-injective {p = keep refl p} {here px} {there w} ()
  lookup-injective {p = keep refl p} {there v} {here qx} ()
  lookup-injective {p = base} {}

------------------------------------------------------------------------
-- The singleton list being a sublist of xs is isomorphic to its element
-- belonging to xs.

  [x]⊆xs↔x∈xs : ∀ {x : A} {xs} → (List.[ x ] ⊆ xs) Bij.⤖ (x ∈ xs)
  [x]⊆xs↔x∈xs {x} = Bij.bijection to∈ from∈ (to∈-injective _ _) to∈∘from∈≗id

    where

    to∈-injective : ∀ {xs x} (p q : List.[ x ] ⊆ xs) → to∈ p ≡ to∈ q → p ≡ q
    to∈-injective (skip p) (skip q) eq =
      cong skip (to∈-injective p q (there-injective eq))
    to∈-injective (keep eq₁ p) (keep eq₂ q) eq =
      cong₂ keep (≡-irrelevance eq₁ eq₂) ([]⊆-irrelevant p q)
    to∈-injective (skip p) (keep eq q) ()
    to∈-injective (keep eq p) (skip q) ()

    to∈∘from∈≗id : ∀ {xs} (p : x ∈ xs) → to∈ (from∈ p) ≡ p
    to∈∘from∈≗id (here refl) = refl
    to∈∘from∈≗id (there p)   = cong there (to∈∘from∈≗id p)

