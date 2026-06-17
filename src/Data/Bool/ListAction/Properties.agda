------------------------------------------------------------------------
-- The Agda standard library
--
-- Booleans: properties of conjunction and disjunction of lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Bool.ListAction.Properties where

open import Data.Bool.Base
open import Data.Bool.Properties
open import Data.Bool.ListAction
open import Data.List.Base hiding (and; or; all; any)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭⇒↭ₛ)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as ↭
open import Data.List.Relation.Binary.Permutation.Setoid.Properties
open import Data.List.Relation.Unary.Any using (here; there)
open import Function.Base using (_∘′_)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

------------------------------------------------------------------------
-- Properties

-- and

and-++ : ∀ bs cs → and (bs ++ cs) ≡ and bs ∧ and cs
and-++ [] cs = refl
and-++ (b ∷ bs) cs = begin
  b ∧ and (bs ++ cs)    ≡⟨ cong (b ∧_) (and-++ bs cs) ⟩
  b ∧ (and bs ∧ and cs) ≡⟨ ∧-assoc b (and bs) (and cs) ⟨
  (b ∧ and bs) ∧ and cs ∎
  where open ≡-Reasoning

∨-distribˡ-and : ∀ b cs → b ∨ and cs ≡ all (b ∨_) cs
∨-distribˡ-and b [] = ∨-zeroʳ b
∨-distribˡ-and b (c ∷ cs) = trans (∨-distribˡ-∧ b c (and cs)) (cong ((b ∨ c) ∧_) (∨-distribˡ-and b cs))

∨-distribʳ-and : ∀ b cs → and cs ∨ b ≡ all (_∨ b) cs
∨-distribʳ-and b [] = ∨-zeroˡ b
∨-distribʳ-and b (c ∷ cs) = trans (∨-distribʳ-∧ b c (and cs)) (cong ((c ∨ b) ∧_) (∨-distribʳ-and b cs))

and-↭ : and Preserves _↭_ ⟶ _≡_
and-↭ p = foldr-commMonoid ≡-setoid ∧-isCommutativeMonoid (↭⇒↭ₛ p)

and-locate : ∀ bs → and bs ≡ false → false ∈ bs
and-locate (false ∷ bs) p = here refl
and-locate (true ∷ bs) p = there (and-locate bs p)

-- or

or-++ : ∀ bs cs → or (bs ++ cs) ≡ or bs ∨ or cs
or-++ [] cs = refl
or-++ (b ∷ bs) cs = begin
  b ∨ or (bs ++ cs)   ≡⟨ cong (b ∨_) (or-++ bs cs) ⟩
  b ∨ (or bs ∨ or cs) ≡⟨ ∨-assoc b (or bs) (or cs) ⟨
  (b ∨ or bs) ∨ or cs ∎
  where open ≡-Reasoning

∧-distribˡ-or : ∀ b cs → b ∧ or cs ≡ any (b ∧_) cs
∧-distribˡ-or b [] = ∧-zeroʳ b
∧-distribˡ-or b (c ∷ cs) = trans (∧-distribˡ-∨ b c (or cs)) (cong ((b ∧ c) ∨_) (∧-distribˡ-or b cs))

∧-distribʳ-or : ∀ b cs → or cs ∧ b ≡ any (_∧ b) cs
∧-distribʳ-or b [] = ∧-zeroˡ b
∧-distribʳ-or b (c ∷ cs) = trans (∧-distribʳ-∨ b c (or cs)) (cong ((c ∧ b) ∨_) (∧-distribʳ-or b cs))

or-↭ : or Preserves _↭_ ⟶ _≡_
or-↭ p = foldr-commMonoid ≡-setoid ∨-isCommutativeMonoid (↭⇒↭ₛ p)

or-locate : ∀ bs → or bs ≡ true → true ∈ bs
or-locate (false ∷ bs) p = there (or-locate bs p)
or-locate (true ∷ bs) p = here p

-- all

all-↭ : ∀ {a} {A : Set a} (p : A → Bool) → all p Preserves _↭_ ⟶ _≡_
all-↭ p = and-↭ ∘′ ↭.map⁺ p

-- any

any-↭ : ∀ {a} {A : Set a} (p : A → Bool) → any p Preserves _↭_ ⟶ _≡_
any-↭ p = or-↭ ∘′ ↭.map⁺ p
