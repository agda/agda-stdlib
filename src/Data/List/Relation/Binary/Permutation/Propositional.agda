------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition for the permutation relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional
  {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Binary.Equality.Propositional using (_≋_; ≋⇒≡)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Binary.Reasoning.Syntax

import Data.List.Relation.Binary.Permutation.Setoid as Permutation

private
  variable
    x y z v w : A
    ws xs ys zs : List A

------------------------------------------------------------------------
-- An inductive definition of permutation

-- Note that one would expect that this would be defined in terms of
-- `Permutation.Setoid`. This is not currently the case as it involves
-- adding in a bunch of trivial `_≡_` proofs to the constructors which
-- a) adds noise and b) prevents easy access to the variables `x`, `y`.
-- This may be changed in future when a better solution is found.

infix 3 _↭_

data _↭_ : Rel (List A) a where
  refl  : xs ↭ xs
  prep  : ∀ x → xs ↭ ys → x ∷ xs ↭ x ∷ ys
  swap  : ∀ x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  trans : xs ↭ ys → ys ↭ zs → xs ↭ zs

-- Constructor aliases

↭-refl : Reflexive _↭_
↭-refl = refl

↭-prep  : ∀ x → xs ↭ ys → x ∷ xs ↭ x ∷ ys
↭-prep = prep

↭-swap  : ∀ x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
↭-swap = swap

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = ↭-refl

↭-reflexive-≋ : _≋_ ⇒ _↭_
↭-reflexive-≋ xs≋ys = ↭-reflexive (≋⇒≡ xs≋ys)

↭-sym : xs ↭ ys → ys ↭ xs
↭-sym refl                = refl
↭-sym (prep x xs↭ys)      = prep x (↭-sym xs↭ys)
↭-sym (swap x y xs↭ys)    = swap y x (↭-sym xs↭ys)
↭-sym (trans xs↭ys ys↭zs) = trans (↭-sym ys↭zs) (↭-sym xs↭ys)

-- A smart version of trans that avoids unnecessary `refl`s (see #1113).
↭-trans : Transitive _↭_
↭-trans refl ρ₂ = ρ₂
↭-trans ρ₁ refl = ρ₁
↭-trans ρ₁ ρ₂   = trans ρ₁ ρ₂

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = record
  { refl  = ↭-refl
  ; sym   = ↭-sym
  ; trans = ↭-trans
  }

↭-setoid : Setoid _ _
↭-setoid = record
  { isEquivalence = ↭-isEquivalence
  }

------------------------------------------------------------------------
-- _↭_ is finer than `Setoid`-based permutation for any equivalence on A

module _ {ℓ} {_≈_ : Rel A ℓ} (isEquivalence : IsEquivalence _≈_) where

  private
    open module ↭ₛ′ = Permutation record { isEquivalence = isEquivalence }
      using ()
      renaming (_↭_ to _↭ₛ′_)

  ↭⇒↭ₛ′ : _↭_ ⇒ _↭ₛ′_
  ↭⇒↭ₛ′ refl         = ↭ₛ′.↭-refl
  ↭⇒↭ₛ′ (prep x p)   = ↭ₛ′.↭-prep x (↭⇒↭ₛ′ p)
  ↭⇒↭ₛ′ (swap x y p) = ↭ₛ′.↭-swap x y (↭⇒↭ₛ′ p)
  ↭⇒↭ₛ′ (trans p q)  = ↭ₛ′.↭-trans′ (↭⇒↭ₛ′ p) (↭⇒↭ₛ′ q)


------------------------------------------------------------------------
-- _↭_ is equivalent to `Setoid`-based permutation on `≡.setoid A`

private
  open module ↭ₛ = Permutation (≡.setoid A)
    using ()
    renaming (_↭_ to _↭ₛ_)

↭⇒↭ₛ : _↭_ ⇒ _↭ₛ_
↭⇒↭ₛ = ↭⇒↭ₛ′ ≡.isEquivalence

↭ₛ⇒↭ : _↭ₛ_ ⇒ _↭_
↭ₛ⇒↭ (↭ₛ.refl xs≋ys)       = ↭-reflexive-≋ xs≋ys
↭ₛ⇒↭ (↭ₛ.prep refl p)      = ↭-prep _ (↭ₛ⇒↭ p)
↭ₛ⇒↭ (↭ₛ.swap refl refl p) = ↭-swap _ _ (↭ₛ⇒↭ p)
↭ₛ⇒↭ (↭ₛ.trans p q)        = ↭-trans (↭ₛ⇒↭ p) (↭ₛ⇒↭ q)


------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs and allow "zooming in"
-- to localised reasoning.

module PermutationReasoning where

  private module Base = EqReasoning ↭-setoid

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)
    renaming (≈-go to ↭-go)

  open ↭-syntax _IsRelatedTo_ _IsRelatedTo_ ↭-go ↭-sym public
