------------------------------------------------------------------------
-- The Agda standard library
--
-- The 'top' view of Fin
--
-- This is an example of a view of (elements of) a datatype,
-- here i : Fin (suc n), which exhibits every such i as
-- * either, i = fromℕ n
-- * or, i = inject₁ j for a unique j : Fin n
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Relation.Unary.Top where

open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁; inject₁ℕ<)
open import Relation.Binary.PropositionalEquality

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The View, considered as a unary relation on Fin (suc n)

-- NB `Data.Fin.Properties.fromℕ≢inject₁` establishes that the following
-- inductively defined family on `Fin (suc n)` has constructors which
-- target *disjoint* instances of the family; and hence the interpretations
-- of the View constructors will also be disjoint

data View : (i : Fin (suc n)) → Set where

  top :                View (fromℕ n)
  inj : (j : Fin n) → View (inject₁ j)

-- The view covering function, witnessing soundness of the view

view : ∀ {n} i → View {n} i
view {n = zero}  zero    = top
view {n = suc _} zero    = inj _
view {n = suc n} (suc i) with view {n} i
... | top   = top
... | inj j = inj (suc j)

-- Interpretation of the view constructors

⟦_⟧ : ∀ {i} → View {n} i → Fin (suc n)
⟦ top ⟧   = fromℕ _
⟦ inj j ⟧ = inject₁ j

-- Completeness of the view

view-complete : ∀ {i} (v : View {n} i) → ⟦ v ⟧ ≡ i
view-complete top     = refl
view-complete (inj j) = refl

-- 'Computational' behaviour of the covering function

view-top : ∀ n → view {n} (fromℕ n) ≡ top
view-top zero    = refl
view-top (suc n) rewrite view-top n = refl

view-inj : ∀ j → view {n} (inject₁ j) ≡ inj j
view-inj zero       = refl
view-inj (suc j) rewrite view-inj j = refl

------------------------------------------------------------------------
-- Experimental
--
-- Because we work --without-K, Agda's unifier will complain about
-- attempts to match `refl` against hypotheses of the form
--    `view {n] i ≡ v`
-- or gets stuck trying to solve unification problems of the form
--    (inferred index ≟ expected index)
-- even when these problems are *provably* solvable.
--
-- So the two predicates on values of the view defined below
-- are extensionally equivalent to the assertions
-- `view {n] i ≡ top` and `view {n] i ≡ inj j`
--
-- But such assertions can only ever have a unique (irrelevant) proof
-- so we introduce instances to witness them, themselves given in
-- terms of the functions `view-top` and `view-inj` defined above

module Instances {n} where

  private

    lemma : n ≡ toℕ (inject₁ (fromℕ n))
    lemma = sym (begin
      toℕ (inject₁ (fromℕ n)) ≡⟨ toℕ-inject₁ (fromℕ n) ⟩
      toℕ (fromℕ n)           ≡⟨ toℕ-fromℕ n ⟩
      n                         ∎) where open ≡-Reasoning

  data IsTop : ∀ {i} → View {n} i → Set where

    top : IsTop top

  instance

    top⁺ : IsTop {i = fromℕ n} (view (fromℕ n))
    top⁺ rewrite view-top n = top

  data IsInj : ∀ {i} → View {n} i → Set where

    inj : ∀ j → IsInj (inj j)

  instance

    inj⁺ : ∀ {j} → IsInj (view (inject₁ j))
    inj⁺ {j} rewrite view-inj j = inj j

    inject₁≡⁺ : ∀ {i} {j} {eq : inject₁ i ≡ j} → IsInj (view j)
    inject₁≡⁺ {eq = refl} = inj⁺

    inject₁≢n⁺ : ∀ {i} {n≢i : n ≢ toℕ (inject₁ i)} → IsInj (view {n} i)
    inject₁≢n⁺ {i} {n≢i} with view i
    ... | top with () ← n≢i lemma
    ... | inj j = inj j

open Instances

------------------------------------------------------------------------
-- As a corollary, we obtain two useful properties, which are
-- witnessed by, but can also serve as proxy replacements for,
-- the corresponding properties in `Data.Fin.Properties`

view-top-toℕ : ∀ i → .{{IsTop (view i)}} → toℕ i ≡ n
view-top-toℕ {n = n} i with top ← view i = toℕ-fromℕ n

view-inj-toℕ< : ∀ i → .{{IsInj (view i)}} → toℕ i < n
view-inj-toℕ< i with inj j ← view i = inject₁ℕ< j

