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

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Relation.Unary.Top where

open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁; inject₁ℕ<)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    n : ℕ
    i : Fin (suc n)
    j : Fin n

------------------------------------------------------------------------
-- The View, considered as a unary relation on Fin n

-- NB `Data.Fin.Properties.fromℕ≢inject₁` establishes that the following
-- inductively defined family on `Fin n` has constructors which target
-- *disjoint* instances of the family (at index {suc n}); and hence the
-- interpretations of the View constructors will also be disjoint

data View : ∀ {n} (j : Fin n) → Set where
  top : View (fromℕ n)
  inj : {j : Fin n} → View j → View (inject₁ j)

pattern inj₁ {n} j = inj {n = n} {j = j} _

-- The view covering function, witnessing soundness of the view

view-zero : ∀ n → View {suc n} zero
view-zero zero    = top
view-zero (suc n) = inj (view-zero n)

view : ∀ j → View {n} j
view {n = suc n} zero    = view-zero n
view {n = suc n} (suc i) with view {n} i
... | top    = top
... | inj₁ j = inj (view (suc j))

-- Interpretation of the view constructors

⟦_⟧ : View {n} j → Fin n
⟦ top ⟧    = fromℕ _
⟦ inj₁ j ⟧ = inject₁ j

-- Completeness of the view

view-complete : (v : View {n} j) → ⟦ v ⟧ ≡ j
view-complete top     = refl
view-complete (inj _) = refl

-- 'Computational' behaviour of the covering function

view-top : ∀ n → view (fromℕ n) ≡ top
view-top zero                       = refl
view-top (suc n) rewrite view-top n = refl

view-inj : ∀ j → view (inject₁ j) ≡ inj (view {n} j)
view-inj zero                       = refl
view-inj (suc j) rewrite view-inj j = refl

------------------------------------------------------------------------
-- Experimental
--
-- Because we work --without-K, Agda's unifier will complain about
-- attempts to match `refl` against hypotheses of the form
--    `view {n} i ≡ v`
-- or gets stuck trying to solve unification problems of the form
--    (inferred index ≟ expected index)
-- even when these problems are *provably* solvable.
--
-- So the two predicates on values of the view defined below
-- are extensionally equivalent to the assertions
-- `view {n} i ≡ top` and `view {n} i ≡ inj₁ j`
--
-- But such assertions can only ever have a unique (irrelevant) proof
-- so we introduce instances to witness them, themselves given in
-- terms of the functions `view-top` and `view-inj` defined above

module Instances {n} where

  data IsTop : View {suc n} i → Set where
    top : IsTop top

  instance

    top⁺ : IsTop (view (fromℕ n))
    top⁺ rewrite view-top n = top

  data IsInj : View {suc n} i → Set where
    inj : ∀ {j} (v : View {n} j) → IsInj (inj v)

  instance

    inj⁺ : IsInj (view (inject₁ j))
    inj⁺ {j} rewrite view-inj j = inj _

    inject₁≡⁺ : {eq : inject₁ j ≡ i} → IsInj (view i)
    inject₁≡⁺ {eq = refl} = inj⁺

    inject₁≢n⁺ : {n≢i : n ≢ toℕ (inject₁ i)} → IsInj (view i)
    inject₁≢n⁺ {i} {n≢i} with view i
    ... | top = contradiction n≡i n≢i
      where
        open ≡-Reasoning
        n≡i : n ≡ toℕ (inject₁ (fromℕ n))
        n≡i = sym (begin
          toℕ (inject₁ (fromℕ n)) ≡⟨ toℕ-inject₁ (fromℕ n) ⟩
          toℕ (fromℕ n)           ≡⟨ toℕ-fromℕ n ⟩
          n                         ∎)
    ... | inj v = inj v

open Instances

------------------------------------------------------------------------
-- As a corollary, we obtain two useful properties, which are
-- witnessed by, but can also serve as proxy replacements for,
-- the corresponding properties in `Data.Fin.Properties`

view-top-toℕ : ∀ i → .{{IsTop (view i)}} → toℕ i ≡ n
view-top-toℕ {n = n} i with top ← view i = toℕ-fromℕ n

view-inj-toℕ< : ∀ i → .{{IsInj (view i)}} → toℕ i < n
view-inj-toℕ< i with inj₁ j ← view i = inject₁ℕ< j

