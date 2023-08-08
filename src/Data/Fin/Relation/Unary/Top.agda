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
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    n : ℕ
    i : Fin (suc n)
    j : Fin n

------------------------------------------------------------------------
-- The View, considered as a unary relation on Fin (suc n)

-- NB `Data.Fin.Properties.fromℕ≢inject₁` establishes that the following
-- inductively defined family on `Fin (suc n)` has constructors which
-- target *disjoint* instances of the family; and hence the interpretations
-- of the View constructors will also be disjoint

data View : ∀ {n} (j : Fin n) → Set where
  ‵fromℕ : View (fromℕ n)
  ‵inj₁ : {j : Fin n} → View j → View (inject₁ j)

pattern ‵inject₁ {n} j = ‵inj₁ {n = n} {j = j} _

-- The view covering function, witnessing soundness of the view

view-zero : ∀ n → View {suc n} zero
view-zero zero    = ‵fromℕ
view-zero (suc n) = ‵inj₁ (view-zero n)

view : ∀ j → View {n} j
view {n = suc n} zero = view-zero n
view {n = suc n} (suc i) with view {n} i
... | ‵fromℕ  = ‵fromℕ
... | ‵inject₁ j = ‵inj₁ (view (suc j))

-- Interpretation of the view constructors

⟦_⟧ : View {n} j → Fin n
⟦ ‵fromℕ ⟧     = fromℕ _
⟦ ‵inject₁ j ⟧ = inject₁ j

-- Completeness of the view

view-complete : (v : View {n} j) → ⟦ v ⟧ ≡ j
view-complete ‵fromℕ    = refl
view-complete (‵inj₁ _) = refl

-- 'Computational' behaviour of the covering function

view-fromℕ : ∀ n → view {suc n} (fromℕ n) ≡ ‵fromℕ
view-fromℕ zero                         = refl
view-fromℕ (suc n) rewrite view-fromℕ n = refl

view-inject₁ : ∀ j → view {suc n} (inject₁ j) ≡ ‵inj₁ (view {n} j)
view-inject₁ zero                           = refl
view-inject₁ (suc j) rewrite view-inject₁ j = refl

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
-- `view {n} i ≡ ‵fromℕ` and `view {n} i ≡ ‵inject₁ j`
--
-- But such assertions can only ever have a unique (irrelevant) proof
-- so we introduce instances to witness them, themselves given in
-- terms of the functions `view-fromℕ` and `view-inject₁` defined above

module Instances {n} where

  data IsFromℕ : View {suc n} i → Set where
    ‵fromℕ : IsFromℕ ‵fromℕ

  instance

    ‵fromℕ⁺ : IsFromℕ (view (fromℕ n))
    ‵fromℕ⁺ rewrite view-fromℕ n = ‵fromℕ

  data IsInj : View {suc n} i → Set where
    ‵inj₁ : ∀ {j} (v : View {n} j) → IsInj (‵inj₁ v)

  instance

    inj⁺ : IsInj (view (inject₁ j))
    inj⁺ {j} rewrite view-inject₁ j = ‵inj₁ _

    inject₁≡⁺ : {eq : inject₁ j ≡ i} → IsInj (view i)
    inject₁≡⁺ {eq = refl} = inj⁺

    inject₁≢n⁺ : {n≢i : n ≢ toℕ (inject₁ i)} → IsInj (view {suc n} i)
    inject₁≢n⁺ {i} {n≢i} with view i
    ... | ‵fromℕ = contradiction n≡i n≢i
      where
        open ≡-Reasoning
        n≡i : n ≡ toℕ (inject₁ (fromℕ n))
        n≡i = sym (begin
          toℕ (inject₁ (fromℕ n)) ≡⟨ toℕ-inject₁ (fromℕ n) ⟩
          toℕ (fromℕ n)           ≡⟨ toℕ-fromℕ n ⟩
          n                         ∎)
    ... | ‵inj₁ v = ‵inj₁ v



open Instances

------------------------------------------------------------------------
-- As a corollary, we obtain two useful properties, which are
-- witnessed by, but can also serve as proxy replacements for,
-- the corresponding properties in `Data.Fin.Properties`

view-fromℕ-toℕ : ∀ i → .{{IsFromℕ (view i)}} → toℕ i ≡ n
view-fromℕ-toℕ {n = n} i with ‵fromℕ ← view i = toℕ-fromℕ n

view-inject₁-toℕ< : ∀ i → .{{IsInj (view i)}} → toℕ i < n
view-inject₁-toℕ< i with ‵inject₁ j ← view i = inject₁ℕ< j
