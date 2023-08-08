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

module Data.Fin.Relation.Unary.Top.Instances where

open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁)
open import Data.Fin.Properties using (toℕ-fromℕ; toℕ-inject₁; inject₁ℕ<)
open import Data.Fin.Relation.Unary.Top
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    n : ℕ
    i : Fin (suc n)
    j : Fin n

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
-- terms of the functions `view-fromℕ` and `view-inject₁` defined in
-- `Data.Fin.Relation.Unary.Top`

data IsFromℕ : View {suc n} i → Set where
  ‵fromℕ : IsFromℕ (‵fromℕ {n})

instance

  fromℕ⁺ : IsFromℕ (view (fromℕ n))
  fromℕ⁺ {n = n} rewrite view-fromℕ n = ‵fromℕ

data IsInject₁ : View {suc n} i → Set where
  ‵inj₁ : ∀ {j} (v : View {n} j) → IsInject₁ (‵inj₁ v)

instance

  inject₁⁺ : IsInject₁ (view (inject₁ j))
  inject₁⁺ {j = j} rewrite view-inject₁ j = ‵inj₁ _

  inject₁≡⁺ : {eq : inject₁ j ≡ i} → IsInject₁ (view i)
  inject₁≡⁺ {eq = refl} = inject₁⁺

  inject₁≢n⁺ : {n≢i : n ≢ toℕ (inject₁ i)} → IsInject₁ (view {suc n} i)
  inject₁≢n⁺ {n} {i} {n≢i} with view i
  ... | ‵fromℕ = contradiction (sym i≡n) n≢i
    where
      open ≡-Reasoning
      i≡n : toℕ (inject₁ (fromℕ n)) ≡ n
      i≡n = begin
        toℕ (inject₁ (fromℕ n)) ≡⟨ toℕ-inject₁ (fromℕ n) ⟩
        toℕ (fromℕ n)           ≡⟨ toℕ-fromℕ n ⟩
        n                       ∎
  ... | ‵inj₁ v = ‵inj₁ v


------------------------------------------------------------------------
-- As corollaries, we obtain two useful properties, which are
-- witnessed by, but can also serve as proxy replacements for,
-- the corresponding properties in `Data.Fin.Properties`

view-fromℕ-toℕ : ∀ i → .{{IsFromℕ (view i)}} → toℕ i ≡ n
view-fromℕ-toℕ {n = n} i with ‵fromℕ ← view i = toℕ-fromℕ n

view-inject₁-toℕ< : ∀ i → .{{IsInject₁ (view i)}} → toℕ i < n
view-inject₁-toℕ< i with ‵inject₁ j ← view i = inject₁ℕ< j
