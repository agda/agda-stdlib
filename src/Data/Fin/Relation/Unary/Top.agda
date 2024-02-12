------------------------------------------------------------------------
-- The Agda standard library
--
-- The 'top' view of Fin.
--
-- This is an example of a view of (elements of) a datatype,
-- here i : Fin (suc n), which exhibits every such i as
-- * either, i = fromℕ n
-- * or, i = inject₁ j for a unique j : Fin n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Relation.Unary.Top where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; fromℕ; inject₁)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    n : ℕ
    i : Fin n

------------------------------------------------------------------------
-- The View, considered as a unary relation on Fin n

-- NB `Data.Fin.Properties.fromℕ≢inject₁` establishes that the following
-- inductively defined family on `Fin n` has constructors which target
-- *disjoint* instances of the family (moreover at indices `n = suc _`);
-- hence the interpretations of the View constructors will also be disjoint.

data View : (i : Fin n) → Set where
  ‵fromℕ : View (fromℕ n)
  ‵inj₁ : View i → View (inject₁ i)

pattern ‵inject₁ i = ‵inj₁ {i = i} _

-- The view covering function, witnessing soundness of the view

view : (i : Fin n) → View i
view zero = view-zero where
  view-zero : View (zero {n})
  view-zero {n = zero}  = ‵fromℕ
  view-zero {n = suc _} = ‵inj₁ view-zero
view (suc i) with view i
... | ‵fromℕ     = ‵fromℕ
... | ‵inject₁ i = ‵inj₁ (view (suc i))

-- Interpretation of the view constructors

⟦_⟧ : {i : Fin n} → View i → Fin n
⟦ ‵fromℕ ⟧     = fromℕ _
⟦ ‵inject₁ i ⟧ = inject₁ i

-- Completeness of the view

view-complete : (v : View i) → ⟦ v ⟧ ≡ i
view-complete ‵fromℕ    = refl
view-complete (‵inj₁ _) = refl

-- 'Computational' behaviour of the covering function

view-fromℕ : ∀ n → view (fromℕ n) ≡ ‵fromℕ
view-fromℕ zero                         = refl
view-fromℕ (suc n) rewrite view-fromℕ n = refl

view-inject₁ : (i : Fin n) → view (inject₁ i) ≡ ‵inj₁ (view i)
view-inject₁ zero                           = refl
view-inject₁ (suc i) rewrite view-inject₁ i = refl

-- Uniqueness of the view

view-unique : (v : View i) → view i ≡ v
view-unique ‵fromℕ            = view-fromℕ _
view-unique (‵inj₁ {i = i} v) = begin
  view (inject₁ i) ≡⟨ view-inject₁ i ⟩
  ‵inj₁ (view i)   ≡⟨ cong ‵inj₁ (view-unique v) ⟩
  ‵inj₁ v          ∎ where open ≡-Reasoning
