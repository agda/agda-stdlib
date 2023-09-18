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
open import Data.Fin.Base as Fin using (Fin; zero; suc; fromℕ; inject₁)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation.Core using (contradiction)

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

-- An important distinguished observer and its properties

toℕ  : {i : Fin n} → View i → ℕ
toℕ (‵fromℕ {n}) = n
toℕ (‵inj₁ v)    = toℕ v

toℕ[view[suc]]≡suc[toℕ[view]] : (i : Fin n) →
                                toℕ (view (suc i)) ≡ suc (toℕ (view i))
toℕ[view[suc]]≡suc[toℕ[view]] i with view i
... | ‵fromℕ {n}      = refl
... | ‵inj₁ {i = j} v = trans (toℕ[view[suc]]≡suc[toℕ[view]] j)
                              (cong (suc ∘ toℕ) (view-unique v))

toℕ[view]≡Fin[toℕ] : (i : Fin n) → toℕ (view i) ≡ Fin.toℕ i
toℕ[view]≡Fin[toℕ] {n = suc n} zero       = toℕ[view[zero]]≡Fin[toℕ[zero]] n
  where
  toℕ[view[zero]]≡Fin[toℕ[zero]] : ∀ n → toℕ (view (zero {n})) ≡ zero
  toℕ[view[zero]]≡Fin[toℕ[zero]] zero    = refl
  toℕ[view[zero]]≡Fin[toℕ[zero]] (suc n) = toℕ[view[zero]]≡Fin[toℕ[zero]] n
toℕ[view]≡Fin[toℕ] {n = suc n} (suc i)
  rewrite toℕ[view[suc]]≡suc[toℕ[view]] i = cong suc (toℕ[view]≡Fin[toℕ] i)

-- independent reimplementation of Data.Fin.Properties.toℕ-fromℕ
n≡Fin[toℕ[fromℕ]] : ∀ n → n ≡ Fin.toℕ (fromℕ n)
n≡Fin[toℕ[fromℕ]] n = begin -- toℕ[view]≡Fin[toℕ] i
  n                    ≡⟨⟩
  toℕ (‵fromℕ {n})     ≡⟨ sym (cong toℕ (view-fromℕ n)) ⟩
  toℕ (view (fromℕ n)) ≡⟨ toℕ[view]≡Fin[toℕ] (fromℕ n) ⟩
  Fin.toℕ (fromℕ n)    ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- Derived induction principle from the Top view, via another view!

-- The idea being, that in what follows, a call pattern is repeated over
-- and over again, so should be reified as induction over a revised view,
-- `View≢`/`view≢`obtained from `View`/`view` by restricting the domain.

data View≢ : {i : Fin (suc n)} → n ≢ Fin.toℕ i → Set where
  ‵inj₁ : (j : Fin n) {n≢j : n ≢ Fin.toℕ (inject₁ j)} → View≢ n≢j

view≢ : {i : Fin (suc n)} (n≢i : n ≢ Fin.toℕ i) → View≢ n≢i
view≢ {i = i} n≢ with view i
... | ‵fromℕ {n} = contradiction (n≡Fin[toℕ[fromℕ]] n) n≢
... | ‵inject₁ j = ‵inj₁ j
