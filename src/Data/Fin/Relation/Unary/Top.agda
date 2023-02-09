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

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _∸_)
open import Data.Nat.Properties using (n∸n≡0; +-∸-assoc)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; fromℕ<; inject₁)
open import Data.Fin.Properties as Fin
  using (suc-injective; inject₁-injective; toℕ-fromℕ; toℕ<n; toℕ-inject₁; inject₁ℕ<)
open import Relation.Binary.PropositionalEquality

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The View, considered as a unary relation on Fin (suc n)

-- First, a lemma not in `Data.Fin.Properties`,
-- but which establishes disjointness of the
-- (interpretations of the) constructors of the View

top≢inject₁ : ∀ (j : Fin n) → fromℕ n ≢ inject₁ j
top≢inject₁ (suc j) eq = top≢inject₁ j (suc-injective eq)

-- The View, itself

data View : (i : Fin (suc n)) → Set where

  top :                View (fromℕ n)
  inj : (j : Fin n) → View (inject₁ j)

-- The view covering function, witnessing soundness of the view

view : ∀ {n} i → View {n} i
view {n = zero}  zero = top
view {n = suc _} zero = inj _
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
-- so we introduce instances to witness them, themselves given by
-- the functions `view-top` and `view-inj` defined above

module Instances {n} where

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
    ... | top   = ⊥-elim (n≢i (begin
      n                         ≡˘⟨ toℕ-fromℕ n ⟩
      toℕ (fromℕ n)           ≡˘⟨ toℕ-inject₁ (fromℕ n) ⟩
      toℕ (inject₁ (fromℕ n)) ∎)) where open ≡-Reasoning
    ... | inj j = inj j

open Instances

------------------------------------------------------------------------
-- As a corollary, we obtain two useful properties, which are
-- witnessed by, but can also serve as proxy replacements for,
-- the corresponding properties in `Data.Fin.Properties`

module _ {n} where

  view-top-toℕ : ∀ i → .{{IsTop (view i)}} → toℕ i ≡ n
  view-top-toℕ i with top ← view i = toℕ-fromℕ n

  view-inj-toℕ< : ∀ i → .{{IsInj (view i)}} → toℕ i < n
  view-inj-toℕ< i with inj j ← view i = inject₁ℕ< j

------------------------------------------------------------------------
-- Examples

private module Examples {n} where

-- Similarly, we can redefine certain operations in `Data.Fin.Base`,
-- together with their corresponding properties in `Data.Fin.Properties`

-- Here: the reimplementation of the function `lower₁` and its properties,
-- specified as a partial inverse to `inject₁`, defined on the domain given
-- by `n ≢ toℕ i`, equivalently `i ≢ from ℕ n`, ie `IsInj {n} (view i)`

-- Definition
{-
lower₁ : ∀ (i : Fin (suc n)) → n ≢ toℕ i → Fin n
lower₁ {zero}  zero    ne = ⊥-elim (ne refl)
lower₁ {suc n} zero    _  = zero
lower₁ {suc n} (suc i) ne = suc (lower₁ i (ne ∘ cong suc))
-}

  lower₁ : (i : Fin (suc n)) → .{{IsInj (view {n} i)}} → Fin n
  lower₁ i with inj j ← view i = j -- the view *inverts* inject₁

-- Properties
{-
toℕ-lower₁ : ∀ i (p : n ≢ toℕ i) → toℕ (lower₁ i p) ≡ toℕ i

lower₁-injective : ∀ {n≢i : n ≢ toℕ i} {n≢j : n ≢ toℕ j} →
                   lower₁ i n≢i ≡ lower₁ j n≢j → i ≡ j
inject₁-lower₁ : ∀ (i : Fin (suc n)) (n≢i : n ≢ toℕ i) →
                 inject₁ (lower₁ i n≢i) ≡ i
lower₁-inject₁′ : ∀ (i : Fin n) (n≢i : n ≢ toℕ (inject₁ i)) →
                  lower₁ (inject₁ i) n≢i ≡ i
lower₁-inject₁ : ∀ (i : Fin n) →
                 lower₁ (inject₁ i) (toℕ-inject₁-≢ i) ≡ i
lower₁-inject₁ i = lower₁-inject₁′ i (toℕ-inject₁-≢ i)
lower₁-irrelevant : ∀ (i : Fin (suc n)) (n≢i₁ n≢i₂ : n ≢ toℕ i) →
                    lower₁ i n≢i₁ ≡ lower₁ i n≢i₂
inject₁≡⇒lower₁≡ : ∀ {i : Fin n} {j : Fin (ℕ.suc n)} →
                  (n≢j : n ≢ toℕ j) → inject₁ i ≡ j → lower₁ j n≢j ≡ i
-}

  lower₁-irrelevant : (i : Fin (suc n)) .{{ii₁ ii₂ : IsInj (view {n} i)}} →
                      lower₁ i {{ii₁}} ≡ lower₁ i {{ii₂}}
  lower₁-irrelevant i with inj ii ← view i = refl

  toℕ-lower₁ : (i : Fin (suc n)) .{{ii : IsInj (view {n} i)}} →
                toℕ (lower₁ i {{ii}}) ≡ toℕ i
  toℕ-lower₁ i with inj j ← view i = sym (toℕ-inject₁ j)

  lower₁-injective : (i j : Fin (suc n)) →
                     .{{ii : IsInj (view {n} i)}} →
                     .{{jj : IsInj (view {n} j)}} →
                     lower₁ i {{ii}} ≡ lower₁ j {{jj}} → i ≡ j
  lower₁-injective i j with inj ii ← view i | inj jj ← view j = cong inject₁

  inject₁-lower₁ : (i : Fin (suc n)) .{{ii : IsInj (view {n} i)}} →
                   inject₁ (lower₁ i {{ii}}) ≡ i
  inject₁-lower₁ i with inj ii ← view i = refl

  lower₁-inject₁ : (j : Fin n) → lower₁ (inject₁ j) {{inj⁺}} ≡ j
  lower₁-inject₁ j rewrite view-inj j = refl

  inject₁≡⇒lower₁≡ : ∀ {i : Fin n} {j : Fin (suc n)} (eq : inject₁ i ≡ j) →
                       lower₁ j {{inject₁≡⁺ {eq = eq}}} ≡ i
  inject₁≡⇒lower₁≡ refl = lower₁-inject₁ _

-- Second: the reimplementation of the function `opposite` and its properties,

-- Definition
{-
  opposite : Fin n → Fin n
  opposite {suc n} zero    = fromℕ n
  opposite {suc n} (suc i) = inject₁ (opposite i)
-}

  opposite : ∀ {n} → Fin n → Fin n
  opposite {n = suc n} i with view i
  ... | top   = zero
  ... | inj j = suc (opposite {n} j)

-- Properties

  opposite-zero≡top : ∀ n → opposite {suc n} zero ≡ fromℕ n
  opposite-zero≡top zero    = refl
  opposite-zero≡top (suc n) = cong suc (opposite-zero≡top n)

  opposite-top≡zero : ∀ n → opposite {suc n} (fromℕ n) ≡ zero
  opposite-top≡zero n rewrite view-top n = refl

  opposite-suc≡inject₁-opposite : ∀ {n} (j : Fin n) →
                                  opposite (suc j) ≡ inject₁ (opposite j)
  opposite-suc≡inject₁-opposite {suc n} i with view i
  ... | top   = refl
  ... | inj j = cong suc (opposite-suc≡inject₁-opposite {n} j)

  opposite-involutive : ∀ {n} (j : Fin n) → opposite (opposite j) ≡ j
  opposite-involutive {suc n} zero
    rewrite opposite-zero≡top n
          | view-top n            = refl
  opposite-involutive {suc n} (suc i)
    rewrite opposite-suc≡inject₁-opposite i
          | view-inj (opposite i) = cong suc (opposite-involutive i)

  opposite-suc : (j : Fin n) → toℕ (opposite (suc j)) ≡ toℕ (opposite j)
  opposite-suc j = begin
    toℕ (opposite (suc j))      ≡⟨ cong toℕ (opposite-suc≡inject₁-opposite j) ⟩
    toℕ (inject₁ (opposite j))  ≡⟨ toℕ-inject₁ (opposite j) ⟩
    toℕ (opposite j) ∎
    where open ≡-Reasoning

  opposite-prop : ∀ {n} (i : Fin n) → toℕ (opposite i) ≡ n ∸ suc (toℕ i)
  opposite-prop {suc n} i with view i
  ... | top   rewrite toℕ-fromℕ n | n∸n≡0 n = refl
  ... | inj j = begin
    suc (toℕ (opposite j)) ≡⟨ cong suc (opposite-prop j) ⟩
    suc (n ∸ suc (toℕ j)) ≡˘⟨ +-∸-assoc 1 {n} {suc (toℕ j)} (toℕ<n j) ⟩
    n ∸ toℕ j             ≡˘⟨ cong (n ∸_) (toℕ-inject₁ j) ⟩
    n ∸ toℕ (inject₁ j)   ∎ where open ≡-Reasoning
