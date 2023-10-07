------------------------------------------------------------------------
-- The Agda standard library
--
-- A standard consequence of accessibility/well-foundedness:
-- the impossibility of 'infinite descent' from any x st P to
-- 'smaller' y also satisfying P
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Induction.NoInfiniteDescent where

open import Data.Product.Base using (_,_; proj₁; proj₂; ∃-syntax; _×_)
open import Function.Base using (_∘_)
open import Induction.WellFounded
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Unary using (Pred)

private
  variable
    a b ℓ ℓ₁ ℓ₂ r : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definitions

module _ {_<_ : Rel A r} (P : Pred A ℓ)  where

    private
      _<⁺_ : Rel A _
      z <⁺ x = z ⟨ _<_ ⟩⁺ x

    SmallerCounterexample : Pred A _
    SmallerCounterexample x = (px : P x) → ∃[ y ] y < x × P y

    SmallerCounterexample⁺ : Pred A _
    SmallerCounterexample⁺ x = (px : P x) → ∃[ y ] y <⁺ x × P y

------------------------------------------------------------------------
-- Basic result

    module Lemma (sce : ∀ {x} → SmallerCounterexample x) where

      accNoSmallestCounterexample : ∀ {x} → Acc _<_ x → ¬ (P x)
      accNoSmallestCounterexample = Some.wfRec _
        (λ _ hy py → let z , z<y , pz = sce py in hy z<y pz) _

      wfNoSmallestCounterexample : WellFounded _<_ → ∀ {x} → ¬ (P x)
      wfNoSmallestCounterexample wf = accNoSmallestCounterexample (wf _)



