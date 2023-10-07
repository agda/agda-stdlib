------------------------------------------------------------------------
-- The Agda standard library
--
-- A standard consequence of accessibility/well-foundedness:
-- the impossibility of 'infinite descent' from any (accessible)
-- element x satisfying P to 'smaller' y also satisfying P
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Induction.NoInfiniteDescent where

open import Data.Product.Base using (_,_; ∃-syntax; _×_)
open import Function.Base using (_∘_)
open import Induction.WellFounded using (WellFounded; Acc; acc-inverse; module Some)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Unary using (Pred; _∩_)

private
  variable
    a r ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Definitions

module InfiniteDescent (_<_ : Rel A r) (P : Pred A ℓ)  where

    DescentAt : Pred A _
    DescentAt x = P x → ∃[ y ] y < x × P y

    InfiniteDescent : Set _
    InfiniteDescent = ∀ {x} → DescentAt x

    AccInfiniteDescent : Set _
    AccInfiniteDescent = ∀ {x} → Acc _<_ x → DescentAt x

------------------------------------------------------------------------
-- Basic result: assumes unrestricted descent

    module Lemma (descent : InfiniteDescent) where

      accNoInfiniteDescent : ∀ {x} → Acc _<_ x → ¬ (P x)
      accNoInfiniteDescent = Some.wfRec (¬_ ∘ P)
        (λ _ hy py → let z , z<y , pz = descent py in hy z<y pz) _

      wfNoInfiniteDescent : WellFounded _<_ → ∀ {x} → ¬ (P x)
      wfNoInfiniteDescent wf = accNoInfiniteDescent (wf _)

------------------------------------------------------------------------
-- Extended result: assumes descent only for accessible elements

module _ {_<_ : Rel A r} (P : Pred A ℓ) where

    open InfiniteDescent _<_ P hiding (module Lemma)

    module Corollary (descent : AccInfiniteDescent) where

      accNoInfiniteDescent : ∀ {x} → Acc _<_ x → ¬ (P x)
      accNoInfiniteDescent ax px = ID∩.Lemma.accNoInfiniteDescent descent∩ ax (px , ax)
        
        where
        P∩Acc : Pred A _
        P∩Acc = P ∩ (Acc _<_)

        module ID∩ = InfiniteDescent _<_ P∩Acc

        descent∩ : ID∩.InfiniteDescent
        descent∩ (px , ax) = let y , y<x , py = descent ax px in
          y , y<x , py , acc-inverse ax y<x

      wfNoInfiniteDescent : WellFounded _<_ → ∀ {x} → ¬ (P x)
      wfNoInfiniteDescent wf = accNoInfiniteDescent (wf _)

------------------------------------------------------------------------
-- Exports

open InfiniteDescent public using (InfiniteDescent; AccInfiniteDescent; module Lemma)
open Corollary public
