------------------------------------------------------------------------
-- The Agda standard library
--
-- A standard consequence of accessibility/well-foundedness:
-- the impossibility of 'infinite descent' from any (accessible)
-- element x satisfying P to 'smaller' y also satisfying P
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Induction.NoInfiniteDescent where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; Σ-syntax; ∃-syntax; _×_)
open import Function.Base using (_∘_)
open import Induction.WellFounded using (WellFounded; Acc; acc; acc-inverse; module Some)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Unary using (Pred; _∩_; _⇒_; IUniversal)

private
  variable
    a r ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Definitions

module InfiniteDescent (_<_ : Rel A r) (P : Pred A ℓ)  where

    DescentAt : Pred A _
    DescentAt x = P x → ∃[ y ] y < x × P y

    AccDescent : Set _
    AccDescent = ∀[ Acc _<_ ⇒ DescentAt ]

    Descent : Set _
    Descent = ∀[ DescentAt ]

    InfiniteDescentAt : Pred A _
    InfiniteDescentAt x = P x → Σ[ f ∈ (ℕ → A) ] f zero ≡ x × ∀ n → f (suc n) < f n

    AccInfiniteDescent : Set _
    AccInfiniteDescent = ∀[ Acc _<_ ⇒ InfiniteDescentAt ]

    InfiniteDescent : Set _
    InfiniteDescent = ∀[ InfiniteDescentAt ]

------------------------------------------------------------------------
-- Basic result: assumes unrestricted descent

    module Lemmas (descent : Descent) where

      accInfiniteDescent : AccInfiniteDescent
      accInfiniteDescent {x} = Some.wfRec InfiniteDescentAt rec x
        where
        rec : _
        rec y rec[y] py
          with z , z<y , pz ← descent py
          with g , g0≡z , g< ← rec[y] z<y pz = f , f0≡y , f<
          where
          f : ℕ → A
          f zero = y
          f (suc n) = g n
          f0≡y : f zero ≡ y
          f0≡y = refl
          f< : ∀ n → f (suc n) < f n
          f< zero rewrite g0≡z = z<y
          f< (suc n)           = g< n

      wfInfiniteDescent : WellFounded _<_ → InfiniteDescent
      wfInfiniteDescent wf = accInfiniteDescent (wf _)

      accNoInfiniteDescent : ∀[ Acc _<_ ⇒ ¬_ ∘ P ]
      accNoInfiniteDescent {x} = Some.wfRec (¬_ ∘ P) rec x
        where
        rec : _
        rec y rec[y] py = let z , z<y , pz = descent py in rec[y] z<y pz

      wfNoInfiniteDescent : WellFounded _<_ → ∀[ ¬_ ∘ P ]
      wfNoInfiniteDescent wf = accNoInfiniteDescent (wf _)

------------------------------------------------------------------------
-- Extended result: assumes descent only for accessible elements

module _ {_<_ : Rel A r} (P : Pred A ℓ) where

    open InfiniteDescent _<_ P public

    module Corollaries (descent : AccDescent) where

      private

        P∩Acc : Pred A _
        P∩Acc = P ∩ (Acc _<_)

        module ID∩ = InfiniteDescent _<_ P∩Acc

        descent∩ : ID∩.Descent
        descent∩ (px , ax) = let y , y<x , py = descent ax px in
          y , y<x , py , acc-inverse ax y<x

        module Lemmas∩ = ID∩.Lemmas descent∩

      accInfiniteDescent : AccInfiniteDescent
      accInfiniteDescent {x} ax px = Lemmas∩.accInfiniteDescent ax (px , ax)

      wfInfiniteDescent : WellFounded _<_ → InfiniteDescent
      wfInfiniteDescent wf = accInfiniteDescent (wf _)

      accNoInfiniteDescent : ∀[ Acc _<_ ⇒ ¬_ ∘ P ]
      accNoInfiniteDescent ax px = Lemmas∩.accNoInfiniteDescent ax (px , ax)

      wfNoInfiniteDescent : WellFounded _<_ → ∀[ ¬_ ∘ P ]
      wfNoInfiniteDescent wf = accNoInfiniteDescent (wf _)

------------------------------------------------------------------------
-- Exports

open Corollaries public
