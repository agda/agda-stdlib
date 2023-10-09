------------------------------------------------------------------------
-- The Agda standard library
--
-- A standard consequence of accessibility/well-foundedness:
-- the impossibility of 'infinite descent' from any (accessible)
-- element x satisfying P to 'smaller' y also satisfying P
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Induction.NoInfiniteDescent where

open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ
open import Data.Product.Base using (_,_; proj₁; ∃-syntax; _×_)
open import Function.Base using (_∘_)
open import Induction.WellFounded using (WellFounded; Acc; acc; acc-inverse; module Some)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Unary using (Pred; _∩_; _⇒_; Universal; IUniversal)

private
  variable
    a r ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Definitions

module InfiniteDescent (_<_ : Rel A r) (P : Pred A ℓ)  where

    DescentAt : Pred A _
    DescentAt x = P x → ∃[ y ] y < x × P y

    Acc⇒Descent : Set _
    Acc⇒Descent = ∀[ Acc _<_ ⇒ DescentAt ]

    Descent : Set _
    Descent = ∀[ DescentAt ]

    InfiniteDescendingSequence : (f : ℕ → A) → Set _
    InfiniteDescendingSequence f = ∀ n → f (suc n) < f n

    InfiniteSequence_From_ : (f : ℕ → A) → Pred A _
    InfiniteSequence f From x = f zero ≡ x × InfiniteDescendingSequence f

    InfiniteDescentAt : Pred A _
    InfiniteDescentAt x = P x → ∃[ f ] Π[ P ∘ f ] × InfiniteSequence f From x

    Acc⇒InfiniteDescent : Set _
    Acc⇒InfiniteDescent = ∀[ Acc _<_ ⇒ InfiniteDescentAt ]

    InfiniteDescent : Set _
    InfiniteDescent = ∀[ InfiniteDescentAt ]

------------------------------------------------------------------------
-- Basic lemmas: assume unrestricted descent

    module Lemmas (descent : Descent) where

      acc⇒infiniteDescent : Acc⇒InfiniteDescent
      acc⇒infiniteDescent {x} = Some.wfRec InfiniteDescentAt rec x
        where
        rec : _
        rec y rec[y] py
          with z , z<y , pz ← descent py
          with g , Π[P∘g] , g0≡z , g<P ← rec[y] z<y pz
             = f , Π[P∘f] , f0≡y , f<P
          where
          f : ℕ → A
          f zero = y
          f (suc n) = g n
          f0≡y : f zero ≡ y
          f0≡y = refl
          f<P : ∀ n → f (suc n) < f n
          f<P zero rewrite g0≡z = z<y
          f<P (suc n)           = g<P n
          Π[P∘f] : Π[ P ∘ f ]
          Π[P∘f] zero rewrite g0≡z = py
          Π[P∘f] (suc n)           = Π[P∘g] n

      wf⇒infiniteDescent : WellFounded _<_ → InfiniteDescent
      wf⇒infiniteDescent wf = acc⇒infiniteDescent (wf _)

      acc⇒noInfiniteDescent : ∀[ Acc _<_ ⇒ ¬_ ∘ P ]
      acc⇒noInfiniteDescent {x} = Some.wfRec (¬_ ∘ P) rec x
        where
        rec : _
        rec y rec[y] py = let z , z<y , pz = descent py in rec[y] z<y pz

      wf⇒noInfiniteDescent : WellFounded _<_ → ∀[ ¬_ ∘ P ]
      wf⇒noInfiniteDescent wf = acc⇒noInfiniteDescent (wf _)

------------------------------------------------------------------------
-- Corollaries: assume descent only for Acc _<_ elements

module _ {_<_ : Rel A r} (P : Pred A ℓ) where

    open InfiniteDescent _<_ P public

    module Corollaries (descent : Acc⇒Descent) where

      private

        P∩Acc : Pred A _
        P∩Acc = P ∩ (Acc _<_)

        module ID∩ = InfiniteDescent _<_ P∩Acc

        descent∩ : ID∩.Descent
        descent∩ (px , acc[x]) =
          let y , y<x , py = descent acc[x] px
          in y , y<x , py , acc-inverse acc[x] y<x

        module Lemmas∩ = ID∩.Lemmas descent∩

      acc⇒infiniteDescent : Acc⇒InfiniteDescent
      acc⇒infiniteDescent acc[x] px =
        let f , Π[[P∩Acc]∘f] , sequence[f] = Lemmas∩.acc⇒infiniteDescent acc[x] (px , acc[x])
        in f , proj₁ ∘ Π[[P∩Acc]∘f] , sequence[f]

      wf⇒infiniteDescent : WellFounded _<_ → InfiniteDescent
      wf⇒infiniteDescent wf = acc⇒infiniteDescent (wf _)

      acc⇒noInfiniteDescent : ∀[ Acc _<_ ⇒ ¬_ ∘ P ]
      acc⇒noInfiniteDescent acc[x] px = Lemmas∩.acc⇒noInfiniteDescent acc[x] (px , acc[x])

      wf⇒noInfiniteDescent : WellFounded _<_ → ∀[ ¬_ ∘ P ]
      wf⇒noInfiniteDescent wf = acc⇒noInfiniteDescent (wf _)


------------------------------------------------------------------------
-- Further corollaries: assume _<⁺_ descent only for Acc _<⁺_  elements

module _ {_<_ : Rel A r} (P : Pred A ℓ) where

  private

    _<⁺_ = TransClosure _<_

    module ID⁺ = InfiniteDescent _<⁺_ P

    DescentAt⁺   = ID⁺.DescentAt
    Descent⁺     = ID⁺.Descent

  Acc⇒Descent⁺ : Set _
  Acc⇒Descent⁺ = ∀[ Acc _<_ ⇒ DescentAt⁺ ]

  InfiniteDescendingSequence⁺ : (f : ℕ → A) → Set _
  InfiniteDescendingSequence⁺ f = ∀ {m n} → m ℕ.< n → f n <⁺ f m

  InfiniteSequence⁺_From_ : (f : ℕ → A) → Pred A _
  InfiniteSequence⁺ f From x = f zero ≡ x × InfiniteDescendingSequence⁺ f

  InfiniteDescentAt⁺ : Pred A _
  InfiniteDescentAt⁺ x = P x → ∃[ f ] Π[ P ∘ f ] × InfiniteSequence⁺ f From x

  Acc⇒InfiniteDescent⁺ : Set _
  Acc⇒InfiniteDescent⁺ = ∀[ Acc _<_ ⇒ InfiniteDescentAt⁺ ]

  InfiniteDescent⁺ : Set _
  InfiniteDescent⁺ = ∀[ InfiniteDescentAt⁺ ]

  module _ (descent⁺ : Acc⇒Descent⁺) where

    private
      descent : ID⁺.Acc⇒Descent
      descent = descent⁺  ∘ (accessible⁻ _)

      module Corollaries⁺ = Corollaries _ descent

      sequence⁺ : ∀ {f} →
                  ID⁺.InfiniteDescendingSequence f → InfiniteDescendingSequence⁺ f
      sequence⁺ {f} seq[f] = seq⁺[f]′ ∘ ℕ.<⇒<′
        where
        seq⁺[f]′ : ∀ {m n} → m ℕ.<′ n → f n <⁺ f m
        seq⁺[f]′ ℕ.<′-base        = seq[f] _
        seq⁺[f]′ (ℕ.<′-step m<′n) = seq[f] _ ++ seq⁺[f]′ m<′n


    acc⇒infiniteDescent⁺ : Acc⇒InfiniteDescent⁺
    acc⇒infiniteDescent⁺ acc[x] px
      with f , Π[P∘f] , f0≡x , sequence[f] ← Corollaries⁺.acc⇒infiniteDescent (accessible _ acc[x]) px
         = f , Π[P∘f] , f0≡x , sequence⁺ sequence[f]

    wf⇒infiniteDescent⁺ : WellFounded _<_ → InfiniteDescent⁺
    wf⇒infiniteDescent⁺ wf = acc⇒infiniteDescent⁺ (wf _)

    acc⇒noInfiniteDescent⁺ : ∀[ Acc _<_ ⇒ ¬_ ∘ P ]
    acc⇒noInfiniteDescent⁺ = Corollaries⁺.acc⇒noInfiniteDescent ∘ (accessible _)

    wf⇒noInfiniteDescent⁺ : WellFounded _<_ → ∀[ ¬_ ∘ P ]
    wf⇒noInfiniteDescent⁺ = Corollaries⁺.wf⇒noInfiniteDescent ∘ (wellFounded _)


------------------------------------------------------------------------
-- Exports

open Corollaries public
