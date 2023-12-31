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
open import Induction.WellFounded
  using (WellFounded; Acc; acc; acc-inverse; module Some)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Nullary.Negation.Core as Negation using (¬_)
open import Relation.Unary
  using (Pred; ∁; _∩_; _⇒_; Universal; IUniversal; Stable)

private
  variable
    a r ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Definitions

module _ (f : ℕ → A) where

  module _ (_<_ : Rel A r) where

    InfiniteDescendingSequence : Set _
    InfiniteDescendingSequence = ∀ n → f (suc n) < f n

    InfiniteSequenceFrom : Pred A _
    InfiniteSequenceFrom x = f zero ≡ x × InfiniteDescendingSequence

  module _ (_<_ : Rel A r) where

    private

      _<⁺_ = TransClosure _<_

    InfiniteDescendingSequence⁺ : Set _
    InfiniteDescendingSequence⁺ = ∀ {m n} → m ℕ.< n → f n <⁺ f m

    InfiniteSequence⁺From : Pred A _
    InfiniteSequence⁺From x = f zero ≡ x × InfiniteDescendingSequence⁺

    sequence⁺ : InfiniteDescendingSequence _<⁺_ → InfiniteDescendingSequence⁺
    sequence⁺ seq[f] = seq⁺[f]′ ∘ ℕ.<⇒<′
      where
      seq⁺[f]′ : ∀ {m n} → m ℕ.<′ n → f n <⁺ f m
      seq⁺[f]′ ℕ.<′-base        = seq[f] _
      seq⁺[f]′ (ℕ.<′-step m<′n) = seq[f] _ ++ seq⁺[f]′ m<′n

    sequence⁻ : InfiniteDescendingSequence⁺ → InfiniteDescendingSequence _<⁺_
    sequence⁻ seq[f] = seq[f] ∘ n<1+n

module InfiniteDescent (_<_ : Rel A r) (P : Pred A ℓ)  where

    DescentAt : Pred A _
    DescentAt x = P x → ∃[ y ] y < x × P y

    Acc⇒Descent : Set _
    Acc⇒Descent = ∀ {x} → Acc _<_ x → DescentAt x

    Descent : Set _
    Descent = ∀ {x} → DescentAt x

    InfiniteDescentAt : Pred A _
    InfiniteDescentAt x = P x → ∃[ f ] InfiniteSequenceFrom f _<_ x × ∀ z → P (f z)

    Acc⇒InfiniteDescent : Set _
    Acc⇒InfiniteDescent = ∀ {x} → Acc _<_ x → InfiniteDescentAt x

    InfiniteDescent : Set _
    InfiniteDescent = ∀ {x} → InfiniteDescentAt x

------------------------------------------------------------------------
-- Basic lemmas: assume unrestricted descent

    module Lemmas (descent : Descent) where

      acc⇒infiniteDescent : Acc⇒InfiniteDescent
      acc⇒infiniteDescent {x} = Some.wfRec InfiniteDescentAt rec x
        where
        rec : _
        rec y rec[y] py
          with z , z<y , pz ← descent py
          with g , (g0≡z , g<P) , Π[P∘g] ← rec[y] z<y pz
             = f , (f0≡y , f<P) , Π[P∘f]
          where
          f : ℕ → A
          f zero = y
          f (suc n) = g n

          f0≡y : f zero ≡ y
          f0≡y = refl

          f<P : ∀ n → f (suc n) < f n
          f<P zero rewrite g0≡z = z<y
          f<P (suc n)           = g<P n

          Π[P∘f] : ∀ n →  P (f n)
          Π[P∘f] zero rewrite g0≡z = py
          Π[P∘f] (suc n)           = Π[P∘g] n

      wf⇒infiniteDescent : WellFounded _<_ → InfiniteDescent
      wf⇒infiniteDescent wf = acc⇒infiniteDescent (wf _)

      acc⇒noInfiniteDescent : ∀ {x} → Acc _<_ x → ¬ P x
      acc⇒noInfiniteDescent {x} = Some.wfRec (¬_ ∘ P) rec x
        where
        rec : _
        rec y rec[y] py = let z , z<y , pz = descent py in rec[y] z<y pz

      wf⇒noInfiniteDescent : WellFounded _<_ → ∀ {x} → ¬ P x
      wf⇒noInfiniteDescent wf = acc⇒noInfiniteDescent (wf _)

------------------------------------------------------------------------
-- Corollaries: assume descent only for Acc _<_ elements

module _ (_<_ : Rel A r) (P : Pred A ℓ) where

  open InfiniteDescent _<_ P

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
      let f , sequence[f] , Π[[P∩Acc]∘f] = Lemmas∩.acc⇒infiniteDescent acc[x] (px , acc[x])
      in f , sequence[f] , proj₁ ∘ Π[[P∩Acc]∘f]

    wf⇒infiniteDescent : WellFounded _<_ → InfiniteDescent
    wf⇒infiniteDescent wf = acc⇒infiniteDescent (wf _)

    acc⇒noInfiniteDescent : ∀ {x} → Acc _<_ x → ¬ P x
    acc⇒noInfiniteDescent acc[x] px = Lemmas∩.acc⇒noInfiniteDescent acc[x] (px , acc[x])

    wf⇒noInfiniteDescent : WellFounded _<_ → ∀ {x} → ¬ P x
    wf⇒noInfiniteDescent wf = acc⇒noInfiniteDescent (wf _)


------------------------------------------------------------------------
-- Further corollaries: assume _<⁺_ descent only for Acc _<⁺_  elements

module FurtherCorollaries (_<_ : Rel A r) (P : Pred A ℓ) where

  private

    _<⁺_ = TransClosure _<_

    module ID⁺ = InfiniteDescent _<⁺_ P

    DescentAt⁺   = ID⁺.DescentAt
    Descent⁺     = ID⁺.Descent

  Acc⇒Descent⁺ : Set _
  Acc⇒Descent⁺ = ∀ {x} → Acc _<_ x → DescentAt⁺ x

  InfiniteDescentAt⁺ : Pred A _
  InfiniteDescentAt⁺ x = P x → ∃[ f ] InfiniteSequence⁺From f _<_ x × ∀ z → P (f z)

  Acc⇒InfiniteDescent⁺ : Set _
  Acc⇒InfiniteDescent⁺ = ∀ {x} → Acc _<_ x → InfiniteDescentAt⁺ x

  InfiniteDescent⁺ : Set _
  InfiniteDescent⁺ = ∀ {x} → InfiniteDescentAt⁺ x

  module _ (descent⁺ : Acc⇒Descent⁺) where

    private
      descent : ID⁺.Acc⇒Descent
      descent = descent⁺  ∘ (accessible⁻ _)

      module Corollaries⁺ = Corollaries _ _ descent

    acc⇒infiniteDescent⁺ : Acc⇒InfiniteDescent⁺
    acc⇒infiniteDescent⁺ acc[x] px
      with f , (f0≡x , sequence[f]) , Π[P∘f] ← Corollaries⁺.acc⇒infiniteDescent (accessible _ acc[x]) px
         = f , (f0≡x , sequence⁺ _ _ sequence[f]) , Π[P∘f]

    wf⇒infiniteDescent⁺ : WellFounded _<_ → InfiniteDescent⁺
    wf⇒infiniteDescent⁺ wf = acc⇒infiniteDescent⁺ (wf _)

    acc⇒noInfiniteDescent⁺ : ∀ {x} → Acc _<_ x → ¬ P x
    acc⇒noInfiniteDescent⁺ = Corollaries⁺.acc⇒noInfiniteDescent ∘ (accessible _)

    wf⇒noInfiniteDescent⁺ : WellFounded _<_ → ∀ {x} → ¬ P x
    wf⇒noInfiniteDescent⁺ = Corollaries⁺.wf⇒noInfiniteDescent ∘ (wellFounded _)

------------------------------------------------------------------------
-- Finally:  the (classical) 'no smallest counterexample' principle itself

module _ (_<_ : Rel A r) {P : Pred A ℓ} (stable : Stable P) where

  open FurtherCorollaries _<_ (∁ P)
    using (acc⇒noInfiniteDescent⁺; wf⇒noInfiniteDescent⁺)
    renaming (Acc⇒Descent⁺ to NoSmallestCounterExample)

  acc⇒noSmallestCounterExample : NoSmallestCounterExample → ∀ {x} → Acc _<_ x → P x
  acc⇒noSmallestCounterExample noSmallest = stable _ ∘ acc⇒noInfiniteDescent⁺ noSmallest

  wf⇒noSmallestCounterExample : WellFounded _<_ → NoSmallestCounterExample → ∀ {x} → P x
  wf⇒noSmallestCounterExample wf noSmallest = stable _ (wf⇒noInfiniteDescent⁺ noSmallest wf)

------------------------------------------------------------------------
-- Exports

open InfiniteDescent public
open Corollaries public
open FurtherCorollaries public

