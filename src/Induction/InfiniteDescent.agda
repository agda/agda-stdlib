------------------------------------------------------------------------
-- The Agda standard library
--
-- A standard consequence of accessibility/well-foundedness:
-- the impossibility of 'infinite descent' from any (accessible)
-- element x satisfying P to 'smaller' y also satisfying P
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Induction.InfiniteDescent where

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
  using (Pred; ∁; _∩_; _⊆_;  _⇒_; Universal; IUniversal; Stable; Empty)

private
  variable
    a r ℓ : Level
    A : Set a
    f : ℕ → A
    _<_ : Rel A r
    P : Pred A ℓ

------------------------------------------------------------------------
-- Definitions

InfiniteDescendingSequence : Rel A r → (ℕ → A) → Set _
InfiniteDescendingSequence _<_ f = ∀ n → f (suc n) < f n

InfiniteDescendingSequenceFrom : Rel A r → (ℕ → A) → Pred A _
InfiniteDescendingSequenceFrom _<_ f x = f zero ≡ x × InfiniteDescendingSequence _<_ f

InfiniteDescendingSequence⁺ : Rel A r → (ℕ → A) → Set _
InfiniteDescendingSequence⁺ _<_ f = ∀ {m n} → m ℕ.< n → TransClosure _<_ (f n) (f m)

InfiniteDescendingSequenceFrom⁺ : Rel A r → (ℕ → A) → Pred A _
InfiniteDescendingSequenceFrom⁺ _<_ f x = f zero ≡ x × InfiniteDescendingSequence⁺ _<_ f

DescentFrom : Rel A r → Pred A ℓ → Pred A _
DescentFrom _<_ P x = P x → ∃[ y ] y < x × P y

Descent : Rel A r → Pred A ℓ → Set _
Descent _<_ P = ∀ {x} → DescentFrom _<_ P x

InfiniteDescentFrom : Rel A r → Pred A ℓ → Pred A _
InfiniteDescentFrom _<_ P x = P x → ∃[ f ] InfiniteDescendingSequenceFrom _<_ f x × ∀ n → P (f n)

InfiniteDescent : Rel A r → Pred A ℓ →  Set _
InfiniteDescent _<_ P = ∀ {x} → InfiniteDescentFrom _<_ P x

InfiniteDescentFrom⁺ : Rel A r → Pred A ℓ → Pred A _
InfiniteDescentFrom⁺ _<_ P x = P x → ∃[ f ] InfiniteDescendingSequenceFrom⁺ _<_ f x × ∀ n → P (f n)

InfiniteDescent⁺ : Rel A r → Pred A ℓ → Set _
InfiniteDescent⁺ _<_ P = ∀ {x} → InfiniteDescentFrom⁺ _<_ P x

NoSmallestCounterExample : Rel A r → Pred A ℓ →  Set _
NoSmallestCounterExample _<_ P = ∀ {x} → Acc _<_ x → DescentFrom (TransClosure _<_) (∁ P) x

------------------------------------------------------------------------
-- We can swap between transitively closed and non-transitively closed
-- definitions

sequence⁺ : InfiniteDescendingSequence (TransClosure _<_) f →
            InfiniteDescendingSequence⁺ _<_ f
sequence⁺ {_<_ = _<_} {f = f} seq[f] = seq⁺[f]′ ∘ ℕ.<⇒<′
  where
  seq⁺[f]′ : ∀ {m n} → m ℕ.<′ n → TransClosure _<_ (f n) (f m)
  seq⁺[f]′ ℕ.<′-base        = seq[f] _
  seq⁺[f]′ (ℕ.<′-step m<′n) = seq[f] _ ++ seq⁺[f]′ m<′n

sequence⁻ : InfiniteDescendingSequence⁺ _<_ f →
            InfiniteDescendingSequence (TransClosure _<_) f
sequence⁻ seq[f] = seq[f] ∘ n<1+n

------------------------------------------------------------------------
-- Results about unrestricted descent

module _ (descent : Descent _<_ P) where

  descent∧acc⇒infiniteDescentFrom : (Acc _<_) ⊆ (InfiniteDescentFrom _<_ P)
  descent∧acc⇒infiniteDescentFrom {x} =
    Some.wfRec (InfiniteDescentFrom _<_ P) rec x
    where
    rec : _
    rec y rec[y] py
      with z , z<y , pz ← descent py
      with g , (g0≡z , g<P) , Π[P∘g] ← rec[y] z<y pz
         = h , (h0≡y , h<P) , Π[P∘h]
      where
      h : ℕ → _
      h zero = y
      h (suc n) = g n

      h0≡y : h zero ≡ y
      h0≡y = refl

      h<P : ∀ n → h (suc n) < h n
      h<P zero rewrite g0≡z = z<y
      h<P (suc n)           = g<P n

      Π[P∘h] : ∀ n →  P (h n)
      Π[P∘h] zero    = py
      Π[P∘h] (suc n) = Π[P∘g] n

  descent∧wf⇒infiniteDescent : WellFounded _<_ → InfiniteDescent _<_ P
  descent∧wf⇒infiniteDescent wf = descent∧acc⇒infiniteDescentFrom (wf _)

  descent∧acc⇒unsatisfiable : Acc _<_ ⊆ ∁ P
  descent∧acc⇒unsatisfiable {x} = Some.wfRec (∁ P) rec x
    where
    rec : _
    rec y rec[y] py = let z , z<y , pz = descent py in rec[y] z<y pz

  descent∧wf⇒empty : WellFounded _<_ → Empty P
  descent∧wf⇒empty wf x = descent∧acc⇒unsatisfiable (wf x)

------------------------------------------------------------------------
-- Results about descent only from accessible elements

module _ (accDescent : Acc _<_ ⊆ DescentFrom _<_ P) where

  private
    descent∩ : Descent _<_ (P ∩ Acc _<_)
    descent∩ (px , acc[x]) =
      let y , y<x , py = accDescent acc[x] px
      in  y , y<x , py , acc-inverse acc[x] y<x

  accDescent∧acc⇒infiniteDescentFrom : Acc _<_ ⊆ InfiniteDescentFrom _<_ P
  accDescent∧acc⇒infiniteDescentFrom acc[x] px =
    let f , sequence[f] , Π[[P∩Acc]∘f] = descent∧acc⇒infiniteDescentFrom descent∩ acc[x] (px , acc[x])
    in f , sequence[f] , proj₁ ∘ Π[[P∩Acc]∘f]

  accDescent∧wf⇒infiniteDescent : WellFounded _<_ → InfiniteDescent _<_ P
  accDescent∧wf⇒infiniteDescent wf = accDescent∧acc⇒infiniteDescentFrom (wf _)

  accDescent∧acc⇒unsatisfiable : Acc _<_ ⊆ ∁ P
  accDescent∧acc⇒unsatisfiable acc[x] px = descent∧acc⇒unsatisfiable descent∩ acc[x] (px , acc[x])

  wf⇒empty : WellFounded _<_ → Empty P
  wf⇒empty wf x = accDescent∧acc⇒unsatisfiable (wf x)

------------------------------------------------------------------------
-- Results about transitively-closed descent only from accessible elements

module _ (accDescent⁺ : Acc _<_ ⊆ DescentFrom (TransClosure _<_) P) where

  private
    descent : Acc (TransClosure _<_) ⊆ DescentFrom (TransClosure _<_) P
    descent = accDescent⁺  ∘ accessible⁻ _

  accDescent⁺∧acc⇒infiniteDescentFrom⁺ : Acc _<_ ⊆ InfiniteDescentFrom⁺ _<_ P
  accDescent⁺∧acc⇒infiniteDescentFrom⁺ acc[x] px
    with f , (f0≡x , sequence[f]) , Π[P∘f]
       ← accDescent∧acc⇒infiniteDescentFrom descent (accessible _ acc[x]) px
       = f , (f0≡x , sequence⁺ sequence[f]) , Π[P∘f]

  accDescent⁺∧wf⇒infiniteDescent⁺ : WellFounded _<_ → InfiniteDescent⁺ _<_ P
  accDescent⁺∧wf⇒infiniteDescent⁺ wf = accDescent⁺∧acc⇒infiniteDescentFrom⁺ (wf _)

  accDescent⁺∧acc⇒unsatisfiable : Acc _<_ ⊆ ∁ P
  accDescent⁺∧acc⇒unsatisfiable = accDescent∧acc⇒unsatisfiable descent ∘ accessible _

  accDescent⁺∧wf⇒empty : WellFounded _<_ → Empty P
  accDescent⁺∧wf⇒empty = wf⇒empty descent ∘ (wellFounded _)

------------------------------------------------------------------------
-- Finally: the (classical) no smallest counterexample principle itself

module _ (stable : Stable P) (noSmallest : NoSmallestCounterExample _<_ P) where

  noSmallestCounterExample∧acc⇒satisfiable : Acc _<_ ⊆ P
  noSmallestCounterExample∧acc⇒satisfiable =
    stable _ ∘ accDescent⁺∧acc⇒unsatisfiable noSmallest

  noSmallestCounterExample∧wf⇒universal : WellFounded _<_ → Universal P
  noSmallestCounterExample∧wf⇒universal wf =
    stable _ ∘ accDescent⁺∧wf⇒empty noSmallest wf
