------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction over Fin
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s; _∸_)
import Data.Nat.Induction as ℕ
import Data.Nat.Properties as ℕ
open import Induction
open import Induction.WellFounded as WF
open import Level using (Level)
import Relation.Binary.Construct.On as On
open import Relation.Unary using (Pred)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality

module Data.Fin.Induction where

private
  variable
    ℓ : Level
    n : ℕ

------------------------------------------------------------------------
-- Re-export accessability

open WF public using (Acc; acc)

------------------------------------------------------------------------
-- Induction over _<_

<-wellFounded : WellFounded {A = Fin n} _<_
<-wellFounded = On.wellFounded toℕ ℕ.<-wellFounded

<-weakInduction : (P : Pred (Fin (suc n)) ℓ) →
                  P zero →
                  (∀ i → P (inject₁ i) → P (suc i)) →
                  ∀ i → P i
<-weakInduction P P₀ Pᵢ⇒Pᵢ₊₁ i = induct (<-wellFounded i)
  where
  induct : ∀ {i} → Acc _<_ i → P i
  induct {zero}  _         = P₀
  induct {suc i} (acc rec) = Pᵢ⇒Pᵢ₊₁ i (induct (rec (inject₁ i) i<i+1))
    where i<i+1 = s≤s (ℕ.≤-reflexive (toℕ-inject₁ i))

------------------------------------------------------------------------
-- Induction over _>_

private
  acc-map : ∀ {x : Fin n} → Acc ℕ._<_ (n ∸ toℕ x) → Acc _>_ x
  acc-map {n} (acc rs) = acc (λ y y>x →
    acc-map (rs (n ∸ toℕ y) (ℕ.∸-monoʳ-< y>x (toℕ≤n y))))

>-wellFounded : WellFounded {A = Fin n} _>_
>-wellFounded {n} x = acc-map (ℕ.<-wellFounded (n ∸ toℕ x))

>-weakInduction : (P : Pred (Fin (suc n)) ℓ) →
                  P (fromℕ n) →
                  (∀ i → P (suc i) → P (inject₁ i)) →
                  ∀ i → P i
>-weakInduction {n = n} P Pₙ Pᵢ₊₁⇒Pᵢ i = induct (>-wellFounded i)
  where
  induct : ∀ {i} → Acc _>_ i → P i
  induct {i} (acc rec) with n ℕ.≟ toℕ i
  ... | yes n≡i = subst P (toℕ-injective (trans (toℕ-fromℕ n) n≡i)) Pₙ
  ... | no  n≢i = subst P (inject₁-lower₁ i n≢i) (Pᵢ₊₁⇒Pᵢ _ Pᵢ₊₁)
    where Pᵢ₊₁ = induct (rec _ (s≤s (ℕ.≤-reflexive (sym (toℕ-lower₁ i n≢i)))))

------------------------------------------------------------------------
-- Induction over _≺_

≺-Rec : RecStruct ℕ ℓ ℓ
≺-Rec = WfRec _≺_

≺-wellFounded : WellFounded _≺_
≺-wellFounded = Subrelation.wellFounded ≺⇒<′ ℕ.<′-wellFounded

module _ {ℓ} where
  open WF.All ≺-wellFounded ℓ public
    renaming
    ( wfRecBuilder to ≺-recBuilder
    ; wfRec        to ≺-rec
    )
    hiding (wfRec-builder)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

≺-rec-builder    = ≺-recBuilder
{-# WARNING_ON_USAGE ≺-rec-builder
"Warning: ≺-rec-builder was deprecated in v0.15.
Please use ≺-recBuilder instead."
#-}
≺-well-founded   = ≺-wellFounded
{-# WARNING_ON_USAGE ≺-well-founded
"Warning: ≺-well-founded was deprecated in v0.15.
Please use ≺-wellFounded instead."
#-}
