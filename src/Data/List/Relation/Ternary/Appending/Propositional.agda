------------------------------------------------------------------------
-- The Agda standard library
--
-- Appending of lists using propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Ternary.Appending.Propositional {a} {A : Set a} where

open import Data.List.Base as List using (List; []; _∷_)
import Data.List.Relation.Binary.Pointwise as Pw
import Data.List.Relation.Ternary.Appending.Setoid as General
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; setoid; refl; cong; cong₂; module ≡-Reasoning)

------------------------------------------------------------------------
-- Re-export the basic combinators

open General hiding (Appending; _++_; break) public

------------------------------------------------------------------------
-- Definition

Appending : List A → List A → List A → Set a
Appending = General.Appending (setoid A)

_++_ : (as bs : List A) → Appending as bs (as List.++ bs)
as ++ bs = Pw.≡⇒Pointwise-≡ refl General.++ Pw.≡⇒Pointwise-≡ refl

break : ∀ {as bs cs} → Appending as bs cs → as List.++ bs ≡ cs
break {as} {bs} {cs} lrs = let (cs₁ , cs₂ , eq , acs , bcs) = General.break lrs in begin
  as  List.++ bs  ≡⟨ cong₂ List._++_ (Pw.Pointwise-≡⇒≡ acs) (Pw.Pointwise-≡⇒≡ bcs) ⟩
  cs₁ List.++ cs₂ ≡⟨ eq ⟩
  cs              ∎ where open ≡-Reasoning
