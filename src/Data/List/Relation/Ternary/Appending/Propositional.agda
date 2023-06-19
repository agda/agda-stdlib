------------------------------------------------------------------------
-- The Agda standard library
--
-- Appending of lists using propositional equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Ternary.Appending.Propositional
  {a} {A : Set a}
  where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product using (_,_)

import Data.List.Properties as Listₚ
import Data.List.Relation.Binary.Pointwise as Pw

open import Relation.Binary.PropositionalEquality
  using (_≡_; setoid; refl; trans; cong₂; module ≡-Reasoning)

import Data.List.Relation.Ternary.Appending.Setoid (setoid A) as General
import Data.List.Relation.Ternary.Appending.Setoid.Properties (setoid A)
  as Appendingₚ

------------------------------------------------------------------------
-- Re-export the basic combinators

open General public
  hiding (_++_; break)

------------------------------------------------------------------------
-- Definition

infixr 5 _++_ _++[]

_++_ : (as bs : List A) → Appending as bs (as List.++ bs)
as ++ bs = Pw.≡⇒Pointwise-≡ refl General.++ Pw.≡⇒Pointwise-≡ refl

_++[] : (as : List A) → Appending as [] as
as ++[] = Appendingₚ.respʳ-≋ (as ++ []) (Pw.≡⇒Pointwise-≡ (Listₚ.++-identityʳ as))

break : ∀ {as bs cs} → Appending as bs cs → as List.++ bs ≡ cs
break {as} {bs} {cs} lrs = let (cs₁ , cs₂ , eq , acs , bcs) = General.break lrs in begin
  as  List.++ bs  ≡⟨ cong₂ List._++_ (Pw.Pointwise-≡⇒≡ acs) (Pw.Pointwise-≡⇒≡ bcs) ⟩
  cs₁ List.++ cs₂ ≡⟨ eq ⟩
  cs              ∎ where open ≡-Reasoning
