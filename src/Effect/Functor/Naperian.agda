------------------------------------------------------------------------
-- The Agda standard library
--
-- Naperian functor
--
-- This file contains definitions of Naperian introduced by Jeremy Gibbons 
-- in the book APLicative Programming with Naperian Functors.
-- https://link.springer.com/chapter/10.1007/978-3-662-54434-1_21
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Functor.Naperian where 

open import Effect.Functor using (RawFunctor)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    b c : Level


-- " Functor f is Naperian if there is a type p of ‘positions’ such that fa≃p→a;
-- then p behaves a little like a logarithm of f
-- in particular, if f and g are both Naperian, then Log(f×g)≃Logf+Logg and Log(f.g) ≃ Log f × Log g"
-- APLicative Programming with Naperian Functors. Jeremy Gibbons.

-- RawNaperian contains just the functions, not the proofs
record RawNaperian {F : Set b → Set c} (d : Level) (RF : RawFunctor F) : Set (suc (b ⊔ d) ⊔ c) where
  field
    Log : Set d
    index : ∀ {A} → F A → (Log → A)
    tabulate : ∀ {A} → (Log → A) → F A

-- Full Naperian has the coherence conditions too. Propositional version (hard to work with).
record Naperian {F : Set b → Set c} (d : Level) (RF : RawFunctor F) : Set (suc (b ⊔ d) ⊔ c) where
  field
    rawNaperian : RawNaperian d RF
  open RawNaperian rawNaperian public
  field
    tabulate-index : ∀ {A} → (fa : F A) → tabulate (index fa) ≡ fa
    index-tabulate : ∀ {A} → (f : Log → A) → ((l : Log) → index (tabulate f) l ≡ f l)
