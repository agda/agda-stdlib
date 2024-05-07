------------------------------------------------------------------------
-- The Agda standard library
--
-- Naperian functor
--
-- Definitions of Naperian Functors, as named by Hancock and McBride,
-- and subsequently documented by Jeremy Gibbons 
-- in the article "APLicative Programming with Naperian Functors"
-- which appeared at ESOP 2017.
-- https://link.springer.com/chapter/10.1007/978-3-662-54434-1_21
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Functor.Naperian where 

open import Effect.Functor using (RawFunctor)
open import Function.Bundles using (_⟶ₛ_; _⟨$⟩_; Func)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    a b c e f : Level
    A : Set a

-- From the paper:
-- "Functor f is Naperian if there is a type p of ‘positions’ such that fa≃p→a;
-- then p behaves a little like a logarithm of f
-- in particular, if f and g are both Naperian,
-- then Log(f×g)≃Logf+Logg and Log(f.g) ≃ Log f × Log g"

-- RawNaperian contains just the functions, not the proofs
record RawNaperian {F : Set a → Set b} c (RF : RawFunctor F) : Set (suc (a ⊔ c) ⊔ b) where
  field
    Log : Set c
    index : F A → (Log → A)
    tabulate : (Log → A) → F A

-- Full Naperian has the coherence conditions too.
-- Propositional version (hard to work with).

module Propositional where
  record Naperian {F : Set a → Set b} c (RF : RawFunctor F) : Set (suc (a ⊔ c) ⊔ b) where
    field
      rawNaperian : RawNaperian c RF
    open RawNaperian rawNaperian public
    field
      tabulate-index : (fa : F A) → tabulate (index fa) ≡ fa
      index-tabulate : (f : Log → A) → ((l : Log) → index (tabulate f) l ≡ f l)

module _ {F : Set a → Set b} c (RF : RawFunctor F) where
  private
    FA : (AS : Setoid a e) → (rn : RawNaperian c RF) → Setoid b (c ⊔ e)
    FA AS rn = record
      { Carrier = F X
      ; _≈_ = λ fx fy → (l : Log) → index fx l ≈ index fy l
      ; isEquivalence = record
        { refl = λ _ → refl
        ; sym = λ eq l → sym (eq l)
        ; trans = λ i≈j j≈k l → trans (i≈j l) (j≈k l)
        }
      }
      where
        open Setoid AS renaming (Carrier to X)
        open RawNaperian rn
        
  record Naperian (AS : Setoid a e) : Set (suc a ⊔ b ⊔ suc c ⊔ e) where
    field
      rawNaperian : RawNaperian c RF
    open RawNaperian rawNaperian public
    private
      module FS = Setoid (FA AS rawNaperian)
      module A = Setoid AS
    field
      tabulate-index : (fx : F A.Carrier) → tabulate (index fx) FS.≈ fx
      index-tabulate : (f : Log → A.Carrier) → ((l : Log) → index (tabulate f) l A.≈ f l)
