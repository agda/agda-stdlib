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
open import Effect.Applicative using (RawApplicative)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
open import Function.Base using (_∘_; const)

private
  variable
    a b c ℓ : Level

-- From the paper:
-- "Functor f is Naperian if there is a type p of ‘positions’ such that fa≃p→a;
-- then p behaves a little like a logarithm of f
-- in particular, if f and g are both Naperian,
-- then Log(f×g)≃Logf+Logg and Log(f.g) ≃ Log f × Log g"

-- RawNaperian contains just the functions, not the proofs
module _ (F : Set a → Set b) c where
  record RawNaperian : Set (suc (a ⊔ c) ⊔ b) where
    field
      rawFunctor : RawFunctor F
      Log : Set c
      index : {A : Set a} → F A → (Log → A)
      tabulate : {A : Set a} → (Log → A) → F A
    open RawFunctor rawFunctor public

  -- Full Naperian has the coherence conditions too.

  record Naperian (S : Setoid a ℓ) : Set (suc (a ⊔ c) ⊔ b ⊔ ℓ) where
    private
      open module S = Setoid S
    field
      rawNaperian : RawNaperian
    open RawNaperian rawNaperian public    

    field
      index-tabulate   : (f : Log → Carrier) → ((l : Log) → index (tabulate f) l ≈ f l)
      natural-tabulate : (f : Carrier → Carrier) (k : Log → Carrier) (l : Log) →
        index (tabulate (f ∘ k)) l ≈ index (f <$> (tabulate k)) l
      natural-index    : (l : Log) (f : Carrier → Carrier) (as : F Carrier) →
        index (f <$> as) l ≈ f (index as l)
    
    tabulate-index : (fx : F Carrier) (l : Log) → index (tabulate (index fx)) l ≈ index fx l
    tabulate-index = index-tabulate ∘ index
   
  PropositionalNaperian : Set (suc (a ⊔ c) ⊔ b)
  PropositionalNaperian = ∀ A → Naperian (setoid A)

  rawApplicative : RawNaperian → RawApplicative F
  rawApplicative rn =
    record
      { rawFunctor = rawFunctor
      ; pure = tabulate ∘ const 
      ; _<*>_ = λ a b → tabulate (λ i → (index a i) (index b i))
      }
      where
        open RawNaperian rn
