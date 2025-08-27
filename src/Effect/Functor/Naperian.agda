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
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Properties as ≡ using (setoid)
open import Function.Base using (_∘_)

private
  variable
    a b c ℓ : Level
    A : Set a

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
      index : F A → (Log → A)
      tabulate : (Log → A) → F A
    open RawFunctor rawFunctor public

  -- Full Naperian has the coherence conditions too.

  record Naperian (S : Setoid a ℓ) : Set (suc (a ⊔ c) ⊔ b ⊔ ℓ) where
    field
      rawNaperian : RawNaperian
    open RawNaperian rawNaperian public
    open module S = Setoid S
    private
      FS : Setoid b (c ⊔ ℓ)
      FS = record
        { _≈_ = λ (fx fy : F Carrier) → ∀ (l : Log) → index fx l ≈ index fy l
        ; isEquivalence = record
          { refl = λ _ → refl
          ; sym = λ eq l → sym (eq l)
          ; trans = λ i≈j j≈k l → trans (i≈j l) (j≈k l)
          }
        }
      module FS = Setoid FS
    field
      index-tabulate   : (f : Log → Carrier) → ((l : Log) → index (tabulate f) l ≈ f l)
      natural-tabulate : (f : Carrier → Carrier) (k : Log → Carrier) → (tabulate (f ∘ k)) FS.≈ (f <$> (tabulate k))
      natural-index    : (f : Carrier → Carrier) (as : F Carrier) (l : Log) → (index (f <$> as) l) ≈ f (index as l)
    
    tabulate-index : (fx : F Carrier) → tabulate (index fx) FS.≈ fx
    tabulate-index = index-tabulate ∘ index
    
  PropositionalNaperian : Set (suc (a ⊔ c) ⊔ b)
  PropositionalNaperian = ∀ A → Naperian (≡.setoid A)
