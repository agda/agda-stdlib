------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise equality for indexed containers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Container.Indexed.Relation.Binary.Pointwise where

open import Data.Product.Base using (_,_; Σ-syntax)
open import Function.Base using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary using (REL; _⇒_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Data.Container.Indexed.Core using (Container; Subtrees; ⟦_⟧)

private variable
  ℓᵉ ℓᵉ′ ℓᵖ ℓˢ ℓˣ ℓʸ : Level
  I O : Set _

------------------------------------------------------------------------
-- Equality, parametrised on an underlying relation.

-- Since ⟦_⟧ is a Σ-type, not a record, I'd say Pointwise should also be
-- a Σ-type, not a record. Maybe we need to update module
-- `Data.Container.Relation.Binary.Pointwise` accordingly...
--
-- record Pointwise  : Set (ℓˢ ⊔ ℓᵖ ⊔ ℓᵉ) where
--   constructor _,_
--   field shape    : c ≡ c'
--         position : Eqs shape xs ys

module _ (C : Container I O ℓˢ ℓᵖ)
         {X : I → Set ℓˣ} {Y : I → Set ℓʸ} (R : (i : I) → REL (X i) (Y i) ℓᵉ)
         (o : O)
         ((c  , xs) : ⟦ C ⟧ X o)
         ((c' , ys) : ⟦ C ⟧ Y o)
  where
  open Container C

  Eqs : c ≡ c' → Subtrees C X o c → Subtrees C Y o c' → Set _
  Eqs refl xs ys = (r : Response c) → R (next c r) (xs r) (ys r)

  Pointwise = Σ[ eq ∈ c ≡ c' ] Eqs eq xs ys

------------------------------------------------------------------------
-- Operations

module _ {C : Container I O ℓˢ ℓᵖ}
         {X : I → Set ℓˣ} {Y : I → Set ℓʸ}
         {R  : (i : I) → REL (X i) (Y i) ℓᵉ}
         {R′ : (i : I) → REL (X i) (Y i) ℓᵉ′}
         where

  map : (R⇒R′ : ∀ i → R i ⇒ R′ i) {o : O} → Pointwise C R o ⇒ Pointwise C R′ o
  map R⇒R′ (refl , f) = refl , R⇒R′ _ ∘ f
