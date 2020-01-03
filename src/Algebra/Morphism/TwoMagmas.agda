------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of Magma homomorphisms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Magma)
import Algebra.Morphism.Definitions as Definitions
open import Data.Product using (_×_; _,_)
open import Function using (id; _∘_)
open import Relation.Binary using (_Preserves_⟶_)
import Relation.Binary.EqReasoning as EqR
open import Relation.Unary using (Pred)


module Algebra.Morphism.TwoMagmas {α α= β β=} (M : Magma α α=) (M' : Magma β β=)
  where
open Magma M using (_≈_; _∙_; setoid) renaming (Carrier to A; refl to ≈refl)
open Magma M' using () renaming (Carrier to B; _≈_ to _≈'_; sym to ≈'sym;
                                               _∙_ to _∙'_; ∙-cong to ∙'cong)
open Definitions A B _≈'_ using (Homomorphic₂)
open Definitions B A _≈_  using () renaming (Homomorphic₂ to Homomorphic₂')
open import Function.Definitions _≈_ _≈'_ using (Inverseᵇ)
open EqR setoid

---------------------------------------------------------------------------------
-- If f and g are mutually inverse maps between A and B, g is congruent,
-- f is a homomorphism, then g is a homomorphism.

IsHomo⇒IsHomo-rev : (f : A → B)              → (g : B → A)  →
                    (g Preserves _≈'_ ⟶ _≈_) → Inverseᵇ f g →
                    Homomorphic₂ f _∙_ _∙'_  → Homomorphic₂' g _∙'_ _∙_
IsHomo⇒IsHomo-rev f g gCong (f∘g=id , g∘f=id) fHomo y y' = begin
  g (y ∙' y')       ≈⟨ gCong (∙'cong y=fx y'=fx') ⟩
  g (f x ∙' f x')   ≈⟨ gCong (≈'sym (fHomo x x')) ⟩
  g (f (x ∙ x'))    ≈⟨ g∘f=id (x ∙ x') ⟩
  x ∙ x'            ≈⟨ ≈refl ⟩
  g y ∙ g y'        ∎
  where
  x    = g y;                x'     = g y'
  y=fx = ≈'sym (f∘g=id y);   y'=fx' = ≈'sym (f∘g=id y')
