------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of Magma homomorphisms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Algebra using (Magma)
import Algebra.Morphism.Definitions as Definitions
import Algebra.Morphism.ToSetoid as ToSetoid
open import Function using (id; _∘_)
open import Relation.Binary using (_Preserves_⟶_)
import Relation.Binary.EqReasoning as EqR
open import Relation.Unary using (Pred)


module Algebra.Morphism.TwoMagmas {α α= β β=} (M : Magma α α=) (M' : Magma β β=)
  where
open Magma M using (_≈_; _∙_; setoid) renaming (Carrier to A; refl to ≈refl)
open Magma M' using () renaming (Carrier to B; _≈_ to _≈'_; sym to ≈'sym;
                                 _∙_ to _∙'_; ∙-cong to ∙'cong; setoid to setoid')

open Definitions A B _≈'_ using (Homomorphic₂)
open Definitions B A _≈_  using () renaming (Homomorphic₂ to Homomorphic₂')
open ToSetoid A setoid using (_≈∘_)
open ToSetoid B setoid' using () renaming (_≈∘_ to _≈'∘_)
open EqR setoid

id' : B → B
id' = id

IsHomo :  Pred (A → B) _
IsHomo f =  Homomorphic₂ f _∙_ _∙'_

IsHomo-rev :  Pred (B → A) _
IsHomo-rev f =  Homomorphic₂' f _∙'_ _∙_

---------------------------------------------------------------------------------
-- If f and g are mutually inverse maps between A and B, g is congruent,
-- f is a homomorphism, then g is a homomorphism.

IsHomo⇒IsHomo-rev : (f : A → B)              → (g : B → A) →
                    (g Preserves _≈'_ ⟶ _≈_) → g ∘ f ≈∘ id → f ∘ g ≈'∘ id' →
                                                             IsHomo f → IsHomo-rev g
IsHomo⇒IsHomo-rev f g gCong g∘f=id f∘g=id fHomo y y' =  begin
  g (y ∙' y')       ≈⟨ gCong (∙'cong y=fx y'=fx') ⟩
  g (f x ∙' f x')   ≈⟨ gCong (≈'sym (fHomo x x')) ⟩
  g (f (x ∙ x'))    ≈⟨ g∘f=id (x ∙ x') ⟩
  x ∙ x'            ≈⟨ ≈refl ⟩
  g y ∙ g y'        ∎
  where
  x    =  g y;                x'     =  g y'
  y=fx =  ≈'sym (f∘g=id y);   y'=fx' =  ≈'sym (f∘g=id y')

