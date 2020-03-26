------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of Magma homomorphisms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Algebra using (Magma)
import Algebra.Morphism.Definitions as Definitions
open import Data.Product using (_,_)
open import Function using (id; _∘_)
open import Function.Definitions using (Inverseᵇ)
open import Relation.Binary using (_Preserves_⟶_)
import Relation.Binary.Reasoning.Setoid as EqR
open import Relation.Unary using (Pred)


module Algebra.Morphism.TwoMagmas {α α= β β=} (M : Magma α α=) (M' : Magma β β=)
  where
open Magma M using (_≈_; _∙_; setoid) renaming (Carrier to A; refl to ≈refl)
open Magma M' using () renaming (Carrier to B; _≈_ to _≈'_; sym to ≈'sym;
                                 _∙_ to _∙'_; ∙-cong to ∙'cong; setoid to setoid')

open Definitions A B _≈'_ using (Homomorphic₂)
open Definitions B A _≈_  using () renaming (Homomorphic₂ to Homomorphic₂')
open EqR setoid

IsHomo :  Pred (A → B) _
IsHomo f =  Homomorphic₂ f _∙_ _∙'_

IsHomo-rev :  Pred (B → A) _
IsHomo-rev f =  Homomorphic₂' f _∙'_ _∙_

---------------------------------------------------------------------------------
-- If f and g are mutually inverse maps between A and B, g is congruent,
-- f is a homomorphism, then g is a homomorphism.

IsHomo⇒IsHomo-rev : {f : A → B}              → {g : B → A}           →
                    (g Preserves _≈'_ ⟶ _≈_) → Inverseᵇ _≈_ _≈'_ f g →
                    IsHomo f                 → IsHomo-rev g

IsHomo⇒IsHomo-rev {f} {g} g-cong ( f∘g=id , g∘f=id) fHomo b b' = begin
  g (b ∙' b')       ≈⟨ g-cong (∙'cong b=fa b'=fa') ⟩
  g (f a ∙' f a')   ≈⟨ g-cong (≈'sym (fHomo a a')) ⟩
  g (f (a ∙ a'))    ≈⟨ g∘f=id (a ∙ a') ⟩
  a ∙ a'            ≡⟨⟩
  g b ∙ g b'        ∎
  where
  a    =  g b;                a'     =  g b'
  b=fa =  ≈'sym (f∘g=id b);   b'=fa' =  ≈'sym (f∘g=id b')
