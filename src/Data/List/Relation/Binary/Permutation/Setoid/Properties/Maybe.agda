------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutations using setoid equality (on Maybe elements)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Setoid.Properties.Maybe where

open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Bundles using (Setoid)

open import Level using (Level)
open import Function.Base using (_∘_; _$_)

open import Data.List.Base using (catMaybes; mapMaybe)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
open import Data.List.Relation.Binary.Permutation.Setoid.Properties

open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Relation.Binary.Pointwise using (nothing; just)
  renaming (setoid to setoidᴹ)

private
  variable
    a b ℓ ℓ′ : Level

------------------------------------------------------------------------
-- catMaybes

module _ (sᴬ : Setoid a ℓ) where
  open Setoid sᴬ using (_≈_)
  open Permutation sᴬ

  private sᴹ = setoidᴹ sᴬ
  open Setoid sᴹ using () renaming (_≈_ to _≈ᴹ_)
  open Permutation sᴹ using () renaming (_↭_ to _↭ᴹ_)

  catMaybes-↭ : ∀ {xs ys} → xs ↭ᴹ ys → catMaybes xs ↭ catMaybes ys
  catMaybes-↭ (refl p) = refl (pointwise p)
    where
    pointwise : ∀ {xs ys} → Pointwise _≈ᴹ_ xs ys →
                Pointwise _≈_ (catMaybes xs) (catMaybes ys)
    pointwise []             = []
    pointwise (just p  ∷ ps) = p ∷ pointwise ps
    pointwise (nothing ∷ ps) = pointwise ps
  catMaybes-↭ (trans xs↭ ↭ys)              = trans (catMaybes-↭ xs↭) (catMaybes-↭ ↭ys)
  catMaybes-↭ (prep nothing    xs↭)        = catMaybes-↭ xs↭
  catMaybes-↭ (prep (just x~y) xs↭)        = prep x~y $ catMaybes-↭ xs↭
  catMaybes-↭ (swap nothing  nothing  xs↭) = catMaybes-↭ xs↭
  catMaybes-↭ (swap nothing  (just y) xs↭) = prep y $ catMaybes-↭ xs↭
  catMaybes-↭ (swap (just x) nothing  xs↭) = prep x $ catMaybes-↭ xs↭
  catMaybes-↭ (swap (just x) (just y) xs↭) = swap x y $ catMaybes-↭ xs↭

------------------------------------------------------------------------
-- mapMaybe

module _ (sᴬ : Setoid a ℓ) (sᴮ : Setoid b ℓ′) where
  open Setoid sᴬ using () renaming (_≈_ to _≈ᴬ_)
  open Permutation sᴬ using () renaming (_↭_ to _↭ᴬ_)
  open Permutation sᴮ using () renaming (_↭_ to _↭ᴮ_)

  private sᴹᴮ = setoidᴹ sᴮ
  open Setoid sᴹᴮ using () renaming (_≈_ to _≈ᴹᴮ_)

  mapMaybe-↭ : ∀ {f} → f Preserves _≈ᴬ_ ⟶ _≈ᴹᴮ_ →
               ∀ {xs ys} → xs ↭ᴬ ys → mapMaybe f xs ↭ᴮ mapMaybe f ys
  mapMaybe-↭ pres = catMaybes-↭ sᴮ ∘ map⁺ sᴬ sᴹᴮ pres
