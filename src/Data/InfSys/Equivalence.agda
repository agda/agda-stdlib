------------------------------------------------------------------------
-- The Agda standard library
--
-- Library for (Generalized) Inference Systems
-- Equivalence between sized types and coinductive records
------------------------------------------------------------------------

{-# OPTIONS --sized-types --guardedness --without-K #-}

open import Agda.Builtin.Equality
open import Codata.Sized.Thunk
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Unary using (_⊆_)
open import Size

module Data.InfSys.Equivalence {𝓁} where

  open import Data.InfSys.Base {𝓁}
  open import Data.InfSys.Coinduction {𝓁}
  open import Data.InfSys.SCoinduction {𝓁}
  open IS

  private
    variable
      U : Set 𝓁
      𝓁c 𝓁p 𝓁n : Level

  {- Equivalence CoInd and SCoInd -}

  coind-size : {is : IS {𝓁c} {𝓁p} {𝓁n} U} →
               CoInd⟦ is ⟧ ⊆ λ u → ∀ {i} → SCoInd⟦ is ⟧ u i
  coind-size p-coind with CoInd⟦_⟧.unfold p-coind
  ... | rn , c , refl , pr =
    sfold (rn , c , refl , λ i → λ where .force → coind-size (pr i))

  size-coind : {is : IS {𝓁c} {𝓁p} {𝓁n} U} →
               (λ u → ∀ {i} → SCoInd⟦ is ⟧ u i) ⊆ CoInd⟦ is ⟧
  size-coind {is = is} p-scoind =
    coind[ is ] (λ u → ∀ {j} → SCoInd⟦ is ⟧ u j) scoind-postfix p-scoind
