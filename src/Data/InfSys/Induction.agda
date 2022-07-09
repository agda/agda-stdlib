------------------------------------------------------------------------
-- The Agda standard library
--
-- Library for (Generalized) Inference Systems
-- Inductive interpretation and induction principle
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Equality
open import Data.Product
open import Level
open import Relation.Unary using (_⊆_)

module Data.InfSys.Induction {𝓁} where

  open import Data.InfSys.Base {𝓁}
  open MetaRule
  open IS

  private
    variable
      U : Set 𝓁
      𝓁c 𝓁p 𝓁n : Level

  {- Inductive Interpretation -}

  data Ind⟦_⟧ (is : IS {𝓁c} {𝓁p} {𝓁n} U) :
    U → Set (𝓁 ⊔ 𝓁c ⊔ 𝓁p ⊔ 𝓁n) where
    fold : ∀{u} → ISF[ is ] Ind⟦ is ⟧ u → Ind⟦ is ⟧ u

  {- Induction Principle -}

  ind[_] : ∀{𝓁'} →
           (is : IS {𝓁c} {𝓁p} {𝓁n} U) →  -- IS
           (S : U → Set 𝓁') →            -- specification
           ISClosed is S →               -- S is closed
           Ind⟦ is ⟧ ⊆ S
  ind[ is ] S cl (fold (rn , c , refl , pr)) =
    cl rn c λ i → ind[ is ] S cl (pr i)

  {- Apply Rule -}

  apply-ind : {is : IS {𝓁c} {𝓁p} {𝓁n} U} →
              (rn : is .Names) →
              RClosed (is .rules rn) Ind⟦ is ⟧
  apply-ind {is = is} rn =
    prefix⇒closed
      (is .rules rn) {P = Ind⟦ _ ⟧}
      λ{(c , refl , pr) → fold (rn , c , refl , pr)}

  {- Postfix - Prefix -}

  ind-postfix : {is : IS {𝓁c} {𝓁p} {𝓁n} U} →
                Ind⟦ is ⟧ ⊆ ISF[ is ] Ind⟦ is ⟧
  ind-postfix (fold x) = x

  ind-prefix : {is : IS {𝓁c} {𝓁p} {𝓁n} U} →
               ISF[ is ] Ind⟦ is ⟧ ⊆ Ind⟦ is ⟧
  ind-prefix x = fold x
