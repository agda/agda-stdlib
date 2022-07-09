------------------------------------------------------------------------
-- The Agda standard library
--
-- Library for (Generalized) Inference Systems
-- Coniductive interpretation and coinduction principle
------------------------------------------------------------------------

{-# OPTIONS --sized-types --without-K #-}

open import Agda.Builtin.Equality
open import Codata.Sized.Thunk
open import Data.Product
open import Level
open import Relation.Unary using (_⊆_)
open import Size

module Data.InfSys.SCoinduction {𝓁} where

  open import Data.InfSys.Base {𝓁}
  open import Data.InfSys.Induction {𝓁}
  open MetaRule
  open IS

  private
    variable
      U : Set 𝓁
      𝓁c 𝓁p 𝓁n : Level

  {- Coinductive interpretation -}

  data SCoInd⟦_⟧ (is : IS {𝓁c} {𝓁p} {𝓁n} U) :
    U → Size → Set (𝓁 ⊔ 𝓁c ⊔ 𝓁p ⊔ 𝓁n) where
    sfold : ∀ {u i} →
            ISF[ is ] (λ u → Thunk (SCoInd⟦ is ⟧ u) i) u →
            SCoInd⟦ is ⟧ u i

  {- Coinduction Principle -}

  scoind[_] : ∀{𝓁'} →
              (is : IS {𝓁c} {𝓁p} {𝓁n} U) →
              (S : U → Set 𝓁') →
              S ⊆ ISF[ is ] S →     -- S is consistent
              S ⊆ λ u → ∀{i} → SCoInd⟦ is ⟧ u i
  scoind[ is ] S cn Su with cn Su
  ... | rn , c , refl , pr =
    sfold (rn , c , refl ,
      λ i → λ where .force → scoind[ is ] S cn (pr i))

  {- Apply Rule -}

  apply-scoind : {is : IS {𝓁c} {𝓁p} {𝓁n} U} →
                 (rn : is .Names) →
                 RClosed (is .rules rn) (λ u → ∀{i} → SCoInd⟦ is ⟧ u i)
  apply-scoind {is = is} rn =
    prefix⇒closed
      (is .rules rn) {P = λ u → ∀{i} → SCoInd⟦ is ⟧ u i }
      λ{(c , refl , pr) →
        sfold (rn , c , refl , λ i → λ where .force → pr i)}

  {- Postfix - Prefix -}

  scoind-postfix : {is : IS {𝓁c} {𝓁p} {𝓁n} U} →
                   (λ u → ∀{i} → SCoInd⟦ is ⟧ u i)
                     ⊆ ISF[ is ] (λ u → ∀{i} → SCoInd⟦ is ⟧ u i)
  scoind-postfix p-scoind with p-scoind
  ... | sfold (rn , c , refl , pr) = rn , c , refl , λ i → (pr i) .force

  scoind-prefix : {is : IS {𝓁c} {𝓁p} {𝓁n} U} →
                  ISF[ is ] (λ u → ∀{i} → SCoInd⟦ is ⟧ u i)
                    ⊆ λ u → ∀{i} → SCoInd⟦ is ⟧ u i
  scoind-prefix (rn , c , refl , pr) = apply-scoind rn c pr
