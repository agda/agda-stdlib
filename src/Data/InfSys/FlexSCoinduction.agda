------------------------------------------------------------------------
-- The Agda standard library
--
-- Library for (Generalized) Inference Systems
-- Interpretation generate by corules
-- Bounded coinduction principle
------------------------------------------------------------------------

{-# OPTIONS --sized-types --without-K #-}

open import Agda.Builtin.Equality
open import Codata.Sized.Thunk
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Unary using (_⊆_)
open import Size

module Data.InfSys.FlexSCoinduction {𝓁} where

  open import Data.InfSys.Base {𝓁}
  open import Data.InfSys.Induction {𝓁}
  open import Data.InfSys.SCoinduction {𝓁}
  open MetaRule
  open IS

  private
    variable
      U : Set 𝓁
      𝓁c 𝓁p 𝓁n : Level
      𝓁n' 𝓁' : Level

  {- Generalized inference systems -}

  SFCoInd⟦_,_⟧ : (I : IS {𝓁c} {𝓁p} {𝓁n} U) →
                 (C : IS {𝓁c} {𝓁p} {𝓁n'} U) →
                 U → Size → Set _
  SFCoInd⟦ I , C ⟧ = SCoInd⟦ I ⊓ Ind⟦ I ∪ C ⟧ ⟧

  {- Bounded Coinduction Principle -}

  bdc-lem : ∀{𝓁''} →
            (I : IS {𝓁c} {𝓁p} {𝓁n} U) →
            (S : U → Set 𝓁') →
            (Q : U → Set 𝓁'') →
            S ⊆ Q →
            S ⊆ ISF[ I ] S →
            S ⊆ ISF[ I ⊓ Q ] S
  bdc-lem _ _ _ bd cn Su with cn Su
  ... | rn , c , refl , pr = rn , (c , bd Su) , refl , pr

  bounded-scoind[_,_] : (I : IS {𝓁c} {𝓁p} {𝓁n} U) →
                        (C : IS {𝓁c} {𝓁p} {𝓁n'} U) →
                        (S : U → Set 𝓁') →
                        S ⊆ Ind⟦ I ∪ C ⟧ → -- S is bounded w.r.t. I ∪ C
                        S ⊆ ISF[ I ] S →   -- S is consistent w.r.t. I
                        S ⊆ (λ u → ∀{i} → SFCoInd⟦ I , C ⟧ u i)
  bounded-scoind[ I , C ] S bd cn Su =
    scoind[ I ⊓ Ind⟦ I ∪ C ⟧ ] S (bdc-lem I S Ind⟦ I ∪ C ⟧ bd cn) Su

  {- Get Ind from SFCoInd -}

  sfcoind-to-ind : {is : IS {𝓁c} {𝓁p} {𝓁n} U}
                   {cois : IS {𝓁c} {𝓁p} {𝓁n'} U} →
                   (λ u → ∀{i} → SFCoInd⟦ is , cois ⟧ u i)
                     ⊆ Ind⟦ is ∪ cois ⟧
  sfcoind-to-ind co with co
  sfcoind-to-ind co | sfold (_ , (_ , sd) , refl , _) = sd

  {- Apply Rule -}

  apply-sfcoind : {is : IS {𝓁c} {𝓁p} {𝓁n} U}
                  {cois : IS {𝓁c} {𝓁p} {𝓁n'} U} →
                  (rn : is .Names) →
                  RClosed
                    (is .rules rn)
                    (λ u → ∀{i} → SFCoInd⟦ is , cois ⟧ u i)
  apply-sfcoind rn c pr =
    apply-scoind rn
      (c , apply-ind (inj₁ rn) c λ i → sfcoind-to-ind (pr i)) pr

  {- Postfix - Prefix -}

  sfcoind-postfix : {is : IS {𝓁c} {𝓁p} {𝓁n} U}
                    {cois : IS {𝓁c} {𝓁p} {𝓁n'} U} →
                    (λ u → ∀{i} → SFCoInd⟦ is , cois ⟧ u i)
                      ⊆ ISF[ is ]
                        (λ u → ∀{i} → SFCoInd⟦ is , cois ⟧ u i)
  sfcoind-postfix SFCoInd with SFCoInd
  ... | sfold (rn , (c , _) , refl , pr) =
    rn , c , refl , λ i → (pr i) .force

  sfcoind-prefix : {is : IS {𝓁c} {𝓁p} {𝓁n} U}
                   {cois : IS {𝓁c} {𝓁p} {𝓁n'} U} →
                   ISF[ is ] (λ u → ∀{i} → SFCoInd⟦ is , cois ⟧ u i)
                     ⊆ λ u → ∀{i} → SFCoInd⟦ is , cois ⟧ u i
  sfcoind-prefix (rn , c , refl , pr) = apply-sfcoind rn c pr
