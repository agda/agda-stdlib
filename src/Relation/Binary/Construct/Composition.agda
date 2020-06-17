------------------------------------------------------------------------
-- The Agda standard library
--
-- Composition of two binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Composition where

open import Data.Product
open import Function.Base
open import Level
open import Relation.Binary

private
  variable
    a b c ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definition

_;_ : {A : Set a} {B : Set b} {C : Set c} →
      REL A B ℓ₁ → REL B C ℓ₂ → REL A C (b ⊔ ℓ₁ ⊔ ℓ₂)
L ; R = λ i j → ∃ λ k → L i k × R k j

------------------------------------------------------------------------
-- Properties

module _ (L : Rel A ℓ₁) (R : Rel A ℓ₂) where

  reflexive : Reflexive L → Reflexive R → Reflexive (L ; R)
  reflexive L-refl R-refl = _ , L-refl , R-refl

  respects : ∀ {p} {P : A → Set p} →
             P Respects L → P Respects R → P Respects (L ; R)
  respects resp-L resp-R (k , Lik , Rkj) = resp-R Rkj ∘ resp-L Lik

module _ {≈ : Rel A ℓ} (L : REL A B ℓ₁) (R : REL B C ℓ₂) where

  respectsˡ : L Respectsˡ ≈ → (L ; R) Respectsˡ ≈
  respectsˡ Lˡ i≈i′ (k , Lik , Rkj) = k , Lˡ i≈i′ Lik , Rkj

module _ {≈ : Rel C ℓ} (L : REL A B ℓ₁) (R : REL B C ℓ₂) where

  respectsʳ : R Respectsʳ ≈ → (L ; R) Respectsʳ ≈
  respectsʳ Rʳ j≈j′ (k , Lik , Rkj) = k , Lik , Rʳ j≈j′ Rkj

module _ {≈ : Rel A ℓ} (L : REL A B ℓ₁) (R : REL B A ℓ₂) where

  respects₂ :  L Respectsˡ ≈ → R Respectsʳ ≈ → (L ; R) Respects₂ ≈
  respects₂ Lˡ Rʳ = respectsʳ L R Rʳ , respectsˡ L R Lˡ

module _ {≈ : REL A B ℓ} (L : REL A B ℓ₁) (R : Rel B ℓ₂) where

  impliesˡ : Reflexive R → (≈ ⇒ L) → (≈ ⇒ L ; R)
  impliesˡ R-refl ≈⇒L {i} {j} i≈j = j , ≈⇒L i≈j , R-refl

module _ {≈ : REL A B ℓ} (L : Rel A ℓ₁) (R : REL A B ℓ₂) where

  impliesʳ : Reflexive L → (≈ ⇒ R) → (≈ ⇒ L ; R)
  impliesʳ L-refl ≈⇒R {i} {j} i≈j = i , L-refl , ≈⇒R i≈j

module _ (L : Rel A ℓ₁) (R : Rel A ℓ₂) (comm : R ; L ⇒ L ; R) where

  transitive : Transitive L → Transitive R → Transitive (L ; R)
  transitive L-trans R-trans {i} {j} {k} (x , Lix , Rxj) (y , Ljy , Ryk) =
    let z , Lxz , Rzy = comm (j , Rxj , Ljy) in z , L-trans Lix  Lxz , R-trans Rzy Ryk

  isPreorder : {≈ : Rel A ℓ} → IsPreorder ≈ L → IsPreorder ≈ R → IsPreorder ≈ (L ; R)
  isPreorder Oˡ Oʳ = record
    { isEquivalence = Oˡ.isEquivalence
    ; reflexive     = impliesˡ L R Oʳ.refl Oˡ.reflexive
    ; trans         = transitive Oˡ.trans Oʳ.trans
    }
    where module Oˡ = IsPreorder Oˡ; module Oʳ = IsPreorder Oʳ
