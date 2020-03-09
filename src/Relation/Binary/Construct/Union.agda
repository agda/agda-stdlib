------------------------------------------------------------------------
-- The Agda standard library
--
-- Union of two binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Union where

open import Data.Product
open import Data.Sum.Base as Sum
open import Function using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Sum using (_⊎-dec_)

private
  variable
    a b ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

_∪_ : ∀ {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL A B ℓ₂ → REL A B (ℓ₁ ⊔ ℓ₂)
L ∪ R = λ i j → L i j ⊎ R i j

------------------------------------------------------------------------
-- Properties

module _ (L : Rel A ℓ) (R : Rel A ℓ) where

  reflexive : Reflexive L ⊎ Reflexive R → Reflexive (L ∪ R)
  reflexive (inj₁ L-refl) = inj₁ L-refl
  reflexive (inj₂ R-refl) = inj₂ R-refl

  total : Total L ⊎ Total R → Total (L ∪ R)
  total (inj₁ L-total) x y = [ inj₁ ∘ inj₁ , inj₂ ∘ inj₁ ] (L-total x y)
  total (inj₂ R-total) x y = [ inj₁ ∘ inj₂ , inj₂ ∘ inj₂ ] (R-total x y)

  min : ∀ {⊤} → Minimum L ⊤ ⊎ Minimum R ⊤ → Minimum (L ∪ R) ⊤
  min = [ inj₁ ∘_ , inj₂ ∘_ ]

  max : ∀ {⊥} → Maximum L ⊥ ⊎ Maximum R ⊥ → Maximum (L ∪ R) ⊥
  max = [ inj₁ ∘_ , inj₂ ∘_ ]

module _ {L : Rel A ℓ} {R : Rel A ℓ} where

  symmetric : Symmetric L → Symmetric R → Symmetric (L ∪ R)
  symmetric L-sym R-sym = [ inj₁ ∘ L-sym , inj₂ ∘ R-sym ]

  respects : ∀ {p} {P : A → Set p} →
             P Respects L → P Respects R → P Respects (L ∪ R)
  respects resp-L resp-R = [ resp-L , resp-R ]

module _ {≈ : Rel A ℓ₁} (L : REL A B ℓ₂) (R : REL A B ℓ₃) where

  respˡ : L Respectsˡ ≈ → R Respectsˡ ≈ → (L ∪ R) Respectsˡ ≈
  respˡ Lˡ Rˡ x≈y = Sum.map (Lˡ x≈y) (Rˡ x≈y)

module _ {≈ : Rel B ℓ₁} (L : REL A B ℓ₂) (R : REL A B ℓ₃) where

  respʳ : L Respectsʳ ≈ → R Respectsʳ ≈ → (L ∪ R) Respectsʳ ≈
  respʳ Lʳ Rʳ x≈y = Sum.map (Lʳ x≈y) (Rʳ x≈y)

module _ {≈ : Rel A ℓ₁} {L : Rel A ℓ₂} {R : Rel A ℓ₃} where

  resp₂ : L Respects₂ ≈ → R Respects₂ ≈ → (L ∪ R) Respects₂ ≈
  resp₂ (Lʳ , Lˡ) (Rʳ , Rˡ) = respʳ L R Lʳ Rʳ , respˡ L R Lˡ Rˡ

module _ (≈ : REL A B ℓ₁) (L : REL A B ℓ₂) (R : REL A B ℓ₃) where

  implies : (≈ ⇒ L) ⊎ (≈ ⇒ R) → ≈ ⇒ (L ∪ R)
  implies = [ inj₁ ∘_ , inj₂ ∘_ ]

  irreflexive : Irreflexive ≈ L → Irreflexive ≈ R → Irreflexive ≈ (L ∪ R)
  irreflexive L-irrefl R-irrefl x≈y = [ L-irrefl x≈y , R-irrefl x≈y ]

module _ {L : REL A B ℓ₁} {R : REL A B ℓ₂} where

  decidable : Decidable L → Decidable R → Decidable (L ∪ R)
  decidable L? R? x y = L? x y ⊎-dec R? x y
