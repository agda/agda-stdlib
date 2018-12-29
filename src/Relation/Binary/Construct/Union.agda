------------------------------------------------------------------------
-- The Agda standard library
--
-- Union of two binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Union where

open import Data.Product
open import Data.Sum
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Definition

_∪_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL A B ℓ₂ → REL A B (ℓ₁ ⊔ ℓ₂)
L ∪ R = λ i j → L i j ⊎ R i j

------------------------------------------------------------------------
-- Properties

module _ {a ℓ} {A : Set a} (L : Rel A ℓ) (R : Rel A ℓ) where

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

module _ {a ℓ} {A : Set a} {L : Rel A ℓ} {R : Rel A ℓ} where

  symmetric : Symmetric L → Symmetric R → Symmetric (L ∪ R)
  symmetric L-sym R-sym = [ inj₁ ∘ L-sym , inj₂ ∘ R-sym ]

  respects : ∀ {p} {P : A → Set p} →
             P Respects L → P Respects R → P Respects (L ∪ R)
  respects resp-L resp-R = [ resp-L , resp-R ]

module _ {a b ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b}
         (≈ : REL A B ℓ₁) (L : REL A B ℓ₂) (R : REL A B ℓ₃) where

  implies : (≈ ⇒ L) ⊎ (≈ ⇒ R) → ≈ ⇒ (L ∪ R)
  implies = [ inj₁ ∘_ , inj₂ ∘_ ]

  irreflexive : Irreflexive ≈ L → Irreflexive ≈ R → Irreflexive ≈ (L ∪ R)
  irreflexive L-irrefl R-irrefl x≈y = [ L-irrefl x≈y , R-irrefl x≈y ]

module _ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {L : REL A B ℓ₁} {R : REL A B ℓ₂} where

  decidable : Decidable L → Decidable R → Decidable (L ∪ R)
  decidable L? R? x y with L? x y | R? x y
  ... | yes Lxy | _       = yes (inj₁ Lxy)
  ... | no  _   | yes Rxy = yes (inj₂ Rxy)
  ... | no ¬Lxy | no ¬Rxy = no [ ¬Lxy , ¬Rxy ]
