------------------------------------------------------------------------
-- The Agda standard library
--
-- Intersection of two binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Intersection where

open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Definition

_∩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL A B ℓ₂ → REL A B (ℓ₁ ⊔ ℓ₂)
L ∩ R = λ i j → L i j × R i j

------------------------------------------------------------------------
-- Properties

module _ {a ℓ₁ ℓ₂} {A : Set a} (L : Rel A ℓ₁) (R : Rel A ℓ₂) where

  reflexive : Reflexive L → Reflexive R → Reflexive (L ∩ R)
  reflexive L-refl R-refl = L-refl , R-refl

  symmetric : Symmetric L → Symmetric R → Symmetric (L ∩ R)
  symmetric L-sym R-sym = map L-sym R-sym

  transitive : Transitive L → Transitive R → Transitive (L ∩ R)
  transitive L-trans R-trans = zip L-trans R-trans

  respects : ∀ {p} (P : A → Set p) →
             P Respects L ⊎ P Respects R → P Respects (L ∩ R)
  respects P resp (Lxy , Rxy) = [ (λ x → x Lxy) , (λ x → x Rxy) ] resp

  min : ∀ {⊤} → Minimum L ⊤ → Minimum R ⊤ → Minimum (L ∩ R) ⊤
  min L-min R-min = < L-min , R-min >

  max : ∀ {⊥} → Maximum L ⊥ → Maximum R ⊥ → Maximum (L ∩ R) ⊥
  max L-max R-max = < L-max , R-max >

module _ {a b ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b}
         (≈ : REL A B ℓ₁) {L : REL A B ℓ₂} {R : REL A B ℓ₃} where

  implies : (≈ ⇒ L) → (≈ ⇒ R) → ≈ ⇒ (L ∩ R)
  implies ≈⇒L ≈⇒R = < ≈⇒L , ≈⇒R >

module _ {a b ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b}
         (≈ : REL A B ℓ₁) (L : REL A B ℓ₂) (R : REL A B ℓ₃) where

  irreflexive : Irreflexive ≈ L ⊎ Irreflexive ≈ R → Irreflexive ≈ (L ∩ R)
  irreflexive irrefl x≈y (Lxy , Rxy) = [ (λ x → x x≈y Lxy) , (λ x → x x≈y Rxy) ] irrefl

module _ {a ℓ₁ ℓ₂ ℓ₃} {A : Set a}
         (≈ : Rel A ℓ₁) (L : Rel A ℓ₂) (R : Rel A ℓ₃) where

  respectsˡ : L Respectsˡ ≈ → R Respectsˡ ≈ → (L ∩ R) Respectsˡ ≈
  respectsˡ L-resp R-resp x≈y = map (L-resp x≈y) (R-resp x≈y)

  respectsʳ : L Respectsʳ ≈ → R Respectsʳ ≈ → (L ∩ R) Respectsʳ ≈
  respectsʳ L-resp R-resp x≈y = map (L-resp x≈y) (R-resp x≈y)

  respects₂ : L Respects₂ ≈ → R Respects₂ ≈ → (L ∩ R) Respects₂ ≈
  respects₂ (Lʳ , Lˡ) (Rʳ , Rˡ) = respectsʳ Lʳ Rʳ , respectsˡ Lˡ Rˡ

  antisymmetric : Antisymmetric ≈ L ⊎ Antisymmetric ≈ R → Antisymmetric ≈ (L ∩ R)
  antisymmetric (inj₁ L-antisym) (Lxy , _) (Lyx , _) = L-antisym Lxy Lyx
  antisymmetric (inj₂ R-antisym) (_ , Rxy) (_ , Ryx) = R-antisym Rxy Ryx

module _ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {L : REL A B ℓ₁} {R : REL A B ℓ₂} where

  decidable : Decidable L → Decidable R → Decidable (L ∩ R)
  decidable L? R? x y with L? x y | R? x y
  ... | no ¬Lxy | _       = no (¬Lxy ∘ proj₁)
  ... | yes _   | no ¬Rxy = no (¬Rxy ∘ proj₂)
  ... | yes Lxy | yes Rxy = yes (Lxy , Rxy)

------------------------------------------------------------------------
-- Structures

module _ {a ℓ₁ ℓ₂} {A : Set a} {L : Rel A ℓ₁} {R : Rel A ℓ₂} where

  isEquivalence : IsEquivalence L → IsEquivalence R → IsEquivalence (L ∩ R)
  isEquivalence eqₗ eqᵣ = record
    { refl  = reflexive  L R Eqₗ.refl  Eqᵣ.refl
    ; sym   = symmetric  L R Eqₗ.sym   Eqᵣ.sym
    ; trans = transitive L R Eqₗ.trans Eqᵣ.trans
    }
    where module Eqₗ = IsEquivalence eqₗ; module Eqᵣ = IsEquivalence eqᵣ

  isDecEquivalence : IsDecEquivalence L → IsDecEquivalence R → IsDecEquivalence (L ∩ R)
  isDecEquivalence eqₗ eqᵣ = record
    { isEquivalence = isEquivalence Eqₗ.isEquivalence Eqᵣ.isEquivalence
    ; _≟_           = decidable Eqₗ._≟_ Eqᵣ._≟_
    }
    where module Eqₗ = IsDecEquivalence eqₗ; module Eqᵣ = IsDecEquivalence eqᵣ

module _ {a ℓ₁ ℓ₂ ℓ₃} {A : Set a} {≈ : Rel A ℓ₁} {L : Rel A ℓ₂} {R : Rel A ℓ₃} where

  isPreorder : IsPreorder ≈ L → IsPreorder ≈ R → IsPreorder ≈ (L ∩ R)
  isPreorder Oₗ Oᵣ = record
    { isEquivalence = Oₗ.isEquivalence
    ; reflexive     = implies ≈ Oₗ.reflexive Oᵣ.reflexive
    ; trans         = transitive L R Oₗ.trans Oᵣ.trans
    }
    where module Oₗ = IsPreorder Oₗ; module Oᵣ = IsPreorder Oᵣ

  isPartialOrderˡ : IsPartialOrder ≈ L → IsPreorder ≈ R → IsPartialOrder ≈ (L ∩ R)
  isPartialOrderˡ Oₗ Oᵣ = record
    { isPreorder = isPreorder Oₗ.isPreorder Oᵣ
    ; antisym    = antisymmetric ≈ L R (inj₁ Oₗ.antisym)
    }
    where module Oₗ = IsPartialOrder Oₗ; module Oᵣ = IsPreorder Oᵣ

  isPartialOrderʳ : IsPreorder ≈ L → IsPartialOrder ≈ R → IsPartialOrder ≈ (L ∩ R)
  isPartialOrderʳ Oₗ Oᵣ = record
    { isPreorder = isPreorder Oₗ Oᵣ.isPreorder
    ; antisym    = antisymmetric ≈ L R (inj₂ Oᵣ.antisym)
    }
    where module Oₗ = IsPreorder Oₗ; module Oᵣ = IsPartialOrder Oᵣ

  isStrictPartialOrderˡ : IsStrictPartialOrder ≈ L →
                          Transitive R → R Respects₂ ≈ →
                          IsStrictPartialOrder ≈ (L ∩ R)
  isStrictPartialOrderˡ Oₗ transᵣ respᵣ = record
    { isEquivalence = Oₗ.isEquivalence
    ; irrefl        = irreflexive ≈ L R (inj₁ Oₗ.irrefl)
    ; trans         = transitive L R Oₗ.trans transᵣ
    ; <-resp-≈      = respects₂ ≈ L R Oₗ.<-resp-≈ respᵣ
    }
    where module Oₗ = IsStrictPartialOrder Oₗ

  isStrictPartialOrderʳ : Transitive L → L Respects₂ ≈ →
                          IsStrictPartialOrder ≈ R →
                          IsStrictPartialOrder ≈ (L ∩ R)
  isStrictPartialOrderʳ transₗ respₗ Oᵣ = record
    { isEquivalence = Oᵣ.isEquivalence
    ; irrefl        = irreflexive ≈ L R (inj₂ Oᵣ.irrefl)
    ; trans         = transitive L R transₗ Oᵣ.trans
    ; <-resp-≈      = respects₂ ≈ L R respₗ Oᵣ.<-resp-≈
    }
    where module Oᵣ = IsStrictPartialOrder Oᵣ
