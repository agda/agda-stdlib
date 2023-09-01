------------------------------------------------------------------------
-- The Agda standard library
--
-- Intersection of two binary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Intersection where

open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Function.Base using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary
open import Relation.Nullary.Decidable using (yes; no; _×-dec_)

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set a
    ≈ L R : Rel A ℓ₁

------------------------------------------------------------------------
-- Definition

infixl 6 _∩_

_∩_ : REL A B ℓ₁ → REL A B ℓ₂ → REL A B (ℓ₁ ⊔ ℓ₂)
L ∩ R = λ i j → L i j × R i j

------------------------------------------------------------------------
-- Properties

module _ (L : Rel A ℓ₁) (R : Rel A ℓ₂) where

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

module _ (≈ : REL A B ℓ₁) {L : REL A B ℓ₂} {R : REL A B ℓ₃} where

  implies : (≈ ⇒ L) → (≈ ⇒ R) → ≈ ⇒ (L ∩ R)
  implies ≈⇒L ≈⇒R = < ≈⇒L , ≈⇒R >

module _ (≈ : REL A B ℓ₁) (L : REL A B ℓ₂) (R : REL A B ℓ₃) where

  irreflexive : Irreflexive ≈ L ⊎ Irreflexive ≈ R → Irreflexive ≈ (L ∩ R)
  irreflexive irrefl x≈y (Lxy , Rxy) = [ (λ x → x x≈y Lxy) , (λ x → x x≈y Rxy) ] irrefl

module _ (≈ : Rel A ℓ₁) (L : Rel A ℓ₂) (R : Rel A ℓ₃) where

  respectsˡ : L Respectsˡ ≈ → R Respectsˡ ≈ → (L ∩ R) Respectsˡ ≈
  respectsˡ L-resp R-resp x≈y = map (L-resp x≈y) (R-resp x≈y)

  respectsʳ : L Respectsʳ ≈ → R Respectsʳ ≈ → (L ∩ R) Respectsʳ ≈
  respectsʳ L-resp R-resp x≈y = map (L-resp x≈y) (R-resp x≈y)

  respects₂ : L Respects₂ ≈ → R Respects₂ ≈ → (L ∩ R) Respects₂ ≈
  respects₂ (Lʳ , Lˡ) (Rʳ , Rˡ) = respectsʳ Lʳ Rʳ , respectsˡ Lˡ Rˡ

  antisymmetric : Antisymmetric ≈ L ⊎ Antisymmetric ≈ R → Antisymmetric ≈ (L ∩ R)
  antisymmetric (inj₁ L-antisym) (Lxy , _) (Lyx , _) = L-antisym Lxy Lyx
  antisymmetric (inj₂ R-antisym) (_ , Rxy) (_ , Ryx) = R-antisym Rxy Ryx

module _ {L : REL A B ℓ₁} {R : REL A B ℓ₂} where

  decidable : Decidable L → Decidable R → Decidable (L ∩ R)
  decidable L? R? x y = L? x y ×-dec R? x y

------------------------------------------------------------------------
-- Structures

isEquivalence : IsEquivalence L → IsEquivalence R → IsEquivalence (L ∩ R)
isEquivalence {L = L} {R = R} eqₗ eqᵣ = record
  { refl  = reflexive  L R L.refl  R.refl
  ; sym   = symmetric  L R L.sym   R.sym
  ; trans = transitive L R L.trans R.trans
  } where module L = IsEquivalence eqₗ; module R = IsEquivalence eqᵣ

isDecEquivalence : IsDecEquivalence L → IsDecEquivalence R → IsDecEquivalence (L ∩ R)
isDecEquivalence eqₗ eqᵣ = record
  { isEquivalence = isEquivalence L.isEquivalence R.isEquivalence
  ; _≟_           = decidable L._≟_ R._≟_
  } where module L = IsDecEquivalence eqₗ; module R = IsDecEquivalence eqᵣ

isPreorder : IsPreorder ≈ L → IsPreorder ≈ R → IsPreorder ≈ (L ∩ R)
isPreorder {≈ = ≈} {L = L} {R = R} Oₗ Oᵣ = record
  { isEquivalence = Oₗ.isEquivalence
  ; reflexive     = implies ≈ Oₗ.reflexive Oᵣ.reflexive
  ; trans         = transitive L R Oₗ.trans Oᵣ.trans
  }
  where module Oₗ = IsPreorder Oₗ; module Oᵣ = IsPreorder Oᵣ

isPartialOrderˡ : IsPartialOrder ≈ L → IsPreorder ≈ R → IsPartialOrder ≈ (L ∩ R)
isPartialOrderˡ {≈ = ≈} {L = L} {R = R} Oₗ Oᵣ = record
  { isPreorder = isPreorder Oₗ.isPreorder Oᵣ
  ; antisym    = antisymmetric ≈ L R (inj₁ Oₗ.antisym)
  } where module Oₗ = IsPartialOrder Oₗ; module Oᵣ = IsPreorder Oᵣ

isPartialOrderʳ : IsPreorder ≈ L → IsPartialOrder ≈ R → IsPartialOrder ≈ (L ∩ R)
isPartialOrderʳ {≈ = ≈} {L = L} {R = R} Oₗ Oᵣ = record
  { isPreorder = isPreorder Oₗ Oᵣ.isPreorder
  ; antisym    = antisymmetric ≈ L R (inj₂ Oᵣ.antisym)
  } where module Oₗ = IsPreorder Oₗ; module Oᵣ = IsPartialOrder Oᵣ

isStrictPartialOrderˡ : IsStrictPartialOrder ≈ L →
                        Transitive R → R Respects₂ ≈ →
                        IsStrictPartialOrder ≈ (L ∩ R)
isStrictPartialOrderˡ {≈ = ≈} {L = L} {R = R}  Oₗ transᵣ respᵣ = record
  { isEquivalence = Oₗ.isEquivalence
  ; irrefl        = irreflexive ≈ L R (inj₁ Oₗ.irrefl)
  ; trans         = transitive L R Oₗ.trans transᵣ
  ; <-resp-≈      = respects₂ ≈ L R Oₗ.<-resp-≈ respᵣ
  } where module Oₗ = IsStrictPartialOrder Oₗ

isStrictPartialOrderʳ : Transitive L → L Respects₂ ≈ →
                        IsStrictPartialOrder ≈ R →
                        IsStrictPartialOrder ≈ (L ∩ R)
isStrictPartialOrderʳ {L = L} {≈ = ≈} {R = R} transₗ respₗ Oᵣ = record
  { isEquivalence = Oᵣ.isEquivalence
  ; irrefl        = irreflexive ≈ L R (inj₂ Oᵣ.irrefl)
  ; trans         = transitive L R transₗ Oᵣ.trans
  ; <-resp-≈      = respects₂ ≈ L R respₗ Oᵣ.<-resp-≈
  } where module Oᵣ = IsStrictPartialOrder Oᵣ
