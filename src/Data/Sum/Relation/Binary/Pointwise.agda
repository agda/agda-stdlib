------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise sum
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Sum.Relation.Binary.Pointwise where

open import Data.Product.Base using (_,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties
open import Level using (Level; _⊔_)
open import Function.Base using (const; _∘_; id)
open import Function.Bundles using (Inverse; mk↔)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as ≡

private
  variable
    a b c d ℓ₁ ℓ₂ ℓ₃ ℓ : Level
    A B C D : Set ℓ
    R S T U : REL A B ℓ
    ≈₁ ≈₂ : Rel A ℓ

------------------------------------------------------------------------
-- Definition

data Pointwise {A : Set a} {B : Set b} {C : Set c} {D : Set d}
               (R : REL A C ℓ₁) (S : REL B D ℓ₂)
               : REL (A ⊎ B) (C ⊎ D) (a ⊔ b ⊔ c ⊔ d ⊔ ℓ₁ ⊔ ℓ₂) where
  inj₁ : ∀ {a c} → R a c → Pointwise R S (inj₁ a) (inj₁ c)
  inj₂ : ∀ {b d} → S b d → Pointwise R S (inj₂ b) (inj₂ d)

----------------------------------------------------------------------
-- Functions

map : ∀ {f : A → C} {g : B → D} →
      R =[ f ]⇒ T → S =[ g ]⇒ U →
      Pointwise R S =[ Sum.map f g ]⇒ Pointwise T U
map R⇒T _ (inj₁ x) = inj₁ (R⇒T x)
map _ S⇒U (inj₂ x) = inj₂ (S⇒U x)

------------------------------------------------------------------------
-- Relational properties

drop-inj₁ : ∀ {x y} → Pointwise R S (inj₁ x) (inj₁ y) → R x y
drop-inj₁ (inj₁ x) = x

drop-inj₂ : ∀ {x y} → Pointwise R S (inj₂ x) (inj₂ y) → S x y
drop-inj₂ (inj₂ x) = x

⊎-refl : Reflexive R → Reflexive S → Reflexive (Pointwise R S)
⊎-refl refl₁ refl₂ {inj₁ x} = inj₁ refl₁
⊎-refl refl₁ refl₂ {inj₂ y} = inj₂ refl₂

⊎-symmetric : Symmetric R → Symmetric S →
              Symmetric (Pointwise R S)
⊎-symmetric sym₁ sym₂ (inj₁ x) = inj₁ (sym₁ x)
⊎-symmetric sym₁ sym₂ (inj₂ x) = inj₂ (sym₂ x)

⊎-transitive : Transitive R → Transitive S →
               Transitive (Pointwise R S)
⊎-transitive trans₁ trans₂ (inj₁ x) (inj₁ y) = inj₁ (trans₁ x y)
⊎-transitive trans₁ trans₂ (inj₂ x) (inj₂ y) = inj₂ (trans₂ x y)

⊎-asymmetric : Asymmetric R → Asymmetric S →
               Asymmetric (Pointwise R S)
⊎-asymmetric asym₁ asym₂ (inj₁ x) = λ { (inj₁ y) → asym₁ x y }
⊎-asymmetric asym₁ asym₂ (inj₂ x) = λ { (inj₂ y) → asym₂ x y }

⊎-substitutive : Substitutive R ℓ₃ → Substitutive S ℓ₃ →
                 Substitutive (Pointwise R S) ℓ₃
⊎-substitutive subst₁ subst₂ P (inj₁ x) = subst₁ (P ∘ inj₁) x
⊎-substitutive subst₁ subst₂ P (inj₂ x) = subst₂ (P ∘ inj₂) x

⊎-decidable : Decidable R → Decidable S → Decidable (Pointwise R S)
⊎-decidable _≟₁_ _≟₂_ (inj₁ x) (inj₁ y) = Dec.map′ inj₁ drop-inj₁ (x ≟₁ y)
⊎-decidable _≟₁_ _≟₂_ (inj₁ x) (inj₂ y) = no λ()
⊎-decidable _≟₁_ _≟₂_ (inj₂ x) (inj₁ y) = no λ()
⊎-decidable _≟₁_ _≟₂_ (inj₂ x) (inj₂ y) = Dec.map′ inj₂ drop-inj₂ (x ≟₂ y)

⊎-reflexive : ≈₁ ⇒ R → ≈₂ ⇒ S →
              (Pointwise ≈₁ ≈₂) ⇒ (Pointwise R S)
⊎-reflexive refl₁ refl₂ (inj₁ x) = inj₁ (refl₁ x)
⊎-reflexive refl₁ refl₂ (inj₂ x) = inj₂ (refl₂ x)

⊎-irreflexive : Irreflexive ≈₁ R → Irreflexive ≈₂ S →
                Irreflexive (Pointwise ≈₁ ≈₂) (Pointwise R S)
⊎-irreflexive irrefl₁ irrefl₂ (inj₁ x) (inj₁ y) = irrefl₁ x y
⊎-irreflexive irrefl₁ irrefl₂ (inj₂ x) (inj₂ y) = irrefl₂ x y

⊎-antisymmetric : Antisymmetric ≈₁ R → Antisymmetric ≈₂ S →
                  Antisymmetric (Pointwise ≈₁ ≈₂) (Pointwise R S)
⊎-antisymmetric antisym₁ antisym₂ (inj₁ x) (inj₁ y) = inj₁ (antisym₁ x y)
⊎-antisymmetric antisym₁ antisym₂ (inj₂ x) (inj₂ y) = inj₂ (antisym₂ x y)

⊎-respectsˡ : R Respectsˡ ≈₁ → S Respectsˡ ≈₂ →
              (Pointwise R S) Respectsˡ (Pointwise ≈₁ ≈₂)
⊎-respectsˡ resp₁ resp₂ (inj₁ x) (inj₁ y) = inj₁ (resp₁ x y)
⊎-respectsˡ resp₁ resp₂ (inj₂ x) (inj₂ y) = inj₂ (resp₂ x y)

⊎-respectsʳ : R Respectsʳ ≈₁ → S Respectsʳ ≈₂ →
              (Pointwise R S) Respectsʳ (Pointwise ≈₁ ≈₂)
⊎-respectsʳ resp₁ resp₂ (inj₁ x) (inj₁ y) = inj₁ (resp₁ x y)
⊎-respectsʳ resp₁ resp₂ (inj₂ x) (inj₂ y) = inj₂ (resp₂ x y)

⊎-respects₂ : R Respects₂ ≈₁ → S Respects₂ ≈₂ →
              (Pointwise R S) Respects₂ (Pointwise ≈₁ ≈₂)
⊎-respects₂ (r₁ , l₁) (r₂ , l₂) = ⊎-respectsʳ r₁ r₂ , ⊎-respectsˡ l₁ l₂

------------------------------------------------------------------------
-- Structures

⊎-isEquivalence : IsEquivalence ≈₁ → IsEquivalence ≈₂ →
                  IsEquivalence (Pointwise ≈₁ ≈₂)
⊎-isEquivalence eq₁ eq₂ = record
  { refl  = ⊎-refl       (refl  eq₁) (refl  eq₂)
  ; sym   = ⊎-symmetric  (sym   eq₁) (sym   eq₂)
  ; trans = ⊎-transitive (trans eq₁) (trans eq₂)
  } where open IsEquivalence

⊎-isDecEquivalence : IsDecEquivalence ≈₁ → IsDecEquivalence ≈₂ →
                     IsDecEquivalence (Pointwise ≈₁ ≈₂)
⊎-isDecEquivalence eq₁ eq₂ = record
  { isEquivalence =
      ⊎-isEquivalence (isEquivalence eq₁) (isEquivalence eq₂)
  ; _≟_           = ⊎-decidable (_≟_ eq₁) (_≟_ eq₂)
  } where open IsDecEquivalence

⊎-isPreorder : IsPreorder ≈₁ R → IsPreorder ≈₂ S →
               IsPreorder (Pointwise ≈₁ ≈₂) (Pointwise R S)
⊎-isPreorder pre₁ pre₂ = record
  { isEquivalence =
      ⊎-isEquivalence (isEquivalence pre₁) (isEquivalence pre₂)
  ; reflexive     = ⊎-reflexive (reflexive pre₁) (reflexive pre₂)
  ; trans         = ⊎-transitive (trans pre₁) (trans pre₂)
  } where open IsPreorder

⊎-isPartialOrder : IsPartialOrder ≈₁ R → IsPartialOrder ≈₂ S →
                   IsPartialOrder
                     (Pointwise ≈₁ ≈₂) (Pointwise R S)
⊎-isPartialOrder po₁ po₂ = record
  { isPreorder = ⊎-isPreorder (isPreorder po₁) (isPreorder po₂)
  ; antisym    = ⊎-antisymmetric (antisym po₁) (antisym    po₂)
  } where open IsPartialOrder

⊎-isStrictPartialOrder : IsStrictPartialOrder ≈₁ R →
                         IsStrictPartialOrder ≈₂ S →
                         IsStrictPartialOrder
                           (Pointwise ≈₁ ≈₂) (Pointwise R S)
⊎-isStrictPartialOrder spo₁ spo₂ = record
  { isEquivalence =
      ⊎-isEquivalence (isEquivalence spo₁) (isEquivalence spo₂)
  ; irrefl        = ⊎-irreflexive (irrefl   spo₁) (irrefl   spo₂)
  ; trans         = ⊎-transitive  (trans    spo₁) (trans    spo₂)
  ; <-resp-≈      = ⊎-respects₂   (<-resp-≈ spo₁) (<-resp-≈ spo₂)
  } where open IsStrictPartialOrder

------------------------------------------------------------------------
-- Bundles

⊎-setoid : Setoid a b → Setoid c d → Setoid _ _
⊎-setoid s₁ s₂ = record
  { isEquivalence =
      ⊎-isEquivalence (isEquivalence s₁) (isEquivalence s₂)
  } where open Setoid

⊎-decSetoid : DecSetoid a b → DecSetoid c d → DecSetoid _ _
⊎-decSetoid ds₁ ds₂ = record
  { isDecEquivalence =
      ⊎-isDecEquivalence (isDecEquivalence ds₁) (isDecEquivalence ds₂)
  } where open DecSetoid

⊎-preorder : Preorder a b ℓ₁ → Preorder c d ℓ₂ → Preorder _ _ _
⊎-preorder p₁ p₂ = record
  { isPreorder   =
      ⊎-isPreorder (isPreorder p₁) (isPreorder p₂)
  } where open Preorder

⊎-poset : Poset a b c → Poset a b c → Poset _ _ _
⊎-poset po₁ po₂ = record
  { isPartialOrder =
      ⊎-isPartialOrder (isPartialOrder po₁) (isPartialOrder po₂)
  } where open Poset

------------------------------------------------------------------------
-- Additional notation

-- Infix combining setoids
infix 4 _⊎ₛ_
_⊎ₛ_ : Setoid a b → Setoid c d → Setoid _ _
_⊎ₛ_ = ⊎-setoid

------------------------------------------------------------------------
-- The propositional equality setoid over products can be
-- decomposed using Pointwise

Pointwise-≡⇒≡ : (Pointwise _≡_ _≡_) ⇒ _≡_ {A = A ⊎ B}
Pointwise-≡⇒≡ (inj₁ x) = ≡.cong inj₁ x
Pointwise-≡⇒≡ (inj₂ x) = ≡.cong inj₂ x

≡⇒Pointwise-≡ : _≡_ {A = A ⊎ B} ⇒ (Pointwise _≡_ _≡_)
≡⇒Pointwise-≡ ≡.refl = ⊎-refl ≡.refl ≡.refl

Pointwise-≡↔≡ : (A : Set a) (B : Set b) →
                 Inverse (≡.setoid A ⊎ₛ ≡.setoid B) (≡.setoid (A ⊎ B))
Pointwise-≡↔≡ _ _ = record
  { to        = id
  ; from      = id
  ; to-cong   = Pointwise-≡⇒≡
  ; from-cong = ≡⇒Pointwise-≡
  ; inverse   = Pointwise-≡⇒≡ , ≡⇒Pointwise-≡
  }
