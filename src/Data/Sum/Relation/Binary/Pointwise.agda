------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise sum
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Relation.Binary.Pointwise where

open import Data.Product using (_,_)
open import Data.Sum.Base as Sum
open import Data.Sum.Properties
open import Level using (_⊔_)
open import Function.Base using (_∘_; id)
open import Function.Inverse using (Inverse)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

----------------------------------------------------------------------
-- Definition

data Pointwise {a b c d r s}
               {A : Set a} {B : Set b} {C : Set c} {D : Set d}
               (R : REL A C r) (S : REL B D s)
               : REL (A ⊎ B) (C ⊎ D) (a ⊔ b ⊔ c ⊔ d ⊔ r ⊔ s) where
  inj₁ : ∀ {a c} → R a c → Pointwise R S (inj₁ a) (inj₁ c)
  inj₂ : ∀ {b d} → S b d → Pointwise R S (inj₂ b) (inj₂ d)

----------------------------------------------------------------------
-- Relational properties

module _ {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂}
         where

  drop-inj₁ : ∀ {x y} → Pointwise ∼₁ ∼₂ (inj₁ x) (inj₁ y) → ∼₁ x y
  drop-inj₁ (inj₁ x) = x

  drop-inj₂ : ∀ {x y} → Pointwise ∼₁ ∼₂ (inj₂ x) (inj₂ y) → ∼₂ x y
  drop-inj₂ (inj₂ x) = x

  ⊎-refl : Reflexive ∼₁ → Reflexive ∼₂ →
           Reflexive (Pointwise ∼₁ ∼₂)
  ⊎-refl refl₁ refl₂ {inj₁ x} = inj₁ refl₁
  ⊎-refl refl₁ refl₂ {inj₂ y} = inj₂ refl₂

  ⊎-symmetric : Symmetric ∼₁ → Symmetric ∼₂ →
                Symmetric (Pointwise ∼₁ ∼₂)
  ⊎-symmetric sym₁ sym₂ (inj₁ x) = inj₁ (sym₁ x)
  ⊎-symmetric sym₁ sym₂ (inj₂ x) = inj₂ (sym₂ x)

  ⊎-transitive : Transitive ∼₁ → Transitive ∼₂ →
                 Transitive (Pointwise ∼₁ ∼₂)
  ⊎-transitive trans₁ trans₂ (inj₁ x) (inj₁ y) = inj₁ (trans₁ x y)
  ⊎-transitive trans₁ trans₂ (inj₂ x) (inj₂ y) = inj₂ (trans₂ x y)

  ⊎-asymmetric : Asymmetric ∼₁ → Asymmetric ∼₂ →
                 Asymmetric (Pointwise ∼₁ ∼₂)
  ⊎-asymmetric asym₁ asym₂ (inj₁ x) = λ { (inj₁ y) → asym₁ x y }
  ⊎-asymmetric asym₁ asym₂ (inj₂ x) = λ { (inj₂ y) → asym₂ x y }

  ⊎-substitutive : ∀ {ℓ₃} → Substitutive ∼₁ ℓ₃ → Substitutive ∼₂ ℓ₃ →
                   Substitutive (Pointwise ∼₁ ∼₂) ℓ₃
  ⊎-substitutive subst₁ subst₂ P (inj₁ x) = subst₁ (P ∘ inj₁) x
  ⊎-substitutive subst₁ subst₂ P (inj₂ x) = subst₂ (P ∘ inj₂) x

  ⊎-decidable : Decidable ∼₁ → Decidable ∼₂ →
                Decidable (Pointwise ∼₁ ∼₂)
  ⊎-decidable _≟₁_ _≟₂_ (inj₁ x) (inj₁ y) = Dec.map′ inj₁ drop-inj₁ (x ≟₁ y)
  ⊎-decidable _≟₁_ _≟₂_ (inj₁ x) (inj₂ y) = no λ()
  ⊎-decidable _≟₁_ _≟₂_ (inj₂ x) (inj₁ y) = no λ()
  ⊎-decidable _≟₁_ _≟₂_ (inj₂ x) (inj₂ y) = Dec.map′ inj₂ drop-inj₂ (x ≟₂ y)

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {≈₁ : Rel A₁ ℓ₂}
         {ℓ₃ ℓ₄} {∼₂ : Rel A₂ ℓ₃} {≈₂ : Rel A₂ ℓ₄} where

  ⊎-reflexive : ≈₁ ⇒ ∼₁ → ≈₂ ⇒ ∼₂ →
                (Pointwise ≈₁ ≈₂) ⇒ (Pointwise ∼₁ ∼₂)
  ⊎-reflexive refl₁ refl₂ (inj₁ x) = inj₁ (refl₁ x)
  ⊎-reflexive refl₁ refl₂ (inj₂ x) = inj₂ (refl₂ x)

  ⊎-irreflexive : Irreflexive ≈₁ ∼₁ → Irreflexive ≈₂ ∼₂ →
                  Irreflexive (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
  ⊎-irreflexive irrefl₁ irrefl₂ (inj₁ x) (inj₁ y) = irrefl₁ x y
  ⊎-irreflexive irrefl₁ irrefl₂ (inj₂ x) (inj₂ y) = irrefl₂ x y

  ⊎-antisymmetric : Antisymmetric ≈₁ ∼₁ → Antisymmetric ≈₂ ∼₂ →
                    Antisymmetric (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
  ⊎-antisymmetric antisym₁ antisym₂ (inj₁ x) (inj₁ y) = inj₁ (antisym₁ x y)
  ⊎-antisymmetric antisym₁ antisym₂ (inj₂ x) (inj₂ y) = inj₂ (antisym₂ x y)

  ⊎-respectsˡ : ∼₁ Respectsˡ ≈₁ → ∼₂ Respectsˡ ≈₂ →
                (Pointwise ∼₁ ∼₂) Respectsˡ (Pointwise ≈₁ ≈₂)
  ⊎-respectsˡ resp₁ resp₂ (inj₁ x) (inj₁ y) = inj₁ (resp₁ x y)
  ⊎-respectsˡ resp₁ resp₂ (inj₂ x) (inj₂ y) = inj₂ (resp₂ x y)

  ⊎-respectsʳ : ∼₁ Respectsʳ ≈₁ → ∼₂ Respectsʳ ≈₂ →
                (Pointwise ∼₁ ∼₂) Respectsʳ (Pointwise ≈₁ ≈₂)
  ⊎-respectsʳ resp₁ resp₂ (inj₁ x) (inj₁ y) = inj₁ (resp₁ x y)
  ⊎-respectsʳ resp₁ resp₂ (inj₂ x) (inj₂ y) = inj₂ (resp₂ x y)

  ⊎-respects₂ : ∼₁ Respects₂ ≈₁ → ∼₂ Respects₂ ≈₂ →
                (Pointwise ∼₁ ∼₂) Respects₂ (Pointwise ≈₁ ≈₂)
  ⊎-respects₂ (r₁ , l₁) (r₂ , l₂) = ⊎-respectsʳ r₁ r₂ , ⊎-respectsˡ l₁ l₂

----------------------------------------------------------------------
-- Structures

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {ℓ₁ ℓ₂} {≈₁ : Rel A₁ ℓ₁} {≈₂ : Rel A₂ ℓ₂}
         where

  ⊎-isEquivalence : IsEquivalence ≈₁ → IsEquivalence ≈₂ →
                    IsEquivalence (Pointwise ≈₁ ≈₂)
  ⊎-isEquivalence eq₁ eq₂ = record
    { refl  = ⊎-refl       (refl  eq₁) (refl  eq₂)
    ; sym   = ⊎-symmetric  (sym   eq₁) (sym   eq₂)
    ; trans = ⊎-transitive (trans eq₁) (trans eq₂)
    }
    where open IsEquivalence

  ⊎-isDecEquivalence : IsDecEquivalence ≈₁ → IsDecEquivalence ≈₂ →
                       IsDecEquivalence (Pointwise ≈₁ ≈₂)
  ⊎-isDecEquivalence eq₁ eq₂ = record
    { isEquivalence =
        ⊎-isEquivalence (isEquivalence eq₁) (isEquivalence eq₂)
    ; _≟_           = ⊎-decidable (_≟_ eq₁) (_≟_ eq₂)
    }
    where open IsDecEquivalence

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {ℓ₁ ℓ₂} {≈₁ : Rel A₁ ℓ₁} {∼₁ : Rel A₁ ℓ₂}
         {ℓ₃ ℓ₄} {≈₂ : Rel A₂ ℓ₃} {∼₂ : Rel A₂ ℓ₄} where

  ⊎-isPreorder : IsPreorder ≈₁ ∼₁ → IsPreorder ≈₂ ∼₂ →
                 IsPreorder (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
  ⊎-isPreorder pre₁ pre₂ = record
    { isEquivalence =
        ⊎-isEquivalence (isEquivalence pre₁) (isEquivalence pre₂)
    ; reflexive     = ⊎-reflexive (reflexive pre₁) (reflexive pre₂)
    ; trans         = ⊎-transitive (trans pre₁) (trans pre₂)
    }
    where open IsPreorder

  ⊎-isPartialOrder : IsPartialOrder ≈₁ ∼₁ →
                     IsPartialOrder ≈₂ ∼₂ →
                     IsPartialOrder
                       (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
  ⊎-isPartialOrder po₁ po₂ = record
    { isPreorder = ⊎-isPreorder (isPreorder po₁) (isPreorder po₂)
    ; antisym    = ⊎-antisymmetric (antisym po₁) (antisym    po₂)
    }
    where open IsPartialOrder

  ⊎-isStrictPartialOrder : IsStrictPartialOrder ≈₁ ∼₁ →
                           IsStrictPartialOrder ≈₂ ∼₂ →
                           IsStrictPartialOrder
                             (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
  ⊎-isStrictPartialOrder spo₁ spo₂ = record
    { isEquivalence =
        ⊎-isEquivalence (isEquivalence spo₁) (isEquivalence spo₂)
    ; irrefl        = ⊎-irreflexive (irrefl   spo₁) (irrefl   spo₂)
    ; trans         = ⊎-transitive  (trans    spo₁) (trans    spo₂)
    ; <-resp-≈      = ⊎-respects₂   (<-resp-≈ spo₁) (<-resp-≈ spo₂)
    }
    where open IsStrictPartialOrder

------------------------------------------------------------------------
-- Bundles

module _ {a b c d} where

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

  -- Some additional notation for combining setoids
  infix 4 _⊎ₛ_
  _⊎ₛ_ : Setoid a b → Setoid c d → Setoid _ _
  _⊎ₛ_ = ⊎-setoid

module _ {a b c d e f} where

  ⊎-preorder : Preorder a b c → Preorder d e f → Preorder _ _ _
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
-- The propositional equality setoid over products can be
-- decomposed using Pointwise

module _ {a b} {A : Set a} {B : Set b} where

  Pointwise-≡⇒≡ : (Pointwise _≡_ _≡_) ⇒ _≡_ {A = A ⊎ B}
  Pointwise-≡⇒≡ (inj₁ x) = P.cong inj₁ x
  Pointwise-≡⇒≡ (inj₂ x) = P.cong inj₂ x

  ≡⇒Pointwise-≡ : _≡_ {A = A ⊎ B} ⇒ (Pointwise _≡_ _≡_)
  ≡⇒Pointwise-≡ P.refl = ⊎-refl P.refl P.refl

Pointwise-≡↔≡ : ∀ {a b} (A : Set a) (B : Set b) →
                Inverse (P.setoid A ⊎ₛ P.setoid B)
                        (P.setoid (A ⊎ B))
Pointwise-≡↔≡ _ _ = record
  { to         = record { _⟨$⟩_ = id; cong = Pointwise-≡⇒≡ }
  ; from       = record { _⟨$⟩_ = id; cong = ≡⇒Pointwise-≡ }
  ; inverse-of = record
    { left-inverse-of  = λ _ → ⊎-refl P.refl P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

module _ {a b c d r s}
         {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {R : REL A C r} {S : REL B D s}
         where

  ₁∼₁ : ∀ {a c} → R a c → Pointwise R S (inj₁ a) (inj₁ c)
  ₁∼₁ = inj₁
  {-# WARNING_ON_USAGE ₁∼₁
  "Warning: ₁∼₁ was deprecated in v1.0.
  Please use inj₁ in `Data.Sum.Properties` instead."
  #-}

  ₂∼₂ : ∀ {b d} → S b d → Pointwise R S (inj₂ b) (inj₂ d)
  ₂∼₂ = inj₂
  {-# WARNING_ON_USAGE ₂∼₂
  "Warning: ₂∼₂ was deprecated in v1.0.
  Please use inj₂ in `Data.Sum.Properties` instead."
  #-}

_⊎-≟_ : ∀ {a b} {A : Set a} {B : Set b} →
        Decidable {A = A} _≡_ → Decidable {A = B} _≡_ →
        Decidable {A = A ⊎ B} _≡_
(dec₁ ⊎-≟ dec₂) s₁ s₂ = Dec.map′ Pointwise-≡⇒≡ ≡⇒Pointwise-≡ (s₁ ≟ s₂)
  where
  open DecSetoid (⊎-decSetoid (P.decSetoid dec₁) (P.decSetoid dec₂))
{-# WARNING_ON_USAGE _⊎-≟_
"Warning: _⊎-≟_ was deprecated in v1.0.
Please use ≡-dec in `Data.Sum.Properties` instead."
#-}
