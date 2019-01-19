------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise sum
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Relation.Binary.Pointwise where

open import Data.Product using (_,_)
open import Data.Sum as Sum
open import Data.Sum.Properties
open import Level using (_⊔_)
open import Function
open import Function.Equality as F
  using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalence; _⇔_; module Equivalence)
open import Function.Injection as Inj
  using (Injection; _↣_; module Injection)
open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; module LeftInverse)
open import Function.Related
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)
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
-- Packages

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
-- Setoid "relatedness"

module _ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} where

  inj₁ₛ : A ⟶ (A ⊎ₛ B)
  inj₁ₛ = record { _⟨$⟩_ = inj₁ ; cong = inj₁ }

  inj₂ₛ : B ⟶ (A ⊎ₛ B)
  inj₂ₛ = record { _⟨$⟩_ = inj₂ ; cong = inj₂ }

  [_,_]ₛ : ∀ {c₁ c₂} {C : Setoid c₁ c₂} →
           (A ⟶ C) → (B ⟶ C) → (A ⊎ₛ B) ⟶ C
  [ f , g ]ₛ = record
    { _⟨$⟩_ = [ f ⟨$⟩_ , g ⟨$⟩_ ]
    ; cong = λ where
      (inj₁ x∼₁y) → F.cong f x∼₁y
      (inj₂ x∼₂y) → F.cong g x∼₂y
    }

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
         {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
         {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
         where

  _⊎-⟶_ : (A ⟶ B) → (C ⟶ D) → (A ⊎ₛ C) ⟶ (B ⊎ₛ D)
  _⊎-⟶_ f g = record
    { _⟨$⟩_ = fg
    ; cong  = fg-cong
    }
    where
    open Setoid (A ⊎ₛ C) using () renaming (_≈_ to _≈AC_)
    open Setoid (B ⊎ₛ D) using () renaming (_≈_ to _≈BD_)

    fg = Sum.map (_⟨$⟩_ f) (_⟨$⟩_ g)

    fg-cong : _≈AC_ =[ fg ]⇒ _≈BD_
    fg-cong (inj₁ x∼₁y) = inj₁ (F.cong f x∼₁y)
    fg-cong (inj₂ x∼₂y) = inj₂ (F.cong g x∼₂y)

swapₛ : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} →
        (A ⊎ₛ B) ⟶ (B ⊎ₛ A)
swapₛ = [ inj₂ₛ , inj₁ₛ ]ₛ

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
         {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
         {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
         where

  _⊎-equivalence_ : Equivalence A B → Equivalence C D →
                    Equivalence (A ⊎ₛ C) (B ⊎ₛ D)
  A⇔B ⊎-equivalence C⇔D = record
    { to   = to   A⇔B ⊎-⟶ to   C⇔D
    ; from = from A⇔B ⊎-⟶ from C⇔D
    } where open Equivalence

  _⊎-injection_ : Injection A B → Injection C D →
                  Injection (A ⊎ₛ C) (B ⊎ₛ D)
  _⊎-injection_ A↣B C↣D = record
    { to        = to A↣B ⊎-⟶ to C↣D
    ; injective = inj _ _
    }
    where
    open Injection
    open Setoid (A ⊎ₛ C) using () renaming (_≈_ to _≈AC_)
    open Setoid (B ⊎ₛ D) using () renaming (_≈_ to _≈BD_)

    inj : ∀ x y →
          (to A↣B ⊎-⟶ to C↣D) ⟨$⟩ x ≈BD (to A↣B ⊎-⟶ to C↣D) ⟨$⟩ y →
          x ≈AC y
    inj (inj₁ x) (inj₁ y) (inj₁ x∼₁y) = inj₁ (injective A↣B x∼₁y)
    inj (inj₂ x) (inj₂ y) (inj₂ x∼₂y) = inj₂ (injective C↣D x∼₂y)
    -- Can be removed in Agda 2.6.0?
    inj (inj₁ x) (inj₂ y) ()
    inj (inj₂ x) (inj₁ y) ()

  _⊎-left-inverse_ : LeftInverse A B → LeftInverse C D →
                     LeftInverse (A ⊎ₛ C) (B ⊎ₛ D)
  A↞B ⊎-left-inverse C↞D = record
    { to              = Equivalence.to   eq
    ; from            = Equivalence.from eq
    ; left-inverse-of = [ (λ x → inj₁ (left-inverse-of A↞B x))
                        , (λ x → inj₂ (left-inverse-of C↞D x)) ]
    }
    where
    open LeftInverse
    eq = LeftInverse.equivalence A↞B ⊎-equivalence
         LeftInverse.equivalence C↞D

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
         {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
         {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
         where

  _⊎-surjection_ : Surjection A B → Surjection C D →
                   Surjection (A ⊎ₛ C) (B ⊎ₛ D)
  A↠B ⊎-surjection C↠D = record
    { to         = LeftInverse.from inv
    ; surjective = record
      { from             = LeftInverse.to inv
      ; right-inverse-of = LeftInverse.left-inverse-of inv
      }
    }
    where
    open Surjection
    inv = right-inverse A↠B ⊎-left-inverse right-inverse C↠D

  _⊎-inverse_ : Inverse A B → Inverse C D →
                Inverse (A ⊎ₛ C) (B ⊎ₛ D)
  A↔B ⊎-inverse C↔D = record
    { to         = Surjection.to   surj
    ; from       = Surjection.from surj
    ; inverse-of = record
      { left-inverse-of  = LeftInverse.left-inverse-of inv
      ; right-inverse-of = Surjection.right-inverse-of surj
      }
    }
    where
    open Inverse
    surj = Inverse.surjection   A↔B ⊎-surjection
           Inverse.surjection   C↔D
    inv  = Inverse.left-inverse A↔B ⊎-left-inverse
           Inverse.left-inverse C↔D

------------------------------------------------------------------------
-- Propositional "relatedness"

module _ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} where

  _⊎-⇔_ : A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
  _⊎-⇔_ A⇔B C⇔D =
    Inverse.equivalence (Pointwise-≡↔≡ B D) ⟨∘⟩
    (A⇔B ⊎-equivalence C⇔D) ⟨∘⟩
    Eq.sym (Inverse.equivalence (Pointwise-≡↔≡ A C))
    where open Eq using () renaming (_∘_ to _⟨∘⟩_)

  _⊎-↣_ : A ↣ B → C ↣ D → (A ⊎ C) ↣ (B ⊎ D)
  _⊎-↣_ A↣B C↣D =
    Inverse.injection (Pointwise-≡↔≡ B D) ⟨∘⟩
    (A↣B ⊎-injection C↣D) ⟨∘⟩
    Inverse.injection (Inv.sym (Pointwise-≡↔≡ A C))
    where open Inj using () renaming (_∘_ to _⟨∘⟩_)

  _⊎-↞_ : A ↞ B → C ↞ D → (A ⊎ C) ↞ (B ⊎ D)
  _⊎-↞_ A↞B C↞D =
    Inverse.left-inverse (Pointwise-≡↔≡ B D) ⟨∘⟩
    (A↞B ⊎-left-inverse C↞D) ⟨∘⟩
    Inverse.left-inverse (Inv.sym (Pointwise-≡↔≡ A C))
    where open LeftInv using () renaming (_∘_ to _⟨∘⟩_)

  _⊎-↠_ : A ↠ B → C ↠ D → (A ⊎ C) ↠ (B ⊎ D)
  _⊎-↠_ A↠B C↠D =
    Inverse.surjection (Pointwise-≡↔≡ B D) ⟨∘⟩
    (A↠B ⊎-surjection C↠D) ⟨∘⟩
    Inverse.surjection (Inv.sym (Pointwise-≡↔≡ A C))
    where open Surj using () renaming (_∘_ to _⟨∘⟩_)

  _⊎-↔_ : A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
  _⊎-↔_ A↔B C↔D =
    Pointwise-≡↔≡ B D ⟨∘⟩
    (A↔B ⊎-inverse C↔D) ⟨∘⟩
    Inv.sym (Pointwise-≡↔≡ A C)
    where open Inv using () renaming (_∘_ to _⟨∘⟩_)

_⊎-cong_ : ∀ {k a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
           A ∼[ k ] B → C ∼[ k ] D → (A ⊎ C) ∼[ k ] (B ⊎ D)
_⊎-cong_ {implication}         = Sum.map
_⊎-cong_ {reverse-implication} = λ f g → lam (Sum.map (app-← f) (app-← g))
_⊎-cong_ {equivalence}         = _⊎-⇔_
_⊎-cong_ {injection}           = _⊎-↣_
_⊎-cong_ {reverse-injection}   = λ f g → lam (app-↢ f ⊎-↣ app-↢ g)
_⊎-cong_ {left-inverse}        = _⊎-↞_
_⊎-cong_ {surjection}          = _⊎-↠_
_⊎-cong_ {bijection}           = _⊎-↔_


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.18

₁∼₁ = inj₁
{-# WARNING_ON_USAGE ₁∼₁
"Warning: ₁∼₁ was deprecated in v0.14.
Please use inj₁ in `Data.Sum.Properties` instead."
#-}
₂∼₂ = inj₂
{-# WARNING_ON_USAGE ₂∼₂
"Warning: ₂∼₂ was deprecated in v0.14.
Please use inj₂ in `Data.Sum.Properties` instead."
#-}
_⊎-≟_ : ∀ {a b} {A : Set a} {B : Set b} →
        Decidable {A = A} _≡_ → Decidable {A = B} _≡_ →
        Decidable {A = A ⊎ B} _≡_
(dec₁ ⊎-≟ dec₂) s₁ s₂ = Dec.map′ Pointwise-≡⇒≡ ≡⇒Pointwise-≡ (s₁ ≟ s₂)
  where
  open DecSetoid (⊎-decSetoid (P.decSetoid dec₁) (P.decSetoid dec₂))
{-# WARNING_ON_USAGE _⊎-≟_
"Warning: _⊎-≟_ was deprecated in v0.14.
Please use ≡-dec in `Data.Sum.Properties` instead."
#-}
