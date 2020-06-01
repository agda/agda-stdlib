------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional equality
--
-- This file contains some core properies of propositional equality which
-- are re-exported by Relation.Binary.PropositionalEquality. They are
-- ``equality rearrangement'' lemmas.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality.Properties where

open import Function.Base using (id; _∘_)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Unary using (Pred)

private
  variable
    a p : Level
    A B C : Set a

------------------------------------------------------------------------
-- Various equality rearrangement lemmas

trans-reflʳ : ∀ {x y : A} (p : x ≡ y) → trans p refl ≡ p
trans-reflʳ refl = refl

trans-assoc : ∀ {x y z u : A} (p : x ≡ y) {q : y ≡ z} {r : z ≡ u} →
  trans (trans p q) r ≡ trans p (trans q r)
trans-assoc refl = refl

trans-symˡ : ∀ {x y : A} (p : x ≡ y) → trans (sym p) p ≡ refl
trans-symˡ refl = refl

trans-symʳ : ∀ {x y : A} (p : x ≡ y) → trans p (sym p) ≡ refl
trans-symʳ refl = refl

trans-injectiveˡ : ∀ {x y z : A} {p₁ p₂ : x ≡ y} (q : y ≡ z) →
                   trans p₁ q ≡ trans p₂ q → p₁ ≡ p₂
trans-injectiveˡ refl = subst₂ _≡_ (trans-reflʳ _) (trans-reflʳ _)

trans-injectiveʳ : ∀ {x y z : A} (p : x ≡ y) {q₁ q₂ : y ≡ z} →
                   trans p q₁ ≡ trans p q₂ → q₁ ≡ q₂
trans-injectiveʳ refl eq = eq

cong-id : ∀ {x y : A} (p : x ≡ y) → cong id p ≡ p
cong-id refl = refl

cong-∘ : ∀ {x y : A} {f : B → C} {g : A → B} (p : x ≡ y) →
         cong (f ∘ g) p ≡ cong f (cong g p)
cong-∘ refl = refl

trans-cong : ∀ {x y z : A} {f : A → B} (p : x ≡ y) {q : y ≡ z} →
             trans (cong f p) (cong f q) ≡ cong f (trans p q)
trans-cong refl = refl

cong₂-reflˡ : ∀ {_∙_ : A → B → C} {x u v} → (p : u ≡ v) →
              cong₂ _∙_ refl p ≡ cong (x ∙_) p
cong₂-reflˡ refl = refl

cong₂-reflʳ : ∀ {_∙_ : A → B → C} {x y u} → (p : x ≡ y) →
              cong₂ _∙_ p refl ≡ cong (_∙ u) p
cong₂-reflʳ refl = refl

module _ {P : Pred A p} {x y : A} where

  subst-injective : ∀ (x≡y : x ≡ y) {p q : P x} →
                    subst P x≡y p ≡ subst P x≡y q → p ≡ q
  subst-injective refl p≡q = p≡q

  subst-subst : ∀ {z} (x≡y : x ≡ y) {y≡z : y ≡ z} {p : P x} →
                subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
  subst-subst refl = refl

  subst-subst-sym : (x≡y : x ≡ y) {p : P y} →
                    subst P x≡y (subst P (sym x≡y) p) ≡ p
  subst-subst-sym refl = refl

  subst-sym-subst : (x≡y : x ≡ y) {p : P x} →
                    subst P (sym x≡y) (subst P x≡y p) ≡ p
  subst-sym-subst refl = refl

subst-∘ : ∀ {x y : A} {P : Pred B p} {f : A → B}
          (x≡y : x ≡ y) {p : P (f x)} →
          subst (P ∘ f) x≡y p ≡ subst P (cong f x≡y) p
subst-∘ refl = refl

subst-application : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                    (B₁ : A₁ → Set b₁) {B₂ : A₂ → Set b₂}
                    {f : A₂ → A₁} {x₁ x₂ : A₂} {y : B₁ (f x₁)}
                    (g : ∀ x → B₁ (f x) → B₂ x) (eq : x₁ ≡ x₂) →
                    subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ (cong f eq) y)
subst-application _ _ refl = refl

------------------------------------------------------------------------
-- Structure of equality as a binary relation

isEquivalence : IsEquivalence {A = A} _≡_
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

isDecEquivalence : Decidable _≡_ → IsDecEquivalence {A = A} _≡_
isDecEquivalence _≟_ = record
  { isEquivalence = isEquivalence
  ; _≟_           = _≟_
  }

isPreorder : IsPreorder {A = A} _≡_ _≡_
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  }

------------------------------------------------------------------------
-- Bundles for equality as a binary relation

setoid : Set a → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = isEquivalence
  }

decSetoid : Decidable {A = A} _≡_ → DecSetoid _ _
decSetoid _≟_ = record
  { _≈_              = _≡_
  ; isDecEquivalence = isDecEquivalence _≟_
  }

preorder : Set a → Preorder _ _ _
preorder A = record
  { Carrier    = A
  ; _≈_        = _≡_
  ; _∼_        = _≡_
  ; isPreorder = isPreorder
  }
