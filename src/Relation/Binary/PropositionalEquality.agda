------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional (intensional) equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality where

import Axiom.Extensionality.Propositional as Ext
open import Axiom.UniquenessOfIdentityProofs
open import Function.Core
open import Function.Equality using (Π; _⟶_; ≡-setoid)
open import Level
open import Data.Empty
open import Data.Product
open import Relation.Nullary using (yes ; no)
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
  as Trivial

private
  variable
    a b c ℓ p : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Re-export contents of core module

open import Relation.Binary.PropositionalEquality.Core public

------------------------------------------------------------------------
-- Some properties

subst₂ : ∀ (_∼_ : REL A B ℓ) {x y u v} → x ≡ y → u ≡ v → x ∼ u → y ∼ v
subst₂ _ refl refl p = p

cong-app : ∀ {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

cong₂ : ∀ (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

setoid : Set a → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = isEquivalence
  }

decSetoid : Decidable {A = A} _≡_ → DecSetoid _ _
decSetoid dec = record
  { _≈_              = _≡_
  ; isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = dec
      }
  }

isPreorder : IsPreorder {A = A} _≡_ _≡_
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  }

preorder : Set a → Preorder _ _ _
preorder A = record
  { Carrier    = A
  ; _≈_        = _≡_
  ; _∼_        = _≡_
  ; isPreorder = isPreorder
  }

------------------------------------------------------------------------
-- Pointwise equality

infix 4 _≗_

_→-setoid_ : ∀ (A : Set a) (B : Set b) → Setoid _ _
A →-setoid B = ≡-setoid A (Trivial.indexedSetoid (setoid B))

_≗_ : (f g : A → B) → Set _
_≗_ {A = A} {B = B} = Setoid._≈_ (A →-setoid B)

:→-to-Π : ∀ {A : Set a} {B : IndexedSetoid A b ℓ} →
          ((x : A) → IndexedSetoid.Carrier B x) → Π (setoid A) B
:→-to-Π {B = B} f = record
  { _⟨$⟩_ = f
  ; cong  = λ { refl → IndexedSetoid.refl B }
  }
  where open IndexedSetoid B using (_≈_)

→-to-⟶ : ∀ {A : Set a} {B : Setoid b ℓ} →
         (A → Setoid.Carrier B) → setoid A ⟶ B
→-to-⟶ = :→-to-Π

------------------------------------------------------------------------
-- Inspect

-- Inspect can be used when you want to pattern match on the result r
-- of some expression e, and you also need to "remember" that r ≡ e.

-- See README.Inspect for an explanation of how/why to use this.

record Reveal_·_is_ {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

------------------------------------------------------------------------
-- Propositionality

isPropositional : Set a → Set a
isPropositional A = (a b : A) → a ≡ b

------------------------------------------------------------------------
-- Various equality rearrangement lemmas

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

-- A lemma that is very similar to Lemma 2.4.3 from the HoTT book.

naturality : ∀ {x y} {x≡y : x ≡ y} {f g : A → B}
             (f≡g : ∀ x → f x ≡ g x) →
             trans (cong f x≡y) (f≡g y) ≡ trans (f≡g x) (cong g x≡y)
naturality {x = x} {x≡y = refl} f≡g =
  f≡g x               ≡⟨ sym (trans-reflʳ _) ⟩
  trans (f≡g x) refl  ∎
  where open ≡-Reasoning

-- A lemma that is very similar to Corollary 2.4.4 from the HoTT book.

cong-≡id : ∀ {f : A → A} {x : A} (f≡id : ∀ x → f x ≡ x) →
           cong f (f≡id x) ≡ f≡id (f x)
cong-≡id {f = f} {x} f≡id =
  cong f fx≡x                                    ≡⟨ sym (trans-reflʳ _) ⟩
  trans (cong f fx≡x) refl                       ≡⟨ cong (trans _) (sym (trans-symʳ fx≡x)) ⟩
  trans (cong f fx≡x) (trans fx≡x (sym fx≡x))    ≡⟨ sym (trans-assoc (cong f fx≡x)) ⟩
  trans (trans (cong f fx≡x) fx≡x) (sym fx≡x)    ≡⟨ cong (λ p → trans p (sym _)) (naturality f≡id) ⟩
  trans (trans f²x≡x (cong id fx≡x)) (sym fx≡x)  ≡⟨ cong (λ p → trans (trans f²x≡x p) (sym fx≡x)) (cong-id _) ⟩
  trans (trans f²x≡x fx≡x) (sym fx≡x)            ≡⟨ trans-assoc f²x≡x ⟩
  trans f²x≡x (trans fx≡x (sym fx≡x))            ≡⟨ cong (trans _) (trans-symʳ fx≡x) ⟩
  trans f²x≡x refl                               ≡⟨ trans-reflʳ _ ⟩
  f≡id (f x)                                     ∎
  where open ≡-Reasoning; fx≡x = f≡id x; f²x≡x = f≡id (f x)

module _ (_≟_ : Decidable {A = A} _≡_) where

  ≡-≟-identity : ∀ {x y : A} (eq : x ≡ y) → x ≟ y ≡ yes eq
  ≡-≟-identity {x} {y} eq with x ≟ y
  ... | yes p = cong yes (Decidable⇒UIP.≡-irrelevant _≟_ p eq)
  ... | no ¬p = ⊥-elim (¬p eq)

  ≢-≟-identity : ∀ {x y : A} → x ≢ y → ∃ λ ¬eq → x ≟ y ≡ no ¬eq
  ≢-≟-identity {x} {y} ¬eq with x ≟ y
  ... | yes p = ⊥-elim (¬eq p)
  ... | no ¬p = ¬p , refl



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

Extensionality = Ext.Extensionality
{-# WARNING_ON_USAGE Extensionality
"Warning: Extensionality was deprecated in v1.0.
Please use Extensionality from `Axiom.Extensionality.Propositional` instead."
#-}
extensionality-for-lower-levels = Ext.lower-extensionality
{-# WARNING_ON_USAGE extensionality-for-lower-levels
"Warning: extensionality-for-lower-levels was deprecated in v1.0.
Please use lower-extensionality from `Axiom.Extensionality.Propositional` instead."
#-}
∀-extensionality = Ext.∀-extensionality
{-# WARNING_ON_USAGE ∀-extensionality
"Warning: ∀-extensionality was deprecated in v1.0.
Please use ∀-extensionality from `Axiom.Extensionality.Propositional` instead."
#-}
