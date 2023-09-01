------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional (intensional) equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.PropositionalEquality where

import Axiom.Extensionality.Propositional as Ext
open import Axiom.UniquenessOfIdentityProofs
open import Function.Base using (id; _∘_)
open import Function.Equality using (Π; _⟶_; ≡-setoid)
open import Level using (Level; _⊔_)
open import Data.Product.Base using (∃)

open import Relation.Nullary.Decidable using (yes; no; dec-yes-irr; dec-no)
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
-- Re-export contents modules that make up the parts

open import Relation.Binary.PropositionalEquality.Core public
open import Relation.Binary.PropositionalEquality.Properties public
open import Relation.Binary.PropositionalEquality.Algebra public

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
-- Propositionality

isPropositional : Set a → Set a
isPropositional A = (a b : A) → a ≡ b

------------------------------------------------------------------------
-- More complex rearrangement lemmas

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
cong-≡id {f = f} {x} f≡id = begin
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

module _ (_≟_ : DecidableEquality A) {x y : A} where

  ≡-≟-identity : (eq : x ≡ y) → x ≟ y ≡ yes eq
  ≡-≟-identity eq = dec-yes-irr (x ≟ y) (Decidable⇒UIP.≡-irrelevant _≟_) eq

  ≢-≟-identity : (x≢y : x ≢ y) → x ≟ y ≡ no x≢y
  ≢-≟-identity = dec-no (x ≟ y)




------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

record Reveal_·_is_ {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

{-# WARNING_ON_USAGE Reveal_·_is_
"Warning: Reveal_·_is_ was deprecated in v2.0.
Please use new `with ... in` syntax described at https://agda.readthedocs.io/en/v2.6.3/language/with-abstraction.html#with-abstraction-equality instead."
#-}
{-# WARNING_ON_USAGE inspect
"Warning: inspect was deprecated in v2.0.
Please use new `with ... in` syntax described at https://agda.readthedocs.io/en/v2.6.3/language/with-abstraction.html#with-abstraction-equality instead."
#-}
