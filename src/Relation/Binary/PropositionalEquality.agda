------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional (intensional) equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.PropositionalEquality where

open import Axiom.UniquenessOfIdentityProofs
open import Function.Base using (id; _∘_)
import Function.Dependent.Bundles as Dependent using (Func)
open import Function.Indexed.Relation.Binary.Equality using (≡-setoid)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Relation.Nullary.Decidable using (yes; no; dec-yes-irr; dec-no)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
  as Trivial using (indexedSetoid)

private
  variable
    a b c ℓ p : Level
    A B C : Set a

------------------------------------------------------------------------
-- Re-export contents modules that make up the parts

open import Relation.Binary.PropositionalEquality.Core public
open import Relation.Binary.PropositionalEquality.Properties public
open import Relation.Binary.PropositionalEquality.Algebra public

------------------------------------------------------------------------
-- Pointwise equality

_→-setoid_ : ∀ (A : Set a) (B : Set b) → Setoid _ _
A →-setoid B = ≡-setoid A (Trivial.indexedSetoid (setoid B))

:→-to-Π : ∀ {A : Set a} {B : IndexedSetoid A b ℓ} →
          ((x : A) → IndexedSetoid.Carrier B x) →
          Dependent.Func (setoid A) B
:→-to-Π {B = B} f = record
  { to = f
  ; cong = λ { refl → IndexedSetoid.refl B }
  }

→-to-⟶ : ∀ {A : Set a} {B : Setoid b ℓ} →
         (A → Setoid.Carrier B) →
         Dependent.Func (setoid A) (Trivial.indexedSetoid B)
→-to-⟶ = :→-to-Π

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

module _ (_≡?_ : DecidableEquality A) {x y : A} where

  ≡-≡?-identity : (eq : x ≡ y) → x ≡? y ≡ yes eq
  ≡-≡?-identity eq = dec-yes-irr (x ≡? y) (Decidable⇒UIP.≡-irrelevant _≡?_) eq

  ≢-≡?-identity : (x≢y : x ≢ y) → x ≡? y ≡ no x≢y
  ≢-≡?-identity = dec-no (x ≡? y)


------------------------------------------------------------------------
-- Inspect

-- Inspect can be used when you want to pattern match on the result r
-- of some expression e, and you also need to "remember" that r ≡ e.

-- See README.Inspect for an explanation of how/why to use this.

-- Normally (but not always) the new `with ... in` syntax described at
-- https://agda.readthedocs.io/en/v2.6.4/language/with-abstraction.html#with-abstraction-equality
-- can be used instead."

record Reveal_·_is_ {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

isPropositional : Set a → Set a
isPropositional = Irrelevant

{-# WARNING_ON_USAGE isPropositional
"Warning: isPropositional was deprecated in v2.0.
Please use Relation.Nullary.Irrelevant instead. "
#-}

-- Version 2.4

≡-≟-identity = ≡-≡?-identity
{-# WARNING_ON_USAGE ≡-≟-identity
"Warning: ≡-≟-identity was deprecated in v2.4.
Please use ≡-≡?-identity instead."
#-}

≢-≟-identity = ≢-≡?-identity
{-# WARNING_ON_USAGE ≢-≟-identity
"Warning: ≢-≟-identity was deprecated in v2.4.
Please use ≢-≡?-identity instead."
#-}
