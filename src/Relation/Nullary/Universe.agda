------------------------------------------------------------------------
-- The Agda standard library
--
-- A universe of proposition functors, along with some properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Universe where

open import Data.Sum.Base as Sum  hiding (map)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_; inj₁; inj₂)
open import Data.Product.Base as Product hiding (map)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Empty using (⊥)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)
open import Function.Base using (_∘_; id)
open import Function.Indexed.Relation.Binary.Equality using (≡-setoid)
open import Level using (Level; _⊔_; suc; Lift; lift; lower)
open import Relation.Nullary.Negation
  using  (¬_; contradiction; ¬¬-Monad; ¬¬-map; negated-stable)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Construct.Always as Always using (setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.PropositionalEquality.Properties as PropEq
  using (setoid)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
  as Trivial using (indexedSetoid)

infix  5 ¬¬_
infixr 4 _⇒_
infixr 3 _∧_
infixr 2 _∨_
infix  1 ⟨_⟩_≈_

-- The universe.

data PropF p : Set (suc p) where
  Id   : PropF p
  K    : (P : Set p) → PropF p
  _∨_  : (F₁ F₂ : PropF p) → PropF p
  _∧_  : (F₁ F₂ : PropF p) → PropF p
  _⇒_  : (P₁ : Set p) (F₂ : PropF p) → PropF p
  ¬¬_  : (F : PropF p) → PropF p

-- Equalities for universe inhabitants.

mutual

  setoid : ∀ {p} → PropF p → Set p → Setoid p p
  setoid Id        P = PropEq.setoid P
  setoid (K P)     _ = PropEq.setoid P
  setoid (F₁ ∨ F₂) P = (setoid F₁ P) ⊎ₛ (setoid F₂ P)
  setoid (F₁ ∧ F₂) P = (setoid F₁ P) ×ₛ (setoid F₂ P)
  setoid (P₁ ⇒ F₂) P = ≡-setoid P₁
                         (Trivial.indexedSetoid (setoid F₂ P))
  setoid (¬¬ F)    P = Always.setoid (¬ ¬ ⟦ F ⟧ P) _

  ⟦_⟧ : ∀ {p} → PropF p → (Set p → Set p)
  ⟦ F ⟧ P = Setoid.Carrier (setoid F P)

⟨_⟩_≈_ : ∀ {p} (F : PropF p) {P : Set p} → Rel (⟦ F ⟧ P) p
⟨_⟩_≈_ F = Setoid._≈_ (setoid F _)

-- ⟦ F ⟧ is functorial.

map : ∀ {p} (F : PropF p) {P Q} → (P → Q) → ⟦ F ⟧ P → ⟦ F ⟧ Q
map Id        f  p = f p
map (K P)     f  p = p
map (F₁ ∨ F₂) f FP = Sum.map  (map F₁ f) (map F₂ f) FP
map (F₁ ∧ F₂) f FP = Product.map (map F₁ f) (map F₂ f) FP
map (P₁ ⇒ F₂) f FP = map F₂ f ∘ FP
map (¬¬ F)    f FP = ¬¬-map (map F f) FP

map-id : ∀ {p} (F : PropF p) {P} → ⟨ ⟦ F ⟧ P ⇒ F ⟩ map F id ≈ id
map-id Id        x        = refl
map-id (K P)     x        = refl
map-id (F₁ ∨ F₂) (inj₁ x) = inj₁ (map-id F₁ x)
map-id (F₁ ∨ F₂) (inj₂ y) = inj₂ (map-id F₂ y)
map-id (F₁ ∧ F₂) (x , y)  = (map-id F₁ x , map-id F₂ y)
map-id (P₁ ⇒ F₂) f        = λ x → map-id F₂ (f x)
map-id (¬¬ F)    ¬¬x      = _

map-∘ : ∀ {p} (F : PropF p) {P Q R} (f : Q → R) (g : P → Q) →
        ⟨ ⟦ F ⟧ P ⇒ F ⟩ map F f ∘ map F g ≈ map F (f ∘ g)
map-∘ Id        f g x        = refl
map-∘ (K P)     f g x        = refl
map-∘ (F₁ ∨ F₂) f g (inj₁ x) = inj₁ (map-∘ F₁ f g x)
map-∘ (F₁ ∨ F₂) f g (inj₂ y) = inj₂ (map-∘ F₂ f g y)
map-∘ (F₁ ∧ F₂) f g x        = (map-∘ F₁ f g (proj₁ x) ,
                                map-∘ F₂ f g (proj₂ x))
map-∘ (P₁ ⇒ F₂) f g h        = λ x → map-∘ F₂ f g (h x)
map-∘ (¬¬ F)    f g x        = _

-- A variant of sequence can be implemented for ⟦ F ⟧.

sequence : ∀ {p AF} → RawApplicative AF →
           (AF (Lift p ⊥) → ⊥) →
           ({A B : Set p} → (A → AF B) → AF (A → B)) →
           ∀ F {P} → ⟦ F ⟧ (AF P) → AF (⟦ F ⟧ P)
sequence {AF = AF} A extract-⊥ sequence-⇒ = helper
  where
  open RawApplicative A

  helper : ∀ F {P} → ⟦ F ⟧ (AF P) → AF (⟦ F ⟧ P)
  helper Id        x        = x
  helper (K P)     x        = pure x
  helper (F₁ ∨ F₂) (inj₁ x) = inj₁ <$> helper F₁ x
  helper (F₁ ∨ F₂) (inj₂ y) = inj₂ <$> helper F₂ y
  helper (F₁ ∧ F₂) (x , y)  = _,_  <$> helper F₁ x ⊛ helper F₂ y
  helper (P₁ ⇒ F₂) f        = sequence-⇒ (helper F₂ ∘ f)
  helper (¬¬ F)    x        =
    pure (λ ¬FP → x (λ fp → extract-⊥ (lift ∘ ¬FP <$> helper F fp)))

-- Some lemmas about double negation.

private
  open module M {a} = RawMonad (¬¬-Monad {a = a})

¬¬-pull : ∀ {p} (F : PropF p) {P} →
          ⟦ F ⟧ (¬ ¬ P) → ¬ ¬ ⟦ F ⟧ P
¬¬-pull = sequence rawApplicative
                   (λ f → f lower)
                   (λ f g → g (λ x → contradiction (λ y → g (λ _ → y)) (f x)))

¬¬-remove : ∀ {p} (F : PropF p) {P} →
            ¬ ¬ ⟦ F ⟧ (¬ ¬ P) → ¬ ¬ ⟦ F ⟧ P
¬¬-remove F = negated-stable ∘ ¬¬-pull (¬¬ F)
