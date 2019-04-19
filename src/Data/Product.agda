------------------------------------------------------------------------
-- The Agda standard library
--
-- Products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product where

open import Function
open import Level
open import Relation.Nullary
open import Agda.Builtin.Equality

private
  variable
    a b c d e f ℓ p q r : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e
    F : Set f

------------------------------------------------------------------------
-- Definition of dependent products

open import Agda.Builtin.Sigma public
  renaming (fst to proj₁; snd to proj₂)
  hiding (module Σ)

module Σ = Agda.Builtin.Sigma.Σ
  renaming (fst to proj₁; snd to proj₂)

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

infix 2 Σ-syntax

Σ-syntax : (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

------------------------------------------------------------------------
-- Definition of non-dependent products

infixr 4 _,′_
infixr 2 _×_

_×_ : ∀ (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

_,′_ : A → B → A × B
_,′_ = _,_

------------------------------------------------------------------------
-- Existential quantifiers

∃ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∄ : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄ P = ¬ ∃ P

∃₂ : ∀ {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

-- Unique existence (parametrised by an underlying equality).

∃! : {A : Set a} → (A → A → Set ℓ) → (A → Set b) → Set (a ⊔ b ⊔ ℓ)
∃! _≈_ B = ∃ λ x → B x × (∀ {y} → B y → x ≈ y)

-- Syntax

∃-syntax : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

∄-syntax : ∀ {A : Set a} → (A → Set b) → Set (a ⊔ b)
∄-syntax = ∄

syntax ∄-syntax (λ x → B) = ∄[ x ] B

------------------------------------------------------------------------
-- Operations over dependent products

infix  4 -,_
infixr 2 _-×-_ _-,-_

-- Sometimes the first component can be inferred.

-,_ : ∀ {A : Set a} {B : A → Set b} {x} → B x → ∃ B
-, y = _ , y

<_,_> : ∀ {A : Set a} {B : A → Set b} {C : ∀ {x} → B x → Set c}
        (f : (x : A) → B x) → ((x : A) → C (f x)) →
        ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

map : ∀ {P : A → Set p} {Q : B → Set q} →
      (f : A → B) → (∀ {x} → P x → Q (f x)) →
      Σ A P → Σ B Q
map f g (x , y) = (f x , g y)

map₁ : (A → B) → A × C → B × C
map₁ f = map f id

map₂ : ∀ {A : Set a} {B : A → Set b} {C : A → Set c} →
       (∀ {x} → B x → C x) → Σ A B → Σ A C
map₂ f = map id f

zip : ∀ {P : A → Set p} {Q : B → Set q} {R : C → Set r} →
      (_∙_ : A → B → C) →
      (∀ {x y} → P x → Q y → R (x ∙ y)) →
      Σ A P → Σ B Q → Σ C R
zip _∙_ _∘_ (a , p) (b , q) = ((a ∙ b) , (p ∘ q))

curry : ∀ {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

------------------------------------------------------------------------
-- Operations for non-dependent products

-- Any of the above operations for dependent products will also work for
-- non-dependent products but sometimes Agda has difficulty inferring
-- the non-dependency. Primed (′ = \prime) versions of the operations
-- are therefore provided below that sometimes have better inference
-- properties.

zip′ : (A → B → C) → (D → E → F) → A × D → B × E → C × F
zip′ f g = zip f g

curry′ : (A × B → C) → (A → B → C)
curry′ = curry

uncurry′ : (A → B → C) → (A × B → C)
uncurry′ = uncurry

-- Operations that can only be defined for non-dependent products

swap : A × B → B × A
swap (x , y) = (y , x)

_-×-_ : (A → B → Set p) → (A → B → Set q) → (A → B → Set _)
f -×- g = f -[ _×_ ]- g

_-,-_ : (A → B → C) → (A → B → D) → (A → B → C × D)
f -,- g = f -[ _,_ ]- g
