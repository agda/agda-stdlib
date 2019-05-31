------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple combinators working solely on and with functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function where

open import Level
open import Strict

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

------------------------------------------------------------------------
-- Types

Fun₁ : Set a → Set a
Fun₁ A = A → A

Fun₂ : Set a → Set a
Fun₂ A = A → A → A

------------------------------------------------------------------------
-- Some simple functions

id : A → A
id x = x

const : A → B → A
const x = λ _ → x

------------------------------------------------------------------------
-- Operations on dependent functions

-- These are functions whose output has a type that depends on the
-- value of the input to the function.

infixr 9 _∘_
infixl 8 _ˢ_
infixl 0 _|>_
infix  0 case_return_of_
infixr -1 _$_ _$!_
infix  -1 _$-

-- Composition

_∘_ : ∀ {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

-- Flipping order of arguments

flip : ∀ {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

-- Application - note that _$_ is right associative, as in Haskell.
-- If you want a left associative infix application operator, use
-- Category.Functor._<$>_ from Category.Monad.Identity.IdentityMonad.

_$_ : ∀ {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

-- Strict (call-by-value) application

_$!_ : ∀ {A : Set a} {B : A → Set b} →
       ((x : A) → B x) → ((x : A) → B x)
_$!_ = flip force

-- Flipped application (aka pipe-forward)

_|>_ : ∀ {A : Set a} {B : A → Set b} →
       (a : A) → (∀ a → B a) → B a
_|>_ = flip _$_

-- The S combinator - written infix as in Conor McBride's paper
-- "Outrageous but Meaningful Coincidences: Dependent type-safe syntax
-- and evaluation".

_ˢ_ : ∀ {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
      ((x : A) (y : B x) → C x y) →
      (g : (x : A) → B x) →
      ((x : A) → C x (g x))
f ˢ g = λ x → f x (g x)

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_return_of_ : ∀ {A : Set a} (x : A) (B : A → Set b) →
                  ((x : A) → B x) → B x
case x return B of f = f x

-- Converting between implicit and explicit function spaces.

_$- : ∀ {A : Set a}{B : A → Set b} →
      ((x : A) → B x) → ({x : A} → B x)
f $- = f _

λ- : ∀ {A : Set a}{B : A → Set b} →
       ({x : A} → B x) → ((x : A) → B x)
λ- f = λ x → f

------------------------------------------------------------------------
-- Non-dependent versions of dependent operations

-- Any of the above operations for dependent functions will also work
-- for non-dependent functions but sometimes Agda has difficulty
-- inferring the non-dependency. Primed (′ = \prime) versions of the
-- operations are therefore provided below that sometimes have better
-- inference properties.

infixr 9 _∘′_
infixl 0 _|>′_
infix  0 case_of_
infixr -1 _$′_ _$!′_

-- Composition

_∘′_ : (B → C) → (A → B) → (A → C)
f ∘′ g = _∘_ f g

-- Application

_$′_ : (A → B) → (A → B)
_$′_ = _$_

-- Strict (call-by-value) application

_$!′_ : (A → B) → (A → B)
_$!′_ = _$!_

-- Flipped application (aka pipe-forward)

_|>′_ : A → (A → B) → B
_|>′_ = _|>_

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_of_ : A → (A → B) → B
case x of f = case x return _ of f

------------------------------------------------------------------------
-- Operations that are only defined for non-dependent functions

infixr 0 _-[_]-_
infixl 1 _on_
infixl 1 _⟨_⟩_
infixl 0 _∋_

-- Binary application

_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

-- Composition of a binary function with a unary function

_on_ : (B → B → C) → (A → B) → (A → A → C)
_*_ on f = λ x y → f x * f y

-- Composition of three binary functions

_-[_]-_ : (A → B → C) → (C → D → E) → (A → B → D) → (A → B → E)
f -[ _*_ ]- g = λ x y → f x y * g x y

-- In Agda you cannot annotate every subexpression with a type
-- signature. This function can be used instead.

_∋_ : (A : Set a) → A → A
A ∋ x = x

-- Conversely it is sometimes useful to be able to extract the
-- type of a given expression.

typeOf : {A : Set a} → A → Set a
typeOf {A = A} _ = A
