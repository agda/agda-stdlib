------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple combinators working solely on and with functions
------------------------------------------------------------------------

-- The contents of this module is also accessible via the `Function`
-- module. See `Function.Strict` for strict versions of these
-- combinators.

{-# OPTIONS --without-K --safe #-}

module Function.Base where

open import Level using (Level)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

------------------------------------------------------------------------
-- Some simple functions

id : A → A
id x = x

const : A → B → A
const x = λ _ → x

constᵣ : A → B → B
constᵣ _ = id

------------------------------------------------------------------------
-- Operations on dependent functions

-- These are functions whose output has a type that depends on the
-- value of the input to the function.

infixr 9 _∘_ _∘₂_
infixl 8 _ˢ_
infixl 0 _|>_
infix  0 case_returning_of_ case_return_of_
infixr -1 _$_

-- Composition

_∘_ : ∀ {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

_∘₂_ : ∀ {A₁ : Set a} {A₂ : A₁ → Set d}
         {B : (x : A₁) → A₂ x → Set b}
         {C : {x : A₁} → {y : A₂ x} → B x y → Set c} →
       ({x : A₁} → {y : A₂ x} → (z : B x y) → C z) →
       (g : (x : A₁) → (y : A₂ x) → B x y) →
       ((x : A₁) → (y : A₂ x) → C (g x y))
f ∘₂ g = λ x y → f (g x y)

-- Flipping order of arguments

flip : ∀ {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y
{-# INLINE flip #-}

-- Application - note that _$_ is right associative, as in Haskell.
-- If you want a left associative infix application operator, use
-- RawFunctor._<$>_ from Effect.Functor.

_$_ : ∀ {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}

-- Flipped application (aka pipe-forward)

_|>_ : ∀ {A : Set a} {B : A → Set b} →
       (a : A) → (∀ a → B a) → B a
_|>_ = flip _$_
{-# INLINE _|>_ #-}

-- The S combinator - written infix as in Conor McBride's paper
-- "Outrageous but Meaningful Coincidences: Dependent type-safe syntax
-- and evaluation".

_ˢ_ : ∀ {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
      ((x : A) (y : B x) → C x y) →
      (g : (x : A) → B x) →
      ((x : A) → C x (g x))
f ˢ g = λ x → f x (g x)
{-# INLINE _ˢ_ #-}

-- Converting between implicit and explicit function spaces.

_$- : ∀ {A : Set a} {B : A → Set b} → ((x : A) → B x) → ({x : A} → B x)
f $- = f _
{-# INLINE _$- #-}

λ- : ∀ {A : Set a} {B : A → Set b} → ({x : A} → B x) → ((x : A) → B x)
λ- f = λ x → f
{-# INLINE λ- #-}

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_returning_of_ : ∀ {A : Set a} (x : A) (B : A → Set b) →
                  ((x : A) → B x) → B x
case x returning B of f = f x
{-# INLINE case_returning_of_ #-}

------------------------------------------------------------------------
-- Non-dependent versions of dependent operations

-- Any of the above operations for dependent functions will also work
-- for non-dependent functions but sometimes Agda has difficulty
-- inferring the non-dependency. Primed (′ = \prime) versions of the
-- operations are therefore provided below that sometimes have better
-- inference properties.

infixr 9 _∘′_ _∘₂′_
infixl 0 _|>′_
infix  0 case_of_
infixr -1 _$′_

-- Composition

_∘′_ : (B → C) → (A → B) → (A → C)
f ∘′ g = _∘_ f g

_∘₂′_ : (C → D) → (A → B → C) → (A → B → D)
f ∘₂′ g = _∘₂_ f g

-- Flipping order of arguments

flip′ : (A → B → C) → (B → A → C)
flip′ = flip

-- Application

_$′_ : (A → B) → (A → B)
_$′_ = _$_

-- Flipped application (aka pipe-forward)

_|>′_ : A → (A → B) → B
_|>′_ = _|>_

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

case_of_ : A → (A → B) → B
case x of f = case x returning _ of f
{-# INLINE case_of_ #-}

------------------------------------------------------------------------
-- Operations that are only defined for non-dependent functions

infixl 1 _⟨_⟩_
infixl 0 _∋_

-- Binary application

_⟨_⟩_ : A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

-- In Agda you cannot annotate every subexpression with a type
-- signature. This function can be used instead.

_∋_ : (A : Set a) → A → A
A ∋ x = x

-- Conversely it is sometimes useful to be able to extract the
-- type of a given expression.

typeOf : {A : Set a} → A → Set a
typeOf {A = A} _ = A

-- Construct an element of the given type by instance search.

it : {A : Set a} → {{A}} → A
it {{x}} = x

------------------------------------------------------------------------
-- Composition of a binary function with other functions

infixr 0 _-⟪_⟫-_ _-⟨_⟫-_
infixl 0 _-⟪_⟩-_
infixr 1 _-⟨_⟩-_ ∣_⟫-_ ∣_⟩-_
infixl 1 _on_ _on₂_ _-⟪_∣ _-⟨_∣

-- Two binary functions

_-⟪_⟫-_ : (A → B → C) → (C → D → E) → (A → B → D) → (A → B → E)
f -⟪ _*_ ⟫- g = λ x y → f x y * g x y

-- A single binary function on the left

_-⟪_∣ : (A → B → C) → (C → B → D) → (A → B → D)
f -⟪ _*_ ∣ = f -⟪ _*_ ⟫- constᵣ

-- A single binary function on the right

∣_⟫-_ : (A → C → D) → (A → B → C) → (A → B → D)
∣ _*_ ⟫- g = const -⟪ _*_ ⟫- g

-- A single unary function on the left

_-⟨_∣ : (A → C) → (C → B → D) → (A → B → D)
f -⟨ _*_ ∣ = f ∘₂ const -⟪ _*_ ∣

-- A single unary function on the right

∣_⟩-_ : (A → C → D) → (B → C) → (A → B → D)
∣ _*_ ⟩- g = ∣ _*_ ⟫- g ∘₂ constᵣ

-- A binary function and a unary function

_-⟪_⟩-_ : (A → B → C) → (C → D → E) → (B → D) → (A → B → E)
f -⟪ _*_ ⟩- g = f -⟪ _*_ ⟫- ∣ constᵣ ⟩- g

-- A unary function and a binary function

_-⟨_⟫-_ : (A → C) → (C → D → E) → (A → B → D) → (A → B → E)
f -⟨ _*_ ⟫- g = f -⟨ const ∣ -⟪ _*_ ⟫- g

-- Two unary functions

_-⟨_⟩-_ : (A → C) → (C → D → E) → (B → D) → (A → B → E)
f -⟨ _*_ ⟩- g = f -⟨ const ∣ -⟪ _*_ ⟫- ∣ constᵣ ⟩- g

-- A single binary function on both sides

_on₂_ : (C → C → D) → (A → B → C) → (A → B → D)
_*_ on₂ f = f -⟪ _*_ ⟫- f

-- A single unary function on both sides

_on_ : (B → B → C) → (A → B) → (A → A → C)
_*_ on f = f -⟨ _*_ ⟩- f


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.4

_-[_]-_ = _-⟪_⟫-_
{-# WARNING_ON_USAGE _-[_]-_
"Warning: Function._-[_]-_ was deprecated in v1.4.
Please use _-⟪_⟫-_ instead."
#-}

-- Version 2.0

case_return_of_ = case_returning_of_
{-# WARNING_ON_USAGE case_return_of_
"case_return_of_ was deprecated in v2.0.
Please use case_returning_of_ instead."
#-}

