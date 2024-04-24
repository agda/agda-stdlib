------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-dependent product combinators for setoid equality preserving
-- functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Function.NonDependent.Setoid where

open import Data.Product.Base as Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Function.Bundles
  using (Func; Equivalence; Injection; Surjection; Bijection; LeftInverse;
         RightInverse; Inverse)

private
  variable
    a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Level
    a ℓ : Level
    A B C D : Setoid a ℓ

------------------------------------------------------------------------
-- Combinators for equality preserving functions

proj₁ₛ : Func (A ×ₛ B) A
proj₁ₛ = record { to = proj₁ ; cong = proj₁ }

proj₂ₛ : Func (A ×ₛ B) B
proj₂ₛ = record { to = proj₂ ; cong = proj₂ }

<_,_>ₛ : Func A B → Func A C → Func A (B ×ₛ C)
< f , g >ₛ = record
  { to   = < to   f , to   g >
  ; cong = < cong f , cong g >
  } where open Func

swapₛ : Func (A ×ₛ B) (B ×ₛ A)
swapₛ = < proj₂ₛ , proj₁ₛ >ₛ

------------------------------------------------------------------------
-- Function bundles

_×-function_ : Func A B → Func C D → Func (A ×ₛ C) (B ×ₛ D)
f ×-function g = record
  { to    = Product.map (to f) (to g)
  ; cong  = Product.map (cong f) (cong g)
  } where open Func

infixr 2 _×-equivalence_ _×-injection_ _×-left-inverse_

_×-equivalence_ : Equivalence A B → Equivalence C D →
                  Equivalence (A ×ₛ C) (B ×ₛ D)
_×-equivalence_ f g = record
  { to        = Product.map (to f) (to g)
  ; from      = Product.map (from f) (from g)
  ; to-cong   = Product.map (to-cong f) (to-cong g)
  ; from-cong = Product.map (from-cong f) (from-cong g)
  } where open Equivalence

_×-injection_ : Injection A B → Injection C D →
                Injection (A ×ₛ C) (B ×ₛ D)
f ×-injection g = record
  { to        = Product.map (to f) (to g)
  ; cong      = Product.map (cong f) (cong g)
  ; injective = Product.map (injective f) (injective g)
  } where open Injection

_×-surjection_ : Surjection A B → Surjection C D →
                 Surjection (A ×ₛ C) (B ×ₛ D)
f ×-surjection g = record
  { to         = Product.map (to f) (to g)
  ; cong       = Product.map (cong f) (cong g)
  ; surjective = λ y → Product.zip _,_ (λ ff gg x₂ → (ff (proj₁ x₂)) , (gg (proj₂ x₂))) (surjective f (proj₁ y)) (surjective g (proj₂ y))
  } where open Surjection

_×-bijection_ : Bijection A B → Bijection C D →
                Bijection (A ×ₛ C) (B ×ₛ D)
f ×-bijection g = record
  { to         = Product.map (to f) (to g)
  ; cong       = Product.map (cong f) (cong g)
  ; bijective  = Product.map (injective f) (injective g) ,
                 λ { (y₀ , y₁) → Product.zip _,_ (λ {ff gg (x₀ , x₁) → ff x₀ , gg x₁}) (surjective f y₀) (surjective g y₁)}
  } where open Bijection

_×-leftInverse_ : LeftInverse A B → LeftInverse C D →
                  LeftInverse (A ×ₛ C) (B ×ₛ D)
f ×-leftInverse g = record
  { to        = Product.map (to f) (to g)
  ; from      = Product.map (from f) (from g)
  ; to-cong   = Product.map (to-cong f) (to-cong g)
  ; from-cong = Product.map (from-cong f) (from-cong g)
  ; inverseˡ   = λ x → inverseˡ f (proj₁ x) , inverseˡ g (proj₂ x)
  } where open LeftInverse

_×-rightInverse_ : RightInverse A B → RightInverse C D →
                   RightInverse (A ×ₛ C) (B ×ₛ D)
f ×-rightInverse g = record
  { to        = Product.map (to f) (to g)
  ; from      = Product.map (from f) (from g)
  ; to-cong   = Product.map (to-cong f) (to-cong g)
  ; from-cong = Product.map (from-cong f) (from-cong g)
  ; inverseʳ   = λ x → inverseʳ f (proj₁ x) , inverseʳ g (proj₂ x)
  } where open RightInverse

infixr 2 _×-surjection_ _×-inverse_

_×-inverse_ : Inverse A B → Inverse C D →
              Inverse (A ×ₛ C) (B ×ₛ D)
f ×-inverse g = record
  { to        = Product.map (to f) (to g)
  ; from      = Product.map (from f) (from g)
  ; to-cong   = Product.map (to-cong f) (to-cong g)
  ; from-cong = Product.map (from-cong f) (from-cong g)
  ; inverse   = (λ x → inverseˡ f (proj₁ x) , inverseˡ g (proj₂ x)) ,
                (λ x → inverseʳ f (proj₁ x) , inverseʳ g (proj₂ x))
  } where open Inverse



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

_×-left-inverse_ = _×-leftInverse_
{-# WARNING_ON_USAGE _×-left-inverse_
"Warning: _×-left-inverse_ was deprecated in v2.0.
Please use _×-leftInverse_ instead."
#-}
