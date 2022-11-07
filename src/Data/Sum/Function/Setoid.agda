------------------------------------------------------------------------
-- The Agda standard library
--
-- Sum combinators for setoid equality preserving functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Function.Setoid where

open import Data.Product.Base as Prod using (_,_)
open import Data.Sum.Base as Sum
open import Data.Sum.Relation.Binary.Pointwise as Pointwise
open import Relation.Binary
open import Function.Base
open import Function.Bundles
open import Function.Definitions hiding (Surjective)
open import Function.Definitions.Core2
open import Level

private
  variable
    a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Level
    a ℓ : Level
    A B C D : Set a
    ≈₁ ≈₂ ≈₃ ≈₄ : Rel A ℓ
    S T U V : Setoid a ℓ

------------------------------------------------------------------------
-- Combinators for equality preserving functions

inj₁ₛ : Func S (S ⊎ₛ T)
inj₁ₛ = record { to = inj₁ ; cong = inj₁ }

inj₂ₛ : Func T (S ⊎ₛ T)
inj₂ₛ = record { to = inj₂ ; cong = inj₂ }

[_,_]ₛ : Func S U → Func T U → Func (S ⊎ₛ T) U
[ f , g ]ₛ = record
  { to   = [ to f , to g ]
  ; cong = λ where
    (inj₁ x∼₁y) → cong f x∼₁y
    (inj₂ x∼₂y) → cong g x∼₂y
  } where open Func

swapₛ : Func (S ⊎ₛ T) (T ⊎ₛ S)
swapₛ = [ inj₂ₛ , inj₁ₛ ]ₛ

------------------------------------------------------------------------
-- Definitions

⊎-injective : ∀ {f g} →
              Injective ≈₁ ≈₂ f →
              Injective ≈₃ ≈₄ g →
              Injective (Pointwise ≈₁ ≈₃) (Pointwise ≈₂ ≈₄) (Sum.map f g)
⊎-injective f-inj g-inj {inj₁ x} {inj₁ y} (inj₁ x∼₁y) = inj₁ (f-inj x∼₁y)
⊎-injective f-inj g-inj {inj₂ x} {inj₂ y} (inj₂ x∼₂y) = inj₂ (g-inj x∼₂y)

⊎-surjective : ∀ {f : A → B} {g : C → D} →
              Surjective ≈₁ f →
              Surjective ≈₂ g →
              Surjective (Pointwise ≈₁ ≈₂) (Sum.map f g)
⊎-surjective f-sur g-sur =
  [ Prod.map inj₁ inj₁ ∘ f-sur
  , Prod.map inj₂ inj₂ ∘ g-sur
  ]

------------------------------------------------------------------------
-- Function bundles

_⊎-function_ : Func S T → Func U V → Func (S ⊎ₛ U) (T ⊎ₛ V)
S→T ⊎-function U→V = record
  { to    = Sum.map (to S→T) (to U→V)
  ; cong  = Pointwise.map (cong S→T) (cong U→V)
  } where open Func

_⊎-equivalence_ : Equivalence S T → Equivalence U V →
                  Equivalence (S ⊎ₛ U) (T ⊎ₛ V)
S⇔T ⊎-equivalence U⇔V = record
  { to        = Sum.map (to S⇔T) (to U⇔V)
  ; from      = Sum.map (from S⇔T) (from U⇔V)
  ; to-cong   = Pointwise.map (to-cong S⇔T) (to-cong U⇔V)
  ; from-cong = Pointwise.map (from-cong S⇔T) (from-cong U⇔V)
  } where open Equivalence

_⊎-injection_ : Injection S T → Injection U V →
                Injection (S ⊎ₛ U) (T ⊎ₛ V)
S↣T ⊎-injection U↣V = record
  { to        = Sum.map (to S↣T) (to U↣V)
  ; cong      = Pointwise.map (cong S↣T) (cong U↣V)
  ; injective = ⊎-injective (injective S↣T) (injective U↣V)
  } where open Injection

_⊎-surjection_ : Surjection S T → Surjection U V →
                 Surjection (S ⊎ₛ U) (T ⊎ₛ V)
S↠T ⊎-surjection U↠V = record
  { to              = Sum.map (to S↠T) (to U↠V)
  ; cong            = Pointwise.map (cong S↠T) (cong U↠V)
  ; surjective      = ⊎-surjective (surjective S↠T) (surjective U↠V)
  } where open Surjection

_⊎-bijection_ : Bijection S T → Bijection U V →
                 Bijection (S ⊎ₛ U) (T ⊎ₛ V)
S⤖T ⊎-bijection U⤖V = record
  { to        = Sum.map (to S⤖T) (to U⤖V)
  ; cong      = Pointwise.map (cong S⤖T) (cong U⤖V)
  ; bijective = ⊎-injective (injective S⤖T) (injective U⤖V) ,
                ⊎-surjective (surjective S⤖T) (surjective U⤖V)
  } where open Bijection

_⊎-leftInverse_ : LeftInverse S T → LeftInverse U V →
                  LeftInverse (S ⊎ₛ U) (T ⊎ₛ V)
S↩T ⊎-leftInverse U↩V = record
  { to              = Sum.map (to S↩T) (to U↩V)
  ; from            = Sum.map (from S↩T) (from U↩V)
  ; to-cong         = Pointwise.map (to-cong S↩T) (to-cong U↩V)
  ; from-cong       = Pointwise.map (from-cong S↩T) (from-cong U↩V)
  ; inverseˡ        = [ inj₁ ∘ inverseˡ S↩T , inj₂ ∘ inverseˡ U↩V ]
  } where open LeftInverse

_⊎-rightInverse_ : RightInverse S T → RightInverse U V →
                   RightInverse (S ⊎ₛ U) (T ⊎ₛ V)
S↪T ⊎-rightInverse U↪V = record
  { to              = Sum.map (to S↪T) (to U↪V)
  ; from            = Sum.map (from S↪T) (from U↪V)
  ; to-cong         = Pointwise.map (to-cong S↪T) (to-cong U↪V)
  ; from-cong       = Pointwise.map (from-cong S↪T) (from-cong U↪V)
  ; inverseʳ        = [ inj₁ ∘ inverseʳ S↪T , inj₂ ∘ inverseʳ U↪V ]
  } where open RightInverse

_⊎-inverse_ : Inverse S T → Inverse U V →
              Inverse (S ⊎ₛ U) (T ⊎ₛ V)
S↔T ⊎-inverse U↔V = record
  { to        = Sum.map (to S↔T) (to U↔V)
  ; from      = Sum.map (from S↔T) (from U↔V)
  ; to-cong   = Pointwise.map (to-cong S↔T) (to-cong U↔V)
  ; from-cong = Pointwise.map (from-cong S↔T) (from-cong U↔V)
  ; inverse   = [ inj₁ ∘ inverseˡ S↔T , inj₂ ∘ inverseˡ U↔V ] ,
                [ inj₁ ∘ inverseʳ S↔T , inj₂ ∘ inverseʳ U↔V ]
  } where open Inverse



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

_⊎-left-inverse_ = _⊎-leftInverse_
{-# WARNING_ON_USAGE _⊎-left-inverse_
"Warning: _⊎-left-inverse_ was deprecated in v2.0.
Please use _⊎-leftInverse_ instead."
#-}
