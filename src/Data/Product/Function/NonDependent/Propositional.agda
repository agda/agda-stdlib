------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-dependent product combinators for propositional equality
-- preserving functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Function.NonDependent.Propositional where

open import Data.Product
open import Data.Product.Function.NonDependent.Setoid
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary
open import Function.Equality using (_⟶_)
open import Function.Equivalence as Eq using (_⇔_; module Equivalence)
open import Function.Injection as Inj using (_↣_; module Injection)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (_↞_; _LeftInverseOf_; module LeftInverse)
open import Function.Related
open import Function.Surjection as Surj using (_↠_; module Surjection)

------------------------------------------------------------------------
-- Combinators for various function types

module _ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} where

  _×-⇔_ : A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
  _×-⇔_ A⇔B C⇔D =
    Inverse.equivalence Pointwise-≡↔≡           ⟨∘⟩
    (A⇔B ×-equivalence C⇔D)                     ⟨∘⟩
    Eq.sym (Inverse.equivalence Pointwise-≡↔≡)
    where open Eq using () renaming (_∘_ to _⟨∘⟩_)

  _×-↣_ : A ↣ B → C ↣ D → (A × C) ↣ (B × D)
  _×-↣_ A↣B C↣D =
    Inverse.injection Pointwise-≡↔≡           ⟨∘⟩
    (A↣B ×-injection C↣D)                     ⟨∘⟩
    Inverse.injection (Inv.sym Pointwise-≡↔≡)
    where open Inj using () renaming (_∘_ to _⟨∘⟩_)

  _×-↞_ : A ↞ B → C ↞ D → (A × C) ↞ (B × D)
  _×-↞_ A↞B C↞D =
    Inverse.left-inverse Pointwise-≡↔≡           ⟨∘⟩
    (A↞B ×-left-inverse C↞D)                     ⟨∘⟩
    Inverse.left-inverse (Inv.sym Pointwise-≡↔≡)
    where open LeftInv using () renaming (_∘_ to _⟨∘⟩_)

  _×-↠_ : A ↠ B → C ↠ D → (A × C) ↠ (B × D)
  _×-↠_ A↠B C↠D =
    Inverse.surjection Pointwise-≡↔≡           ⟨∘⟩
    (A↠B ×-surjection C↠D)                     ⟨∘⟩
    Inverse.surjection (Inv.sym Pointwise-≡↔≡)
    where open Surj using () renaming (_∘_ to _⟨∘⟩_)

  _×-↔_ : A ↔ B → C ↔ D → (A × C) ↔ (B × D)
  _×-↔_ A↔B C↔D =
    Pointwise-≡↔≡          ⟨∘⟩
    (A↔B ×-inverse C↔D)    ⟨∘⟩
    Inv.sym Pointwise-≡↔≡
    where open Inv using () renaming (_∘_ to _⟨∘⟩_)

module _ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} where

  _×-cong_ : ∀ {k} → A ∼[ k ] B → C ∼[ k ] D → (A × C) ∼[ k ] (B × D)
  _×-cong_ {implication}         = λ f g →      map        f         g
  _×-cong_ {reverse-implication} = λ f g → lam (map (app-← f) (app-← g))
  _×-cong_ {equivalence}         = _×-⇔_
  _×-cong_ {injection}           = _×-↣_
  _×-cong_ {reverse-injection}   = λ f g → lam (app-↢ f ×-↣ app-↢ g)
  _×-cong_ {left-inverse}        = _×-↞_
  _×-cong_ {surjection}          = _×-↠_
  _×-cong_ {bijection}           = _×-↔_
