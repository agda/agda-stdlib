------------------------------------------------------------------------
-- The Agda standard library
--
-- Initial objects
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Category
open import Category.Structures using (module Endo)

module Category.InitialObject {o m r} (cat : RawCategory o m r) where

open Endo cat
open RawCategory cat

record RawInitial : Set (o ⊔ m) where
  field
    ⊥ : Obj
    ! : ∀ X → ⊥ ⇒ X

record Initial : Set (o ⊔ m ⊔ r) where
  field
    ⊥ : Obj
    ! : ∀ X → ⊥ ⇒ X
    isInitial : IsInitial ⊥ !

  open IsInitial isInitial public

  rawInitial : RawInitial
  rawInitial = record { ! = ! }
