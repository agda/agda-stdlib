------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed containers core
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Container.Indexed.Core where

open import Level
open import Data.Product.Base using (Σ; Σ-syntax; _,_; ∃)
open import Relation.Unary

private variable
  i o c r ℓ ℓ′ : Level
  I : Set i
  O : Set o

------------------------------------------------------------------------
-- Definition

infix 5 _◃_/_

record Container (I : Set i) (O : Set o) c r : Set (i ⊔ o ⊔ suc c ⊔ suc r) where
  constructor _◃_/_
  field
    Command  : (o : O) → Set c
    Response : ∀ {o} → Command o → Set r
    next     : ∀ {o} (c : Command o) → Response c → I

------------------------------------------------------------------------
-- The semantics ("extension") of an indexed container.

module _ (C : Container I O c r) (X : Pred I ℓ) where
  open Container C

  Subtrees : ∀ o → Command o → Set _
  Subtrees o c = (r : Response c) → X (next c r)

  ⟦_⟧ : Pred O _
  ⟦_⟧ o = Σ (Command o) (Subtrees o)

------------------------------------------------------------------------
-- All and any

module _ (C : Container I O c r) {X : Pred I ℓ} where

  -- All.

  □ : Pred (Σ I X) ℓ′ → Pred (Σ O (⟦ C ⟧ X)) _
  □ P (_ , _ , k) = ∀ r → P (_ , k r)

  -- Any.

  ◇ : Pred (Σ I X) ℓ′ → Pred (Σ O (⟦ C ⟧ X)) _
  ◇ P (_ , _ , k) = ∃ λ r → P (_ , k r)
