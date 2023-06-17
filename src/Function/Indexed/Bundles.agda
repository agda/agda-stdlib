------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on Relations for Indexed sets
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Indexed.Bundles where

open import Relation.Unary using (Pred)
open import Function.Bundles using (_⟶_; _↣_; _↠_; _⤖_; _⇔_; _↩_; _↪_; _↩↪_; _↔_)
open import Relation.Binary hiding (_⇔_)
open import Level using (Level)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Bundles specialised for lifting relations to indexed sets
------------------------------------------------------------------------

infix 3 _⟶ᵢ_ _↣ᵢ_ _↠ᵢ_ _⤖ᵢ_ _⇔ᵢ_ _↩ᵢ_ _↪ᵢ_ _↩↪ᵢ_ _↔ᵢ_
_⟶ᵢ_ : ∀ {i} {I : Set i} → Pred I a → Pred I b → Set _
A ⟶ᵢ B = ∀ {i} → A i ⟶ B i

_↣ᵢ_ : ∀ {i} {I : Set i} → Pred I a → Pred I b → Set _
A ↣ᵢ B = ∀ {i} → A i ↣ B i

_↠ᵢ_ : ∀ {i} {I : Set i} → Pred I a → Pred I b → Set _
A ↠ᵢ B = ∀ {i} → A i ↠ B i

_⤖ᵢ_ : ∀ {i} {I : Set i} → Pred I a → Pred I b → Set _
A ⤖ᵢ B = ∀ {i} → A i ⤖ B i

_⇔ᵢ_ : ∀ {i} {I : Set i} → Pred I a → Pred I b → Set _
A ⇔ᵢ B = ∀ {i} → A i ⇔ B i

_↩ᵢ_ : ∀ {i} {I : Set i} → Pred I a → Pred I b → Set _
A ↩ᵢ B = ∀ {i} → A i ↩ B i

_↪ᵢ_ : ∀ {i} {I : Set i} → Pred I a → Pred I b → Set _
A ↪ᵢ B = ∀ {i} → A i ↪ B i

_↩↪ᵢ_ : ∀ {i} {I : Set i} → Pred I a → Pred I b → Set _
A ↩↪ᵢ B = ∀ {i} → A i ↩↪ B i

_↔ᵢ_ : ∀ {i} {I : Set i} → Pred I a → Pred I b → Set _
A ↔ᵢ B = ∀ {i} → A i ↔ B i
