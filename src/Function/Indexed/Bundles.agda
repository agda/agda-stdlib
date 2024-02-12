------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on Relations for Indexed sets
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Indexed.Bundles where

open import Relation.Unary using (Pred)
open import Function.Bundles using (_⟶_; _↣_; _↠_; _⤖_; _⇔_; _↩_; _↪_; _↩↪_; _↔_)
open import Relation.Binary.Core hiding (_⇔_)
open import Level using (Level)

private
  variable
    a b i : Level
    I : Set i

------------------------------------------------------------------------
-- Bundles specialised for lifting relations to indexed sets
------------------------------------------------------------------------

infix 3 _⟶ᵢ_ _↣ᵢ_ _↠ᵢ_ _⤖ᵢ_ _⇔ᵢ_ _↩ᵢ_ _↪ᵢ_ _↩↪ᵢ_ _↔ᵢ_

_⟶ᵢ_ : Pred I a → Pred I b → Set _
A ⟶ᵢ B = ∀ {i} → A i ⟶ B i

_↣ᵢ_ : Pred I a → Pred I b → Set _
A ↣ᵢ B = ∀ {i} → A i ↣ B i

_↠ᵢ_ : Pred I a → Pred I b → Set _
A ↠ᵢ B = ∀ {i} → A i ↠ B i

_⤖ᵢ_ : Pred I a → Pred I b → Set _
A ⤖ᵢ B = ∀ {i} → A i ⤖ B i

_⇔ᵢ_ : Pred I a → Pred I b → Set _
A ⇔ᵢ B = ∀ {i} → A i ⇔ B i

_↩ᵢ_ : Pred I a → Pred I b → Set _
A ↩ᵢ B = ∀ {i} → A i ↩ B i

_↪ᵢ_ : Pred I a → Pred I b → Set _
A ↪ᵢ B = ∀ {i} → A i ↪ B i

_↩↪ᵢ_ : Pred I a → Pred I b → Set _
A ↩↪ᵢ B = ∀ {i} → A i ↩↪ B i

_↔ᵢ_ : Pred I a → Pred I b → Set _
A ↔ᵢ B = ∀ {i} → A i ↔ B i
