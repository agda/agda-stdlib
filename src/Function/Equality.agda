------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Equality where

{-# WARNING_ON_IMPORT
"Function.Equality was deprecated in v2.0.
Use the standard function hierarchy in Function/Function.Bundles instead."
#-}

import Function.Base as Fun
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid; _=[_]⇒_)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
  as Trivial
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.PropositionalEquality.Properties as ≡

------------------------------------------------------------------------
-- Functions which preserve equality

record Π {f₁ f₂ t₁ t₂}
         (From : Setoid f₁ f₂)
         (To : IndexedSetoid (Setoid.Carrier From) t₁ t₂) :
         Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : (x : Setoid.Carrier From) → IndexedSetoid.Carrier To x
    cong  : Setoid._≈_ From =[ _⟨$⟩_ ]⇒ IndexedSetoid._≈_ To
{-# WARNING_ON_USAGE Π
"Warning: Π was deprecated in v2.0.
Please use Function.Dependent.Bundles.Func instead."
#-}

open Π public

infixr 0 _⟶_

_⟶_ : ∀ {f₁ f₂ t₁ t₂} → Setoid f₁ f₂ → Setoid t₁ t₂ → Set _
From ⟶ To = Π From (Trivial.indexedSetoid To)
{-# WARNING_ON_USAGE _⟶_
"Warning: _⟶_ was deprecated in v2.0.
Please use Function.(Bundles.)Func instead."
#-}

------------------------------------------------------------------------
-- Identity and composition.

id : ∀ {a₁ a₂} {A : Setoid a₁ a₂} → A ⟶ A
id = record { _⟨$⟩_ = Fun.id; cong = Fun.id }
{-# WARNING_ON_USAGE id
"Warning: id was deprecated in v2.0.
Please use Function.Construct.Identity.function instead."
#-}

infixr 9 _∘_

_∘_ : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
        {b₁ b₂} {B : Setoid b₁ b₂}
        {c₁ c₂} {C : Setoid c₁ c₂} →
      B ⟶ C → A ⟶ B → A ⟶ C
f ∘ g = record
  { _⟨$⟩_ = Fun._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
  ; cong  = Fun._∘_ (cong  f) (cong  g)
  }
{-# WARNING_ON_USAGE _∘_
"Warning: _∘_ was deprecated in v2.0.
Please use Function.Construct.Composition.function instead."
#-}

-- Constant equality-preserving function.

const : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
          {b₁ b₂} {B : Setoid b₁ b₂} →
        Setoid.Carrier B → A ⟶ B
const {B = B} b = record
  { _⟨$⟩_ = Fun.const b
  ; cong  = Fun.const (Setoid.refl B)
  }
{-# WARNING_ON_USAGE const
"Warning: const was deprecated in v2.0.
Please use Function.Construct.Constant.function instead."
#-}

------------------------------------------------------------------------
-- Function setoids

-- Dependent.

setoid : ∀ {f₁ f₂ t₁ t₂}
         (From : Setoid f₁ f₂) →
         IndexedSetoid (Setoid.Carrier From) t₁ t₂ →
         Setoid _ _
setoid From To = record
  { Carrier       = Π From To
  ; _≈_           = λ f g → ∀ {x y} → x ≈₁ y → f ⟨$⟩ x ≈₂ g ⟨$⟩ y
  ; isEquivalence = record
    { refl  = λ {f} → cong f
    ; sym   = λ f∼g x∼y → To.sym (f∼g (From.sym x∼y))
    ; trans = λ f∼g g∼h x∼y → To.trans (f∼g From.refl) (g∼h x∼y)
    }
  }
  where
  open module From = Setoid From using () renaming (_≈_ to _≈₁_)
  open module To = IndexedSetoid To   using () renaming (_≈_ to _≈₂_)

-- Non-dependent.

infixr 0 _⇨_

_⇨_ : ∀ {f₁ f₂ t₁ t₂} → Setoid f₁ f₂ → Setoid t₁ t₂ → Setoid _ _
From ⇨ To = setoid From (Trivial.indexedSetoid To)

-- A variant of setoid which uses the propositional equality setoid
-- for the domain, and a more convenient definition of _≈_.

≡-setoid : ∀ {f t₁ t₂} (From : Set f) → IndexedSetoid From t₁ t₂ → Setoid _ _
≡-setoid From To = record
  { Carrier       = (x : From) → Carrier x
  ; _≈_           = λ f g → ∀ x → f x ≈ g x
  ; isEquivalence = record
    { refl  = λ {f} x → refl
    ; sym   = λ f∼g x → sym (f∼g x)
    ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
    }
  } where open IndexedSetoid To

-- Parameter swapping function.

flip : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
         {b₁ b₂} {B : Setoid b₁ b₂}
         {c₁ c₂} {C : Setoid c₁ c₂} →
       A ⟶ B ⇨ C → B ⟶ A ⇨ C
flip {B = B} f = record
  { _⟨$⟩_ = λ b → record
    { _⟨$⟩_ = λ a → f ⟨$⟩ a ⟨$⟩ b
    ; cong  = λ a₁≈a₂ → cong f a₁≈a₂ (Setoid.refl B) }
  ; cong  = λ b₁≈b₂ a₁≈a₂ → cong f a₁≈a₂ b₁≈b₂
  }

→-to-⟶ : ∀ {a b ℓ} {A : Set a} {B : Setoid b ℓ} →
         (A → Setoid.Carrier B) → ≡.setoid A ⟶ B
→-to-⟶ {B = B} to = record
  { _⟨$⟩_ = to
  ; cong = λ { ≡.refl → Setoid.refl B }
  }
