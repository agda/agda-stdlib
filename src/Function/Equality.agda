------------------------------------------------------------------------
-- The Agda standard library
--
-- Function setoids and related constructions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Equality where

import Function as Fun
open import Level
open import Relation.Binary using (Setoid)
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid; _=[_]⇒_)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
  as Trivial

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

open Π public

infixr 0 _⟶_

_⟶_ : ∀ {f₁ f₂ t₁ t₂} → Setoid f₁ f₂ → Setoid t₁ t₂ → Set _
From ⟶ To = Π From (Trivial.indexedSetoid To)

------------------------------------------------------------------------
-- Identity and composition.

id : ∀ {a₁ a₂} {A : Setoid a₁ a₂} → A ⟶ A
id = record { _⟨$⟩_ = Fun.id; cong = Fun.id }

infixr 9 _∘_

_∘_ : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
        {b₁ b₂} {B : Setoid b₁ b₂}
        {c₁ c₂} {C : Setoid c₁ c₂} →
      B ⟶ C → A ⟶ B → A ⟶ C
f ∘ g = record
  { _⟨$⟩_ = Fun._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
  ; cong  = Fun._∘_ (cong  f) (cong  g)
  }

-- Constant equality-preserving function.

const : ∀ {a₁ a₂} {A : Setoid a₁ a₂}
          {b₁ b₂} {B : Setoid b₁ b₂} →
        Setoid.Carrier B → A ⟶ B
const {B = B} b = record
  { _⟨$⟩_ = Fun.const b
  ; cong  = Fun.const (Setoid.refl B)
  }

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
