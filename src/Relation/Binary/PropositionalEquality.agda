------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional (intensional) equality
------------------------------------------------------------------------

module Relation.Binary.PropositionalEquality where

open import Function
open import Function.Equality using (Π; _⟶_; ≡-setoid)
open import Level
open import Data.Empty
open import Data.Product
open import Relation.Nullary using (yes ; no)
open import Relation.Unary using (Pred)
open import Relation.Binary
import Relation.Binary.Indexed as I
open import Relation.Binary.HeterogeneousEquality.Core as H using (_≅_)

-- Some of the definitions can be found in the following modules:

open import Relation.Binary.Core public using (_≡_; refl; _≢_)
open import Relation.Binary.PropositionalEquality.Core public

------------------------------------------------------------------------
-- Some properties

subst₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p)
         {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P refl refl p = p

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

cong-app : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
           f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

setoid : ∀ {a} → Set a → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = isEquivalence
  }

decSetoid : ∀ {a} {A : Set a} → Decidable (_≡_ {A = A}) → DecSetoid _ _
decSetoid dec = record
  { _≈_              = _≡_
  ; isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = dec
      }
  }

isPreorder : ∀ {a} {A : Set a} → IsPreorder {A = A} _≡_ _≡_
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  }

preorder : ∀ {a} → Set a → Preorder _ _ _
preorder A = record
  { Carrier    = A
  ; _≈_        = _≡_
  ; _∼_        = _≡_
  ; isPreorder = isPreorder
  }

------------------------------------------------------------------------
-- Pointwise equality

infix 4 _≗_

_→-setoid_ : ∀ {a b} (A : Set a) (B : Set b) → Setoid _ _
A →-setoid B = ≡-setoid A (Setoid.indexedSetoid (setoid B))

_≗_ : ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) → Set _
_≗_ {A = A} {B} = Setoid._≈_ (A →-setoid B)

:→-to-Π : ∀ {a b₁ b₂} {A : Set a} {B : I.Setoid _ b₁ b₂} →
          ((x : A) → I.Setoid.Carrier B x) → Π (setoid A) B
:→-to-Π {B = B} f = record { _⟨$⟩_ = f; cong = cong′ }
  where
  open I.Setoid B using (_≈_)

  cong′ : ∀ {x y} → x ≡ y → f x ≈ f y
  cong′ refl = I.Setoid.refl B

→-to-⟶ : ∀ {a b₁ b₂} {A : Set a} {B : Setoid b₁ b₂} →
         (A → Setoid.Carrier B) → setoid A ⟶ B
→-to-⟶ = :→-to-Π

------------------------------------------------------------------------
-- Inspect

-- Inspect can be used when you want to pattern match on the result r
-- of some expression e, and you also need to "remember" that r ≡ e.

record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

-- Example usage:

-- f x y with g x | inspect g x
-- f x y | c z | [ eq ] = ...

------------------------------------------------------------------------
-- Convenient syntax for equational reasoning

-- This is special instance of Relation.Binary.EqReasoning.
-- Rather than instantiating the latter with (setoid A),
-- we reimplement equation chains from scratch
-- since then goals are printed much more readably.

module ≡-Reasoning {a} {A : Set a} where

  infix  3 _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≅⟨_⟩_
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _≅⟨_⟩_ : ∀ (x {y z} : A) → x ≅ y → y ≡ z → x ≡ z
  _ ≅⟨ x≅y ⟩ y≡z = trans (H.≅-to-≡ x≅y) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl

------------------------------------------------------------------------
-- Functional extensionality

-- If _≡_ were extensional, then the following statement could be
-- proved.

Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g

-- If extensionality holds for a given universe level, then it also
-- holds for lower ones.

extensionality-for-lower-levels :
  ∀ {a₁ b₁} a₂ b₂ →
  Extensionality (a₁ ⊔ a₂) (b₁ ⊔ b₂) → Extensionality a₁ b₁
extensionality-for-lower-levels a₂ b₂ ext f≡g =
  cong (λ h → lower ∘ h ∘ lift) $
    ext (cong (lift {ℓ = b₂}) ∘ f≡g ∘ lower {ℓ = a₂})

-- Functional extensionality implies a form of extensionality for
-- Π-types.

∀-extensionality :
  ∀ {a b} →
  Extensionality a (suc b) →
  {A : Set a} (B₁ B₂ : A → Set b) →
  (∀ x → B₁ x ≡ B₂ x) → (∀ x → B₁ x) ≡ (∀ x → B₂ x)
∀-extensionality ext B₁ B₂ B₁≡B₂ with ext B₁≡B₂
∀-extensionality ext B .B  B₁≡B₂ | refl = refl

------------------------------------------------------------------------
-- Proof irrelevance

isPropositional : ∀ {a} → Set a → Set a
isPropositional A = (a b : A) → a ≡ b

≡-irrelevance : ∀ {a} {A : Set a} → Irrelevant (_≡_ {A = A})
≡-irrelevance refl refl = refl

module _ {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) {a b : A} where

  ≡-≟-identity : (eq : a ≡ b) → a ≟ b ≡ yes eq
  ≡-≟-identity eq with a ≟ b
  ... | yes p = cong yes (≡-irrelevance p eq)
  ... | no ¬p = ⊥-elim (¬p eq)

  ≢-≟-identity : a ≢ b → ∃ λ ¬eq → a ≟ b ≡ no ¬eq
  ≢-≟-identity ¬eq with a ≟ b
  ... | yes p = ⊥-elim (¬eq p)
  ... | no ¬p = ¬p , refl

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

proof-irrelevance = ≡-irrelevance
