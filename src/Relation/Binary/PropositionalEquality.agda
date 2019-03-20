------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional (intensional) equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality where

open import Function
open import Function.Equality using (Π; _⟶_; ≡-setoid)
open import Level
open import Data.Empty
open import Data.Product
open import Relation.Nullary using (yes ; no)
open import Relation.Unary using (Pred)
open import Axiom.UIP
open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
import Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
  as Trivial

------------------------------------------------------------------------
-- Re-export contents of core module

open import Relation.Binary.PropositionalEquality.Core public

------------------------------------------------------------------------
-- Some properties

subst₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p)
         {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂ P refl refl p = p

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

decSetoid : ∀ {a} {A : Set a} → Decidable {A = A} _≡_ → DecSetoid _ _
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
A →-setoid B = ≡-setoid A (Trivial.indexedSetoid (setoid B))

_≗_ : ∀ {a b} {A : Set a} {B : Set b} (f g : A → B) → Set _
_≗_ {A = A} {B} = Setoid._≈_ (A →-setoid B)

:→-to-Π : ∀ {a b₁ b₂} {A : Set a} {B : IndexedSetoid _ b₁ b₂} →
          ((x : A) → IndexedSetoid.Carrier B x) → Π (setoid A) B
:→-to-Π {B = B} f = record { _⟨$⟩_ = f; cong = cong′ }
  where
  open IndexedSetoid B using (_≈_)

  cong′ : ∀ {x y} → x ≡ y → f x ≈ f y
  cong′ refl = IndexedSetoid.refl B

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
-- Propositionality

isPropositional : ∀ {a} → Set a → Set a
isPropositional A = (a b : A) → a ≡ b


module _ {a} {A : Set a} {x y : A} where

------------------------------------------------------------------------
-- Various equality rearrangement lemmas

  trans-injectiveˡ : ∀ {z} {p₁ p₂ : x ≡ y} (q : y ≡ z) →
                     trans p₁ q ≡ trans p₂ q → p₁ ≡ p₂
  trans-injectiveˡ refl = subst₂ _≡_ (trans-reflʳ _) (trans-reflʳ _)

  trans-injectiveʳ : ∀ {z} (p : x ≡ y) {q₁ q₂ : y ≡ z} →
                     trans p q₁ ≡ trans p q₂ → q₁ ≡ q₂
  trans-injectiveʳ refl eq = eq

cong-id :
  ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) →
  cong id p ≡ p
cong-id refl = refl

cong-∘ :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {x y : A}
    {f : B → C} {g : A → B}
  (p : x ≡ y) →
  cong (f ∘ g) p ≡ cong f (cong g p)
cong-∘ refl = refl

module _ {a p} {A : Set a} {P : A → Set p} {x y : A} where

  subst-injective : ∀ (x≡y : x ≡ y) {p q : P x} →
    subst P x≡y p ≡ subst P x≡y q → p ≡ q
  subst-injective refl p≡q = p≡q

  subst-subst : ∀ {z} (x≡y : x ≡ y) {y≡z : y ≡ z} {p : P x} →
    subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
  subst-subst refl = refl

  subst-subst-sym : (x≡y : x ≡ y) {p : P y} →
    subst P x≡y (subst P (sym x≡y) p) ≡ p
  subst-subst-sym refl = refl

  subst-sym-subst : (x≡y : x ≡ y) {p : P x} →
    subst P (sym x≡y) (subst P x≡y p) ≡ p
  subst-sym-subst refl = refl

subst-∘ :
  ∀ {a b p} {A : Set a} {B : Set b} {x y : A} {P : B → Set p}
    {f : A → B}
  (x≡y : x ≡ y) {p : P (f x)} →
  subst (P ∘ f) x≡y p ≡ subst P (cong f x≡y) p
subst-∘ refl = refl

subst-application :
  ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
    (B₁ : A₁ → Set b₁) {B₂ : A₂ → Set b₂}
    {f : A₂ → A₁} {x₁ x₂ : A₂} {y : B₁ (f x₁)}
  (g : ∀ x → B₁ (f x) → B₂ x) (eq : x₁ ≡ x₂) →
  subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ (cong f eq) y)
subst-application _ _ refl = refl

-- A lemma that is very similar to Lemma 2.4.3 from the HoTT book.

naturality :
  ∀ {a b} {A : Set a} {B : Set b} {x y} {x≡y : x ≡ y} {f g : A → B}
  (f≡g : ∀ x → f x ≡ g x) →
  trans (cong f x≡y) (f≡g y) ≡ trans (f≡g x) (cong g x≡y)
naturality {x = x} {x≡y = refl} f≡g =
  f≡g x               ≡⟨ sym (trans-reflʳ _) ⟩
  trans (f≡g x) refl  ∎
  where
  open ≡-Reasoning

-- A lemma that is very similar to Corollary 2.4.4 from the HoTT book.

cong-≡id :
  ∀ {a} {A : Set a} {f : A → A} {x : A}
  (f≡id : ∀ x → f x ≡ x) →
  cong f (f≡id x) ≡ f≡id (f x)
cong-≡id {f = f} {x} f≡id =
  cong f (f≡id x)                                               ≡⟨ sym (trans-reflʳ _) ⟩
  trans (cong f (f≡id x)) refl                                  ≡⟨ cong (trans _) (sym (trans-symʳ (f≡id x))) ⟩
  trans (cong f (f≡id x)) (trans (f≡id x) (sym (f≡id x)))       ≡⟨ sym (trans-assoc (cong f (f≡id x))) ⟩
  trans (trans (cong f (f≡id x)) (f≡id x)) (sym (f≡id x))       ≡⟨ cong (λ p → trans p (sym _)) (naturality f≡id) ⟩
  trans (trans (f≡id (f x)) (cong id (f≡id x))) (sym (f≡id x))  ≡⟨ cong (λ p → trans (trans (f≡id (f x)) p) (sym (f≡id x))) (cong-id _) ⟩
  trans (trans (f≡id (f x)) (f≡id x)) (sym (f≡id x))            ≡⟨ trans-assoc (f≡id (f x)) ⟩
  trans (f≡id (f x)) (trans (f≡id x) (sym (f≡id x)))            ≡⟨ cong (trans _) (trans-symʳ (f≡id x)) ⟩
  trans (f≡id (f x)) refl                                       ≡⟨ trans-reflʳ _ ⟩
  f≡id (f x)                                                    ∎
  where
  open ≡-Reasoning

module _ {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) {a : A} where

  ≡-≟-identity : ∀ {b} (eq : a ≡ b) → a ≟ b ≡ yes eq
  ≡-≟-identity {b} eq with a ≟ b
  ... | yes p = cong yes (Decidable⇒UIP.≡-irrelevant _≟_ p eq)
  ... | no ¬p = ⊥-elim (¬p eq)

  ≢-≟-identity : ∀ {b} → a ≢ b → ∃ λ ¬eq → a ≟ b ≡ no ¬eq
  ≢-≟-identity {b} ¬eq with a ≟ b
  ... | yes p = ⊥-elim (¬eq p)
  ... | no ¬p = ¬p , refl
