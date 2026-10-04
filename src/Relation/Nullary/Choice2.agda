------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the `Choice` construct
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Choice2 where

open import Agda.Builtin.Equality

open import Data.Bool.Base using (Bool; T; true; false; not; if_then_else_; _∧_; _∨_)

open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Empty.Polymorphic using () renaming (⊥ to ⊥ˡ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Base using (⊤)
open import Data.Unit.Polymorphic.Base using () renaming (⊤ to ⊤ˡ)

open import Level using (Level; _⊔_)

open import Function.Base using (_$_; _∘′_; _∘_; const; id)

open import Relation.Nullary.Negation.Core
  using (¬_; contraposition; contradiction-irr; contradiction; _¬-⊎_; ¬¬-η)
open import Relation.Nullary.Recomputable as Recomputable using (Recomputable; ⊥-recompute)


open import Relation.Nullary.Orthogonal
  using (_⫫[_]_; byOrthogonality)

private
  variable
    ℓa ℓaⁿ ℓb ℓbⁿ : Level
    A : Set ℓa
    ¬A : Set ℓaⁿ
    B : Set ℓb
    ¬B : Set ℓbⁿ
    a b : Bool

------------------------------------------------------------------------
-- `Choice` idiom.

-- The choice between A and B is reflected by a boolean value.
-- `Choice A B b` is equivalent to `if b then A else B`.
-- `Choice A (¬ A) b` is equivalent to `Reflects A b`

data Choice (A : Set ℓa) (B : Set ℓb) : Bool → Set (ℓa ⊔ ℓb) where
  ofʸ : (a : A) → Choice A B true
  ofⁿ : (a : B) → Choice A B false

Reflects : Set ℓa → Bool → Set ℓa
Reflects A = Choice A (¬ A)

------------------------------------------------------------------------
-- Constructors and destructors

-- These lemmas are intended to be used mostly when `b` is a value, so
-- that the `if` expressions have already been evaluated away.
-- In this case, `of` works like the relevant constructor (`ofⁿ` or
-- `ofʸ`), and `invert` strips off the constructor to just give either
-- the proof of `A` or the proof of `B`.

of : ∀ {b} → if b then A else B → Choice A B b
of {b = true } a = ofʸ a
of {b = false} b = ofⁿ b

invert : ∀ {b} → Choice A B b → if b then A else B
invert (ofʸ a) = a
invert (ofⁿ b) = b

------------------------------------------------------------------------
-- Transformation

map : (A → B) → (¬A → ¬B) → Choice A ¬A b → Choice B ¬B b
map f g (ofʸ a) = ofʸ (f a)
map f g (ofⁿ b) = ofⁿ (g b)

map₁ : (A → B) → Choice A ¬A b → Choice B ¬A b
map₁ f = map f id

map₂ : (¬A → ¬B) → Choice A ¬A b → Choice A ¬B b
map₂ = map id

------------------------------------------------------------------------
-- recompute

-- Given an irrelevant proof of a reflected type, a proof can
-- be recomputed and subsequently used in relevant contexts.

recompute : {{oA : A ⫫[ ⊥ ] B}} → Choice A B b → Recomputable A
recompute (ofʸ a) _ = a
recompute (ofⁿ b) a = ⊥-elim-irr (byOrthogonality a b)

recompute-constant :
  {{oA : A ⫫[ ⊥ ] B}} (r : Choice A B b) (p q : A) →
  recompute r p ≡ recompute r q
recompute-constant = Recomputable.recompute-constant ∘ recompute

------------------------------------------------------------------------
-- Interaction with true, false, negation, product, sums etc.

⊥ˡ-choice : Choice A (¬ (⊥ˡ {ℓb})) false
⊥ˡ-choice = ofⁿ λ ()

⊥ˡ-reflects : Reflects (⊥ˡ {ℓa}) false
⊥ˡ-reflects = ⊥ˡ-choice

⊤ˡ-choice : Choice (⊤ˡ {ℓa}) B true
⊤ˡ-choice = ofʸ _

⊤ˡ-reflects : Reflects (⊤ˡ {ℓa}) true
⊤ˡ-reflects = ⊤ˡ-choice

⊥-choice : Choice A (¬ ⊥) false
⊥-choice = ofⁿ λ ()

⊥-reflects : Reflects ⊥ false
⊥-reflects = ⊥-choice

⊤-choice : Choice ⊤ B true
⊤-choice = ofʸ _

⊤-reflects : Reflects ⊤ true
⊤-reflects = ⊤-choice

∁-choice : Choice A B b → Choice B A (not b)
∁-choice (ofʸ a) = ofⁿ a
∁-choice (ofⁿ b) = ofʸ b

¬-reflects : ∀ {b} → Reflects A b → Reflects (¬ A) (not b)
¬-reflects = map id ¬¬-η ∘′ ∁-choice

T-choice : (b : Bool) → Choice (T b) (T (not b)) b
T-choice true  = ⊤-choice
T-choice false = ∁-choice ⊤-choice

-- This could also be implemented using map over T-choice
-- if only we had a conveniently accessible proof of
-- T (not b) → ¬ T b
T-reflects : ∀ b → Reflects (T b) b
T-reflects true  = ⊤-choice
T-reflects false = ⊥-choice

infixr 2 _×-choice_ _!×-choice_

_×-choice_ : Choice A ¬A a → Choice B ¬B b →
             Choice (A × B) (¬A ⊎ ¬B) (a ∧ b)
ofʸ  a ×-choice ofʸ  b = ofʸ (a , b)
ofʸ  a ×-choice ofⁿ ¬b = ofⁿ (inj₂ ¬b)
ofⁿ ¬a ×-choice _      = ofⁿ (inj₁ ¬a)

_×-reflects_ : Reflects A a → Reflects B b → Reflects (A × B) (a ∧ b)
ra ×-reflects rb = map₂
  [ contraposition proj₁
  , contraposition proj₂
  ]′ (ra ×-choice rb)

_!×-choice_ : Choice A ¬A a → Choice B ¬B b →
              Choice (A × B) (¬A ⊎ (A × ¬B)) (a ∧ b)
ofʸ  a !×-choice ofʸ  b = ofʸ (a , b)
ofʸ  a !×-choice ofⁿ ¬b = ofⁿ (inj₂ (a , ¬b))
ofⁿ ¬a !×-choice _      = ofⁿ (inj₁ ¬a)

_⊎-choice_ : Choice A ¬A a → Choice B ¬B b  →
             Choice (A ⊎ B) (¬A × ¬B) (a ∨ b)
ofʸ  a ⊎-choice      _ = ofʸ (inj₁ a)
ofⁿ ¬a ⊎-choice ofʸ  b = ofʸ (inj₂ b)
ofⁿ ¬a ⊎-choice ofⁿ ¬b = ofⁿ (¬a , ¬b)

_→-choice_ :
  {{oA : A ⫫[ ⊥ ] ¬A}} →
  Choice A ¬A a → Choice B ¬B b →
  Choice (A → B) (A × ¬B) (not a ∨ b)
ofʸ  a →-choice ofʸ  b = ofʸ (const b)
ofʸ  a →-choice ofⁿ ¬b = ofⁿ (a , ¬b)
ofⁿ ¬a →-choice _      = ofʸ (λ a → byOrthogonality a ¬a)

------------------------------------------------------------------------
-- Other lemmas

fromEquivalence : ∀ {b} → (T b → A) → (A → T b) → Reflects A b
fromEquivalence {b = true}  sound complete = of (sound _)
fromEquivalence {b = false} sound complete = of complete

-- `Choice` is deterministic on orthogonal types.
det : {{oA : A ⫫[ ⊥ ] ¬A}} → Choice A ¬A a → Choice A ¬A b → a ≡ b
det (ofʸ  a) (ofʸ  _) = refl
det (ofʸ  a) (ofⁿ ¬a) = byOrthogonality a ¬a
det (ofⁿ ¬a) (ofʸ  a) = byOrthogonality a ¬a
det (ofⁿ ¬a) (ofⁿ  _) = refl

T-reflects-elim : Reflects (T a) b → b ≡ a
T-reflects-elim {a} r = det r (T-reflects a)
