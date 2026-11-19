------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the `Choice` construct
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Choice where

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
open import Relation.Nullary.Recomputable as Recomputable using (Recomputable)


open import Relation.Nullary.Orthogonal
  using (_⫫[_]_; negation; orthogonal; ∁; _∩_; _!∩_; _∪_; _⇒_)

private
  variable
    ℓa ℓaⁿ ℓb ℓbⁿ p q : Level
    A : Set ℓa
    ¬A : Set ℓaⁿ
    B : Set ℓb
    ¬B : Set ℓbⁿ
    P : Set p
    Q : Set q
    oA : A ⫫[ P ] ¬A
    oB : B ⫫[ P ] ¬B
    a b : Bool

------------------------------------------------------------------------
-- `Choice` idiom.

-- The choice between A and B is reflected by a boolean value.
-- `Choice A B b` is equivalent to `if b then A else B`.
-- `Choice A (¬ A) b` is equivalent to `Reflects A b`

data Choice
  (A : Set ℓa) (P : Set p) (B : Set ℓb)
  (oA : A ⫫[ P ] B) : Bool → Set (ℓa ⊔ p ⊔ ℓb) where
  ofʸ : (a : A) → Choice A P B oA true
  ofⁿ : (a : B) → Choice A P B oA false

Reflects : Set ℓa → Bool → Set ℓa
Reflects A = Choice A ⊥ (¬ A) (negation {A = A})

------------------------------------------------------------------------
-- Constructors and destructors

-- These lemmas are intended to be used mostly when `b` is a value, so
-- that the `if` expressions have already been evaluated away.
-- In this case, `of` works like the relevant constructor (`ofⁿ` or
-- `ofʸ`), and `invert` strips off the constructor to just give either
-- the proof of `A` or the proof of `B`.

of : ∀ {b} → if b then A else B → Choice A P B oA b
of {b = true } a = ofʸ a
of {b = false} b = ofⁿ b

invert : ∀ {b} → Choice A P B oA b → if b then A else B
invert (ofʸ a) = a
invert (ofⁿ b) = b

------------------------------------------------------------------------
-- Transformation

map : (A → B) → (¬A → ¬B) →
      Choice A P ¬A oA b → Choice B Q ¬B oB b
map f g (ofʸ a) = ofʸ (f a)
map f g (ofⁿ b) = ofⁿ (g b)

map₁ : (A → B) → Choice A P ¬A oA b → Choice B Q ¬A oB b
map₁ f = map f id

map₂ : (¬A → ¬B) → Choice A P ¬A oA b → Choice A Q ¬B oB b
map₂ = map id

------------------------------------------------------------------------
-- recompute

-- Given an irrelevant proof of a reflected type, a proof can
-- be recomputed and subsequently used in relevant contexts.

recompute : ∀ {b} → Choice A ⊥ B oA b → Recomputable A
recompute (ofʸ  a) _ = a
recompute {oA = oA} (ofⁿ b) a = ⊥-elim-irr (oA .orthogonal a b)

recompute-constant : ∀ {b} (r : Choice A ⊥ B oA b) (p q : A) →
                     recompute r p ≡ recompute r q
recompute-constant = Recomputable.recompute-constant ∘ recompute

------------------------------------------------------------------------
-- Interaction with true, false, negation, product, sums etc.

⊥ˡ-choice : Choice A P (¬ ⊥ˡ) oA false
⊥ˡ-choice = ofⁿ λ ()

⊥ˡ-reflects : Reflects (⊥ˡ {ℓa}) false
⊥ˡ-reflects = ⊥ˡ-choice

⊤ˡ-choice : Choice ⊤ˡ P B oA true
⊤ˡ-choice = ofʸ _

⊤ˡ-reflects : Reflects (⊤ˡ {ℓa}) true
⊤ˡ-reflects = ⊤ˡ-choice

⊥-choice : Choice A P (¬ ⊥) oA false
⊥-choice = ofⁿ λ ()

⊥-reflects : Reflects ⊥ false
⊥-reflects = ⊥-choice

⊤-choice : Choice ⊤ P B oA true
⊤-choice = ofʸ _

⊤-reflects : Reflects ⊤ true
⊤-reflects = ⊤-choice

∁-choice : ∀ {b} → Choice A P B oA b → Choice B P A (∁ oA) (not b)
∁-choice (ofʸ a) = ofⁿ a
∁-choice (ofⁿ b) = ofʸ b

¬-reflects : ∀ {b} → Reflects A b → Reflects (¬ A) (not b)
¬-reflects = map id ¬¬-η ∘′ ∁-choice

Truth-choice : ∀ b {oA} → Choice (T b) P (T (not b)) oA b
Truth-choice true  = ⊤-choice
Truth-choice false = ∁-choice ⊤-choice

-- This could also be implemented using map over Truth-choice
-- if only we had a conveniently accessible proof of
-- T (not b) → ¬ T b
T-reflects : ∀ b → Reflects (T b) b
T-reflects true  = ⊤-choice
T-reflects false = ⊥-choice

infixr 2 _×-choice_ _!×-choice_

_×-choice_ : Choice A P ¬A oA a → Choice B P ¬B oB b →
             Choice (A × B) P (¬A ⊎ ¬B) (oA ∩ oB) (a ∧ b)
ofʸ  a ×-choice ofʸ  b = ofʸ (a , b)
ofʸ  a ×-choice ofⁿ ¬b = ofⁿ (inj₂ ¬b)
ofⁿ ¬a ×-choice _      = ofⁿ (inj₁ ¬a)

_×-reflects_ : Reflects A a → Reflects B b → Reflects (A × B) (a ∧ b)
ra ×-reflects rb = map₂
  [ contraposition proj₁
  , contraposition proj₂
  ]′ (ra ×-choice rb)

_!×-choice_ : Choice A P ¬A oA a → Choice B P ¬B oB b →
              Choice (A × B) P (¬A ⊎ (A × ¬B)) (oA !∩ oB) (a ∧ b)
ofʸ  a !×-choice ofʸ  b = ofʸ (a , b)
ofʸ  a !×-choice ofⁿ ¬b = ofⁿ (inj₂ (a , ¬b))
ofⁿ ¬a !×-choice _      = ofⁿ (inj₁ ¬a)

_⊎-choice_ : Choice A P ¬A oA a → Choice B P ¬B oB b  →
             Choice (A ⊎ B) P (¬A × ¬B) (oA ∪ oB) (a ∨ b)
ofʸ  a ⊎-choice      _ = ofʸ (inj₁ a)
ofⁿ ¬a ⊎-choice ofʸ  b = ofʸ (inj₂ b)
ofⁿ ¬a ⊎-choice ofⁿ ¬b = ofⁿ (¬a , ¬b)

_→-choice_ : Choice A B ¬A oA a → Choice B P ¬B oB b →
             Choice (A → B) P (A × ¬B) (A ⇒ oB) (not a ∨ b)
ofʸ  a →-choice ofʸ  b = ofʸ (const b)
ofʸ  a →-choice ofⁿ ¬b = ofⁿ (a , ¬b)
_→-choice_ {oA = oA} (ofⁿ ¬a) _ = ofʸ (λ a → oA .orthogonal a ¬a)

------------------------------------------------------------------------
-- Other lemmas

fromEquivalence : ∀ {b} → (T b → A) → (A → T b) → Reflects A b
fromEquivalence {b = true}  sound complete = of (sound _)
fromEquivalence {b = false} sound complete = of complete

-- `Choice` is deterministic on orthogonal types.
det : ∀ {b b′} → Choice A ⊥ ¬A oA b → Choice A ⊥ ¬A oA b′ → b ≡ b′
det (ofʸ  a) (ofʸ  _) = refl
det {oA = oA} (ofʸ  a) (ofⁿ ¬a) = ⊥-elim (oA .orthogonal a ¬a)
det {oA = oA} (ofⁿ ¬a) (ofʸ  a) = ⊥-elim (oA .orthogonal a ¬a)
det (ofⁿ ¬a) (ofⁿ  _) = refl

T-reflects-elim : ∀ {a b} → Reflects (T a) b → b ≡ a
T-reflects-elim {a} r = det r (T-reflects a)
