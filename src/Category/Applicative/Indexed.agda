------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed applicative functors
------------------------------------------------------------------------

-- Note that currently the applicative functor laws are not included
-- here.

{-# OPTIONS --without-K --safe #-}

module Category.Applicative.Indexed where

open import Category.Functor using (RawFunctor)
open import Data.Product using (_×_; _,_)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private
  variable
    a b c i f : Level
    A : Set a
    B : Set b
    C : Set c

IFun : Set i → (ℓ : Level) → Set (i ⊔ suc ℓ)
IFun I ℓ = I → I → Set ℓ → Set ℓ

------------------------------------------------------------------------
-- Type, and usual combinators

record RawIApplicative {I : Set i} (F : IFun I f) :
                       Set (i ⊔ suc f) where
  infixl 4 _⊛_ _<⊛_ _⊛>_
  infix  4 _⊗_

  field
    pure : ∀ {i} → A → F i i A
    _⊛_  : ∀ {i j k} → F i j (A → B) → F j k A → F i k B

  rawFunctor : ∀ {i j} → RawFunctor (F i j)
  rawFunctor = record
    { _<$>_ = λ g x → pure g ⊛ x
    }

  private
    open module RF {i j : I} =
           RawFunctor (rawFunctor {i = i} {j = j})
           public

  _<⊛_ : ∀ {i j k} → F i j A → F j k B → F i k A
  x <⊛ y = const <$> x ⊛ y

  _⊛>_ : ∀ {i j k} → F i j A → F j k B → F i k B
  x ⊛> y = flip const <$> x ⊛ y

  _⊗_ : ∀ {i j k} → F i j A → F j k B → F i k (A × B)
  x ⊗ y = (_,_) <$> x ⊛ y

  zipWith : ∀ {i j k} → (A → B → C) → F i j A → F j k B → F i k C
  zipWith f x y = f <$> x ⊛ y

  zip : ∀ {i j k} → F i j A → F j k B → F i k (A × B)
  zip = zipWith _,_

------------------------------------------------------------------------
-- Applicative with a zero

record RawIApplicativeZero
       {I : Set i} (F : IFun I f) :
       Set (i ⊔ suc f) where
  field
    applicative : RawIApplicative F
    ∅           : ∀ {i j} → F i j A

  open RawIApplicative applicative public

------------------------------------------------------------------------
-- Alternative functors: `F i j A` is a monoid

record RawIAlternative
       {I : Set i} (F : IFun I f) :
       Set (i ⊔ suc f) where
  infixr 3 _∣_
  field
    applicativeZero : RawIApplicativeZero F
    _∣_             : ∀ {i j} → F i j A → F i j A → F i j A

  open RawIApplicativeZero applicativeZero public


------------------------------------------------------------------------
-- Applicative functor morphisms, specialised to propositional
-- equality.

record Morphism {I : Set i} {F₁ F₂ : IFun I f}
                (A₁ : RawIApplicative F₁)
                (A₂ : RawIApplicative F₂) : Set (i ⊔ suc f) where
  module A₁ = RawIApplicative A₁
  module A₂ = RawIApplicative A₂
  field
    op      : ∀ {i j} → F₁ i j A → F₂ i j A
    op-pure : ∀ {i} (x : A) → op (A₁.pure {i = i} x) ≡ A₂.pure x
    op-⊛    : ∀ {i j k} (f : F₁ i j (A → B)) (x : F₁ j k A) →
              op (f A₁.⊛ x) ≡ (op f A₂.⊛ op x)

  op-<$> : ∀ {i j} (f : A → B) (x : F₁ i j A) →
           op (f A₁.<$> x) ≡ (f A₂.<$> op x)
  op-<$> f x = begin
    op (A₁._⊛_ (A₁.pure f) x)       ≡⟨ op-⊛ _ _ ⟩
    A₂._⊛_ (op (A₁.pure f)) (op x)  ≡⟨ P.cong₂ A₂._⊛_ (op-pure _) P.refl ⟩
    A₂._⊛_ (A₂.pure f) (op x)       ∎
    where open P.≡-Reasoning
