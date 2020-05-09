------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

{-# OPTIONS --without-K --safe #-}

module Category.Monad.Indexed where

open import Category.Applicative.Indexed
open import Function
open import Level

private
  variable
    a b c i f : Level
    A : Set a
    B : Set b
    C : Set c
    I : Set i

record RawIMonad {I : Set i} (M : IFun I f) : Set (i ⊔ suc f) where
  infixl 1 _>>=_ _>>_ _>=>_
  infixr 1 _=<<_ _<=<_

  field
    return : ∀ {i} → A → M i i A
    _>>=_  : ∀ {i j k} → M i j A → (A → M j k B) → M i k B

  _>>_ : ∀ {i j k} → M i j A → M j k B → M i k B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : ∀ {i j k} → (A → M j k B) → M i j A → M i k B
  f =<< c = c >>= f

  _>=>_ : ∀ {i j k} → (A → M i j B) → (B → M j k C) → (A → M i k C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : ∀ {i j k} → (B → M j k C) → (A → M i j B) → (A → M i k C)
  g <=< f = f >=> g

  join : ∀ {i j k} → M i j (M j k A) → M i k A
  join m = m >>= id

  rawIApplicative : RawIApplicative M
  rawIApplicative = record
    { pure = return
    ; _⊛_  = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
    }

  open RawIApplicative rawIApplicative public

RawIMonadT : {I : Set i} (T : IFun I f → IFun I f) → Set (i ⊔ suc f)
RawIMonadT T = ∀ {M} → RawIMonad M → RawIMonad (T M)

record RawIMonadZero {I : Set i} (M : IFun I f) : Set (i ⊔ suc f) where
  field
    monad           : RawIMonad M
    applicativeZero : RawIApplicativeZero M

  open RawIMonad monad public
  open RawIApplicativeZero applicativeZero using (∅) public

record RawIMonadPlus {I : Set i} (M : IFun I f) : Set (i ⊔ suc f) where
  field
    monad       : RawIMonad M
    alternative : RawIAlternative M

  open RawIMonad monad public
  open RawIAlternative alternative using (∅; _∣_) public

  monadZero : RawIMonadZero M
  monadZero = record
    { monad           = monad
    ; applicativeZero = RawIAlternative.applicativeZero alternative
    }
