------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

module Category.Monad.Indexed where

open import Category.Applicative.Indexed
open import Function
open import Level

record RawIMonad {i f} {I : Set i} (M : IFun I f) :
                 Set (i ⊔ suc f) where
  infixl 1 _>>=_ _>>_ _>=>_
  infixr 1 _=<<_ _<=<_

  field
    return : ∀ {i A} → A → M i i A
    _>>=_  : ∀ {i j k A B} → M i j A → (A → M j k B) → M i k B

  _>>_ : ∀ {i j k A B} → M i j A → M j k B → M i k B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : ∀ {i j k A B} → (A → M j k B) → M i j A → M i k B
  f =<< c = c >>= f

  _>=>_ : ∀ {i j k a} {A : Set a} {B C} →
          (A → M i j B) → (B → M j k C) → (A → M i k C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : ∀ {i j k B C a} {A : Set a} →
          (B → M j k C) → (A → M i j B) → (A → M i k C)
  g <=< f = f >=> g

  join : ∀ {i j k A} → M i j (M j k A) → M i k A
  join m = m >>= id

  rawIApplicative : RawIApplicative M
  rawIApplicative = record
    { pure = return
    ; _⊛_  = λ f x → f >>= λ f' → x >>= λ x' → return (f' x')
    }

  open RawIApplicative rawIApplicative public

RawIMonadT : ∀ {i f} {I : Set i} (T : IFun I f → IFun I f) → Set (i ⊔ suc f)
RawIMonadT T = ∀ {M} → RawIMonad M → RawIMonad (T M)

record RawIMonadZero {i f} {I : Set i} (M : IFun I f) :
                     Set (i ⊔ suc f) where
  field
    monad : RawIMonad M
    ∅     : ∀ {i j A} → M i j A

  open RawIMonad monad public

record RawIMonadPlus {i f} {I : Set i} (M : IFun I f) :
                     Set (i ⊔ suc f) where
  infixr 3 _∣_
  field
    monadZero : RawIMonadZero M
    _∣_       : ∀ {i j A} → M i j A → M i j A → M i j A

  open RawIMonadZero monadZero public
