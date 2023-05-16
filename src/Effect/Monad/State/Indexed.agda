------------------------------------------------------------------------
-- The Agda standard library
--
-- The indexed state monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.State.Indexed where

open import Effect.Applicative.Indexed
open import Effect.Monad
open import Function.Identity.Effectful as Id using (Identity)
open import Effect.Monad.Indexed
open import Data.Product
open import Data.Unit
open import Function.Base
open import Level

private
  variable
    i f : Level
    I : Set i

------------------------------------------------------------------------
-- Indexed state

IStateT : (I → Set f) → (Set f → Set f) → IFun I f
IStateT S M i j A = S i → M (A × S j)

------------------------------------------------------------------------
-- Indexed state applicative

StateTIApplicative : ∀ (S : I → Set f) {M} →
                     RawMonad M → RawIApplicative (IStateT S M)
StateTIApplicative S Mon = record
  { pure = λ a s → pure (a , s)
  ; _⊛_  = λ f t s → do
     (f′ , s′)  ← f s
     (t′ , s′′) ← t s′
     pure (f′ t′ , s′′)
  } where open RawMonad Mon

StateTIApplicativeZero : ∀ (S : I → Set f) {M} →
                         RawMonadZero M → RawIApplicativeZero (IStateT S M)
StateTIApplicativeZero S Mon = record
  { applicative = StateTIApplicative S rawMonad
  ; ∅           = const ∅
  } where open RawMonadZero Mon

StateTIAlternative : ∀ (S : I → Set f) {M} →
                     RawMonadPlus M → RawIAlternative (IStateT S M)
StateTIAlternative S Mon = record
  { applicativeZero = StateTIApplicativeZero S rawMonadZero
  ; _∣_             = λ m n s → m s ∣ n s
  } where open RawMonadPlus Mon

------------------------------------------------------------------------
-- Indexed state monad

StateTIMonad : ∀ (S : I → Set f) {M} → RawMonad M → RawIMonad (IStateT S M)
StateTIMonad S Mon = record
  { return = λ x s → pure (x , s)
  ; _>>=_  = λ m f s → m s >>= uncurry f
  } where open RawMonad Mon

StateTIMonadZero : ∀ (S : I → Set f) {M} →
                   RawMonadZero M → RawIMonadZero (IStateT S M)
StateTIMonadZero S Mon = record
  { monad           = StateTIMonad S (RawMonadZero.rawMonad Mon)
  ; applicativeZero = StateTIApplicativeZero S Mon
  } where open RawMonadZero Mon

StateTIMonadPlus : ∀ (S : I → Set f) {M} →
                   RawMonadPlus M → RawIMonadPlus (IStateT S M)
StateTIMonadPlus S Mon = record
  { monad       = StateTIMonad S rawMonad
  ; alternative = StateTIAlternative S Mon
  } where open RawMonadPlus Mon

------------------------------------------------------------------------
-- State monad operations

record RawIMonadState {I : Set i} (S : I → Set f)
                      (M : IFun I f) : Set (i ⊔ suc f) where
  field
    monad : RawIMonad M
    get   : ∀ {i} → M i i (S i)
    put   : ∀ {i j} → S j → M i j (Lift f ⊤)

  open RawIMonad monad public

  modify : ∀ {i j} → (S i → S j) → M i j (Lift f ⊤)
  modify f = get >>= put ∘ f

StateTIMonadState : ∀ {i f} {I : Set i} (S : I → Set f) {M} →
                    RawMonad M → RawIMonadState S (IStateT S M)
StateTIMonadState S Mon = record
  { monad = StateTIMonad S Mon
  ; get   = λ s   → pure (s , s)
  ; put   = λ s _ → pure (_ , s)
  }
  where open RawMonad Mon
