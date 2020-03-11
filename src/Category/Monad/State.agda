------------------------------------------------------------------------
-- The Agda standard library
--
-- The state monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Category.Monad.State where

open import Category.Applicative.Indexed
open import Category.Monad
open import Function.Identity.Categorical as Id using (Identity)
open import Category.Monad.Indexed
open import Data.Product
open import Data.Unit
open import Function
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
  { pure = λ a s → return (a , s)
  ; _⊛_  = λ f t s → do
     (f′ , s′)  ← f s
     (t′ , s′′) ← t s′
     return (f′ t′ , s′′)
  } where open RawMonad Mon

StateTIApplicativeZero : ∀ (S : I → Set f) {M} →
                         RawMonadZero M → RawIApplicativeZero (IStateT S M)
StateTIApplicativeZero S Mon = record
  { applicative = StateTIApplicative S monad
  ; ∅           = const ∅
  } where open RawMonadZero Mon

StateTIAlternative : ∀ (S : I → Set f) {M} →
                     RawMonadPlus M → RawIAlternative (IStateT S M)
StateTIAlternative S Mon = record
  { applicativeZero = StateTIApplicativeZero S monadZero
  ; _∣_             = λ m n s → m s ∣ n s
  } where open RawMonadPlus Mon

------------------------------------------------------------------------
-- Indexed state monad

StateTIMonad : ∀ (S : I → Set f) {M} → RawMonad M → RawIMonad (IStateT S M)
StateTIMonad S Mon = record
  { return = λ x s → return (x , s)
  ; _>>=_  = λ m f s → m s >>= uncurry f
  } where open RawMonad Mon

StateTIMonadZero : ∀ (S : I → Set f) {M} →
                   RawMonadZero M → RawIMonadZero (IStateT S M)
StateTIMonadZero S Mon = record
  { monad           = StateTIMonad S (RawMonadZero.monad Mon)
  ; applicativeZero = StateTIApplicativeZero S Mon
  } where open RawMonadZero Mon

StateTIMonadPlus : ∀ (S : I → Set f) {M} →
                   RawMonadPlus M → RawIMonadPlus (IStateT S M)
StateTIMonadPlus S Mon = record
  { monad       = StateTIMonad S monad
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
  ; get   = λ s   → return (s , s)
  ; put   = λ s _ → return (_ , s)
  }
  where open RawIMonad Mon

------------------------------------------------------------------------
-- Ordinary state monads

RawMonadState : Set f → (Set f → Set f) → Set _
RawMonadState S M = RawIMonadState {I = ⊤} (λ _ → S) (λ _ _ → M)

module RawMonadState {S : Set f} {M : Set f → Set f}
                     (Mon : RawMonadState S M) where
  open RawIMonadState Mon public

StateT : Set f → (Set f → Set f) → Set f → Set f
StateT S M = IStateT {I = ⊤} (λ _ → S) M _ _

StateTMonad : ∀ (S : Set f) {M} → RawMonad M → RawMonad (StateT S M)
StateTMonad S = StateTIMonad (λ _ → S)

StateTMonadZero : ∀ (S : Set f) {M} →
                  RawMonadZero M → RawMonadZero (StateT S M)
StateTMonadZero S = StateTIMonadZero (λ _ → S)

StateTMonadPlus : ∀ (S : Set f) {M} →
                  RawMonadPlus M → RawMonadPlus (StateT S M)
StateTMonadPlus S = StateTIMonadPlus (λ _ → S)

StateTMonadState : ∀ (S : Set f) {M} →
                   RawMonad M → RawMonadState S (StateT S M)
StateTMonadState S = StateTIMonadState (λ _ → S)

State : Set f → Set f → Set f
State S = StateT S Identity

StateMonad : (S : Set f) → RawMonad (State S)
StateMonad S = StateTMonad S Id.monad

StateMonadState : (S : Set f) → RawMonadState S (State S)
StateMonadState S = StateTMonadState S Id.monad

LiftMonadState : ∀ {S₁} (S₂ : Set f) {M} →
                 RawMonadState S₁ M →
                 RawMonadState S₁ (StateT S₂ M)
LiftMonadState S₂ Mon = record
  { monad = StateTIMonad (λ _ → S₂) monad
  ; get   = λ s → get >>= λ x → return (x , s)
  ; put   = λ s′ s → put s′ >> return (_ , s)
  }
  where open RawIMonadState Mon
