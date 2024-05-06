------------------------------------------------------------------------
-- The Agda standard library
--
-- A delimited continuation monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Continuation where

open import Effect.Applicative.Indexed using (IFun)
open import Effect.Monad using (RawMonad)
open import Function.Identity.Effectful as Id using (Identity)
open import Effect.Monad.Indexed using (RawIMonad)
open import Function.Base using (flip)
open import Level using (Level; _⊔_; suc)

private
  variable
    i f : Level
    I : Set i

------------------------------------------------------------------------
-- Delimited continuation monads

DContT : (I → Set f) → (Set f → Set f) → IFun I f
DContT K M r₂ r₁ a = (a → M (K r₁)) → M (K r₂)

DCont : (I → Set f) → IFun I f
DCont K = DContT K Identity

DContTIMonad : ∀ (K : I → Set f) {M} → RawMonad M → RawIMonad (DContT K M)
DContTIMonad K Mon = record
  { return = λ a k → k a
  ; _>>=_  = λ c f k → c (flip f k)
  }
  where open RawMonad Mon

DContIMonad : (K : I → Set f) → RawIMonad (DCont K)
DContIMonad K = DContTIMonad K Id.monad

------------------------------------------------------------------------
-- Delimited continuation operations

record RawIMonadDCont {I : Set i} (K : I → Set f)
                      (M : IFun I f) : Set (i ⊔ suc f) where
  field
    monad : RawIMonad M
    reset : ∀ {r₁ r₂ r₃} → M r₁ r₂ (K r₂) → M r₃ r₃ (K r₁)
    shift : ∀ {a r₁ r₂ r₃ r₄} →
            ((a → M r₁ r₁ (K r₂)) → M r₃ r₄ (K r₄)) → M r₃ r₂ a

  open RawIMonad monad public

DContTIMonadDCont : ∀ (K : I → Set f) {M} →
                    RawMonad M → RawIMonadDCont K (DContT K M)
DContTIMonadDCont K Mon = record
  { monad = DContTIMonad K Mon
  ; reset = λ e k → e pure >>= k
  ; shift = λ e k → e (λ a k′ → (k a) >>= k′) pure
  }
  where
  open RawMonad Mon

DContIMonadDCont : (K : I → Set f) → RawIMonadDCont K (DCont K)
DContIMonadDCont K = DContTIMonadDCont K Id.monad
