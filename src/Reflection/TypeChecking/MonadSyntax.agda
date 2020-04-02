------------------------------------------------------------------------
-- The Agda standard library
--
-- Monad syntax for the TC monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.TypeChecking.MonadSyntax where

open import Agda.Builtin.Reflection
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Monad syntax

pure : A → TC A
pure = returnTC
{-# INLINE pure #-}

infixl 3 _<|>_
_<|>_ : TC A → TC A → TC A
_<|>_ = catchTC
{-# INLINE _<|>_ #-}

infixl 1 _>>=_ _>>_ _<&>_
_>>=_ : TC A → (A → TC B) → TC B
_>>=_ = bindTC
{-# INLINE _>>=_ #-}

_>>_ : TC A → TC B → TC B
xs >> ys = bindTC xs (λ _ → ys)
{-# INLINE _>>_ #-}

infixl 4 _<$>_ _<*>_ _<$_
_<*>_ : TC (A → B) → TC A → TC B
fs <*> xs = bindTC fs (λ f → bindTC xs (λ x → returnTC (f x)))
{-# INLINE _<*>_ #-}

_<$>_ : (A → B) → TC A → TC B
f <$> xs = bindTC xs (λ x → returnTC (f x))
{-# INLINE _<$>_ #-}

_<$_ : A → TC B → TC A
x <$ xs = bindTC xs (λ _ → returnTC x)
{-# INLINE _<$_ #-}

_<&>_ : TC A → (A → B) → TC B
xs <&> f = bindTC xs (λ x → returnTC (f x))
{-# INLINE _<&>_ #-}
