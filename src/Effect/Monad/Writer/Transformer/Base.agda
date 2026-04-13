------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic type and definition of the writer monad transformer
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Effect.Monad.Writer.Transformer.Base where

open import Algebra using (RawMonoid)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Effect.Functor using (RawFunctor)
open import Function.Base using (id; _∘′_)
open import Level using (Level; suc; _⊔_)

private
  variable
    w f g : Level
    A : Set g
    M : Set w → Set g
    𝕎 : RawMonoid w g

------------------------------------------------------------------------
-- Writer monad operations

record RawMonadWriter
       (𝕎 : RawMonoid w f)
       (M : Set w → Set g)
       : Set (suc w ⊔ g) where
  open RawMonoid 𝕎 renaming (Carrier to W)
  field
    writer : W × A → M A
    listen : M A → M (W × A)
    pass   : M ((W → W) × A) → M A

  tell : W → M ⊤
  tell w = writer (w , tt)

------------------------------------------------------------------------
-- Writer monad transformer (CPS-encoded)

record WriterT
       (𝕎 : RawMonoid w f)
       (M : Set w → Set g)
       (A : Set w)
       : Set (w ⊔ g) where
  constructor mkWriterT
  open RawMonoid 𝕎 renaming (Carrier to W)
  field runWriterT : W → M (W × A)
open WriterT public

module _ {𝕎 : RawMonoid w f} where

  open RawMonoid 𝕎 renaming (Carrier to W)

  evalWriterT : RawFunctor M → WriterT 𝕎 M A → M A
  evalWriterT M ma = proj₂ <$> runWriterT ma ε
    where open RawFunctor M

  execWriterT : RawFunctor M → WriterT 𝕎 M A → M W
  execWriterT M ma = proj₁ <$> runWriterT ma ε
    where open RawFunctor M
