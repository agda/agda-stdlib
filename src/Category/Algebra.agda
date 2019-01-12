------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebras for endofunctors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Category
open import Category.Functor
open import Category.Structures

module Category.Algebra {o m r}
                        {cat : RawCategory o m r}
                        (F : RawFunctor cat cat) where
  open RawCategory cat
  open RawFunctor F renaming (F to F₀)

  record Algebra : Set (o ⊔ m) where
    field
      {Carrier} : Obj
      evaluate  : F₀ Carrier ⇒ Carrier
  open Algebra public
