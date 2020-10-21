------------------------------------------------------------------------
-- The Agda standard library
--
-- A universe for the types involved in the reflected syntax.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Universe where

open import Data.List              using (List)
open import Data.String            using (String)
open import Data.Product           using (_×_)
open import Reflection.Argument    using (Arg)
open import Reflection.Abstraction using (Abs)
open import Reflection.Term        using (Term; Pattern; Sort; Clause)

data Univ : Set where
  ⟨term⟩   : Univ
  ⟨pat⟩    : Univ
  ⟨sort⟩   : Univ
  ⟨clause⟩ : Univ
  ⟨list⟩   : Univ → Univ
  ⟨arg⟩    : Univ → Univ
  ⟨abs⟩    : Univ → Univ
  ⟨named⟩  : Univ → Univ

⟦_⟧ : Univ → Set
⟦ ⟨term⟩    ⟧ = Term
⟦ ⟨pat⟩     ⟧ = Pattern
⟦ ⟨sort⟩    ⟧ = Sort
⟦ ⟨clause⟩  ⟧ = Clause
⟦ ⟨list⟩ k  ⟧ = List ⟦ k ⟧
⟦ ⟨arg⟩ k   ⟧ = Arg ⟦ k ⟧
⟦ ⟨abs⟩ k   ⟧ = Abs ⟦ k ⟧
⟦ ⟨named⟩ k ⟧ = String × ⟦ k ⟧
