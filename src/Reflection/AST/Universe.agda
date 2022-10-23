------------------------------------------------------------------------
-- The Agda standard library
--
-- A universe for the types involved in the reflected syntax.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Universe where

open import Data.List.Base             using (List)
open import Data.String.Base           using (String)
open import Data.Product               using (_×_)
open import Reflection.AST.Argument    using (Arg)
open import Reflection.AST.Abstraction using (Abs)
open import Reflection.AST.Term        using (Term; Pattern; Sort; Clause)

data Univ : Set where
  ⟨term⟩   : Univ
  ⟨pat⟩    : Univ
  ⟨sort⟩   : Univ
  ⟨clause⟩ : Univ
  ⟨list⟩   : Univ → Univ
  ⟨arg⟩    : Univ → Univ
  ⟨abs⟩    : Univ → Univ
  ⟨named⟩  : Univ → Univ

pattern ⟨tel⟩ = ⟨list⟩ (⟨named⟩ (⟨arg⟩ ⟨term⟩))

⟦_⟧ : Univ → Set
⟦ ⟨term⟩    ⟧ = Term
⟦ ⟨pat⟩     ⟧ = Pattern
⟦ ⟨sort⟩    ⟧ = Sort
⟦ ⟨clause⟩  ⟧ = Clause
⟦ ⟨list⟩ k  ⟧ = List ⟦ k ⟧
⟦ ⟨arg⟩ k   ⟧ = Arg ⟦ k ⟧
⟦ ⟨abs⟩ k   ⟧ = Abs ⟦ k ⟧
⟦ ⟨named⟩ k ⟧ = String × ⟦ k ⟧
