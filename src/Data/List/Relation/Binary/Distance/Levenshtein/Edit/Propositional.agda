------------------------------------------------------------------------
-- The Agda standard library
--
-- Levenshtein distance: the Edit relation and its properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Distance.Levenshtein.Edit.Propositional {a} (A : Set a) where

open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)

private
  variable
    xs ys : List A

------------------------------------------------------------------------
-- Re-exporting the core definitions

open import Data.List.Relation.Binary.Distance.Levenshtein.Edit.Setoid (setoid A)
  as Edit
  using
    ( Edit
    ; done
    ; delL
    ; delR
    ; swap
    ; fromPointwise
    ; toPointwise
    ; edit-[]ˡ
    ; edit-[]ʳ
    ; reflexive
    ; symmetric
    ; compose
    ; not-unique
    ; not-triangle
    ) public

pattern same edit = Edit.skip refl edit

reflexive-invert : Edit xs ys 0 → xs ≡ ys
reflexive-invert done        = refl
reflexive-invert (same edit) = cong (_ ∷_) (reflexive-invert edit)
