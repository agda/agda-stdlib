------------------------------------------------------------------------
-- The Agda standard library
--
-- Regular expressions
--
-- The content of this module (and others in the Regex subdirectory) is
-- based on Alexandre Agular and Bassel Mannaa's 2009 technical report:
-- Regular Expressions in Agda
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecPoset)

module Text.Regex {a e r} (decPoset : DecPoset a e r) where


private
  preorder = DecPoset.preorder decPoset

import Text.Regex.Base                  preorder as Regex
import Text.Regex.SmartConstructors     preorder as Smart
import Text.Regex.Derivative.Brzozowski decPoset as Eat
import Text.Regex.Search                decPoset as Search

------------------------------------------------------------------------
-- Re-exporting basic definition and semantics

open Regex public
  using ( Range; module Range
        ; [_]; _─_
        ; Regex; module Regex; Exp; module Exp
        ; ε; [^_]; ∅; ·; singleton
        ; _∈ᴿ_; _∉ᴿ_
        ; _∈_; _∉_; sum; prod; star
        )

------------------------------------------------------------------------
-- Re-exporting smart constructors

open Smart public
  using (_∣_; _∙_; _⋆; _+; _⁇)

------------------------------------------------------------------------
-- Re-exporting semantics decidability

open Eat public
  using (_∈?_; _∉?_)

------------------------------------------------------------------------
-- Re-exporting search algorithms

open Search public
  using (Span; toInfix; Match; mkMatch; search)
