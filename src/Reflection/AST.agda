------------------------------------------------------------------------
-- The Agda standard library
--
-- The reflected abstract syntax tree
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST where

import Agda.Builtin.Reflection as Builtin

------------------------------------------------------------------------
-- Names, Metas, and Literals re-exported publicly

open import Reflection.AST.Abstraction as Abstraction public
  using (Abs; abs)
open import Reflection.AST.Argument as Argument public
  using (Arg; arg; Args; vArg; hArg; iArg; defaultModality)
open import Reflection.AST.Definition as Definition  public
  using (Definition)
open import Reflection.AST.Meta as Meta public
  using (Meta)
open import Reflection.AST.Name as Name public
  using (Name; Names)
open import Reflection.AST.Literal as Literal public
  using (Literal)
open import Reflection.AST.Pattern as Pattern public
  using (Pattern)
open import Reflection.AST.Term as Term public
  using (Term; Type; Clause; Clauses; Sort)

import Reflection.AST.Argument.Modality    as Modality
import Reflection.AST.Argument.Quantity    as Quantity
import Reflection.AST.Argument.Relevance   as Relevance
import Reflection.AST.Argument.Visibility  as Visibility
import Reflection.AST.Argument.Information as Information

open Definition.Definition public
open Information.ArgInfo public
open Literal.Literal public
open Modality.Modality public
open Quantity.Quantity public
open Relevance.Relevance public
open Term.Term public
open Visibility.Visibility public

open import Reflection.AST.Show public

------------------------------------------------------------------------
-- Fixity

open Builtin public
  using (non-assoc; related; unrelated; fixity)
  renaming
  ( left-assoc      to assocˡ
  ; right-assoc     to assocʳ
  ; primQNameFixity to getFixity
  )
