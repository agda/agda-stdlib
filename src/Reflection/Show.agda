------------------------------------------------------------------------
-- The Agda standard library
--
-- Converting reflection machinery to strings
------------------------------------------------------------------------

-- Note that Reflection.termErr can also be used directly in tactic
-- error messages.

{-# OPTIONS --without-K --safe #-}

module Reflection.Show where

import Data.Char as Char
import Data.Float as Float
open import Data.List hiding (_++_; intersperse)
import Data.Nat as ℕ
import Data.Nat.Show as ℕ
open import Data.Product using (_×_; _,_)
open import Data.String as String
import Data.Word as Word
open import Relation.Nullary using (yes; no)
open import Function.Base using (id; _∘′_; case_of_)

open import Reflection.Abstraction hiding (map)
open import Reflection.Argument hiding (map)
open import Reflection.Argument.Relevance
open import Reflection.Argument.Visibility
open import Reflection.Argument.Modality
open import Reflection.Argument.Information
open import Reflection.Definition
open import Reflection.Literal
open import Reflection.Pattern
open import Reflection.Term

------------------------------------------------------------------------
-- Re-export primitive show functions

open import Agda.Builtin.Reflection public
  using () renaming
  ( primShowMeta  to showMeta
  ; primShowQName to showName
  )

------------------------------------------------------------------------
-- Non-primitive show functions

showRelevance : Relevance → String
showRelevance relevant   = "relevant"
showRelevance irrelevant = "irrelevant"

showRel : Relevance → String
showRel relevant   = ""
showRel irrelevant = "."

showVisibility : Visibility → String
showVisibility visible   = "visible"
showVisibility hidden    = "hidden"
showVisibility instance′ = "instance"

showLiteral : Literal → String
showLiteral (nat x)    = ℕ.show x
showLiteral (word64 x) = ℕ.show (Word.toℕ x)
showLiteral (float x)  = Float.show x
showLiteral (char x)   = Char.show x
showLiteral (string x) = String.show x
showLiteral (name x)   = showName x
showLiteral (meta x)   = showMeta x

private
  -- add appropriate parens depending on the given visibility
  visibilityParen : Visibility → String → String
  visibilityParen visible   s = parensIfSpace s
  visibilityParen hidden    s = braces s
  visibilityParen instance′ s = braces (braces s)

mutual

  showTerms : List (Arg Term) → String
  showTerms []             = ""
  showTerms (arg i t ∷ ts) = visibilityParen (visibility i) (showTerm t) <+> showTerms ts

  showTerm : Term → String
  showTerm (var x args)         = "var" <+> ℕ.show x <+> showTerms args
  showTerm (con c args)         = showName c <+> showTerms args
  showTerm (def f args)         = showName f <+> showTerms args
  showTerm (lam v (abs s x))    = "λ" <+> visibilityParen v s <+> "→" <+> showTerm x
  showTerm (pat-lam cs args)    =
    "λ {" <+> showClauses cs <+> "}" <+> showTerms args
  showTerm (Π[ x ∶ arg i a ] b) =
    "Π (" ++ visibilityParen (visibility i) x <+> ":" <+>
    parensIfSpace (showTerm a) ++ ")" <+> parensIfSpace (showTerm b)
  showTerm (sort s)             = showSort s
  showTerm (lit l)              = showLiteral l
  showTerm (meta x args)        = showMeta x <+> showTerms args
  showTerm unknown              = "unknown"

  showSort : Sort → String
  showSort (set t) = "Set" <+> parensIfSpace (showTerm t)
  showSort (lit n) = "Set" ++ ℕ.show n -- no space to disambiguate from set t
  showSort (prop t) = "Prop" <+> parensIfSpace (showTerm t)
  showSort (propLit n) = "Prop" ++ ℕ.show n -- no space to disambiguate from prop t
  showSort (inf n) = "Setω" ++ ℕ.show n
  showSort unknown = "unknown"

  showPatterns : List (Arg Pattern) → String
  showPatterns []       = ""
  showPatterns (a ∷ ps) = showArg a <+> showPatterns ps
    where
    -- Quantities are ignored.
    showArg : Arg Pattern → String
    showArg (arg (arg-info h (modality r _)) p) =
      braces? (showRel r ++ showPattern p)
      where
      braces? = case h of λ where
        visible   → id
        hidden    → braces
        instance′ → braces ∘′ braces

  showPattern : Pattern → String
  showPattern (con c []) = showName c
  showPattern (con c ps) = parens (showName c <+> showPatterns ps)
  showPattern (dot t)    = "." ++ parens (showTerm t)
  showPattern (var x)    = "pat-var" <+> ℕ.show x
  showPattern (lit l)    = showLiteral l
  showPattern (proj f)   = showName f
  showPattern (absurd _) = "()"

  showClause : Clause → String
  showClause (clause tel ps t)      = "[" <+> showTel tel <+> "]" <+> showPatterns ps <+> "→" <+> showTerm t
  showClause (absurd-clause tel ps) = "[" <+> showTel tel <+> "]" <+> showPatterns ps

  showClauses : List Clause → String
  showClauses []       = ""
  showClauses (c ∷ cs) = showClause c <+> ";" <+> showClauses cs

  showTel : List (String × Arg Type) → String
  showTel [] = ""
  showTel ((x , arg i t) ∷ tel) = visibilityParen (visibility i) (x <+> ":" <+> showTerm t) ++ showTel tel

showDefinition : Definition → String
showDefinition (function cs)       = "function" <+> braces (showClauses cs)
showDefinition (data-type pars cs) =
 "datatype" <+> ℕ.show pars <+> braces (intersperse ", " (map showName cs))
showDefinition (record′ c fs)      =
 "record" <+> showName c <+> braces (intersperse ", " (map (showName ∘′ unArg) fs))
showDefinition (constructor′ d)    = "constructor" <+> showName d
showDefinition axiom               = "axiom"
showDefinition primitive′          = "primitive"
