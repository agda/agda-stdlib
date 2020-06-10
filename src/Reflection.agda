------------------------------------------------------------------------
-- The Agda standard library
--
-- Support for reflection
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection where

import Agda.Builtin.Reflection as Builtin

------------------------------------------------------------------------
-- Names, Metas, and Literals re-exported publicly

open import Reflection.Abstraction as Abstraction public
  using (Abs; abs)
open import Reflection.Argument as Argument public
  using (Arg; arg; Args; vArg; hArg; iArg)
open import Reflection.Definition as Definition  public
  using (Definition)
open import Reflection.Meta as Meta public
  using (Meta)
open import Reflection.Name as Name public
  using (Name; Names)
open import Reflection.Literal as Literal public
  using (Literal)
open import Reflection.Pattern as Pattern public
  using (Pattern)
open import Reflection.Term as Term public
  using (Term; Type; Clause; Clauses; Sort)

import Reflection.Argument.Relevance as Relevance
import Reflection.Argument.Visibility as Visibility
import Reflection.Argument.Information as Information

open Definition.Definition public
open Information.ArgInfo public
open Literal.Literal public
open Relevance.Relevance public
open Term.Term public
open Visibility.Visibility public

------------------------------------------------------------------------
-- Fixity

open Builtin public
  using (non-assoc; related; unrelated; fixity)
  renaming
  ( left-assoc      to assocˡ
  ; right-assoc     to assocʳ
  ; primQNameFixity to getFixity
  )

------------------------------------------------------------------------
-- Type checking monad

open import Reflection.TypeChecking.Monad public

-- Standard monad operators

open import Reflection.TypeChecking.Monad.Syntax public
  using (_>>=_; _>>_)

------------------------------------------------------------------------
-- Show

open import Reflection.Show public



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

returnTC = return
{-# WARNING_ON_USAGE returnTC
"Warning: returnTC was deprecated in v1.1.
Please use return instead."
#-}

-- Version 1.3

Arg-info = Information.ArgInfo
{-# WARNING_ON_USAGE Arg-info
"Warning: Arg-info was deprecated in v1.3.
Please use Reflection.Argument.Information's ArgInfo instead."
#-}

infix 4 _≟-Lit_ _≟-Name_ _≟-Meta_ _≟-Visibility_ _≟-Relevance_ _≟-Arg-info_
        _≟-Pattern_ _≟-ArgPatterns_

_≟-Lit_ = Literal._≟_
{-# WARNING_ON_USAGE _≟-Lit_
"Warning: _≟-Lit_ was deprecated in v1.3.
Please use Reflection.Literal's _≟_ instead."
#-}

_≟-Name_ = Name._≟_
{-# WARNING_ON_USAGE _≟-Name_
"Warning: _≟-Name_ was deprecated in v1.3.
Please use Reflection.Name's _≟_ instead."
#-}

_≟-Meta_ = Meta._≟_
{-# WARNING_ON_USAGE _≟-Meta_
"Warning: _≟-Meta_ was deprecated in v1.3.
Please use Reflection.Meta's _≟_ instead."
#-}

_≟-Visibility_ = Visibility._≟_
{-# WARNING_ON_USAGE _≟-Visibility_
"Warning: _≟-Visibility_ was deprecated in v1.3.
Please use Reflection.Argument.Visibility's _≟_ instead."
#-}

_≟-Relevance_ = Relevance._≟_
{-# WARNING_ON_USAGE _≟-Relevance_
"Warning: _≟-Relevance_ was deprecated in v1.3.
Please use Reflection.Argument.Relevance's _≟_ instead."
#-}

_≟-Arg-info_ = Information._≟_
{-# WARNING_ON_USAGE _≟-Arg-info_
"Warning: _≟-Arg-info_ was deprecated in v1.3.
Please use Reflection.Argument.Information's _≟_ instead."
#-}

_≟-Pattern_ = Pattern._≟_
{-# WARNING_ON_USAGE _≟-Pattern_
"Warning: _≟-Pattern_ was deprecated in v1.3.
Please use Reflection.Pattern's _≟_ instead."
#-}

_≟-ArgPatterns_ = Pattern._≟s_
{-# WARNING_ON_USAGE _≟-ArgPatterns_
"Warning: _≟-ArgPatterns_ was deprecated in v1.3.
Please use Reflection.Pattern's _≟s_ instead."
#-}

map-Abs = Abstraction.map
{-# WARNING_ON_USAGE map-Abs
"Warning: map-Abs was deprecated in v1.3.
Please use Reflection.Abstraction's map instead."
#-}

map-Arg = Argument.map
{-# WARNING_ON_USAGE map-Arg
"Warning: map-Arg was deprecated in v1.3.
Please use Reflection.Argument's map instead."
#-}

map-Args = Argument.map-Args
{-# WARNING_ON_USAGE map-Args
"Warning: map-Args was deprecated in v1.3.
Please use Reflection.Argument's map-Args instead."
#-}

visibility = Information.visibility
{-# WARNING_ON_USAGE visibility
"Warning: visibility was deprecated in v1.3.
Please use Reflection.Argument.Information's visibility instead."
#-}

relevance = Information.relevance
{-# WARNING_ON_USAGE relevance
"Warning: relevance was deprecated in v1.3.
Please use Reflection.Argument.Information's relevance instead."
#-}

infix 4 _≟-AbsTerm_ _≟-AbsType_ _≟-ArgTerm_ _≟-ArgType_ _≟-Args_
        _≟-Clause_ _≟-Clauses_ _≟_
        _≟-Sort_

_≟-AbsTerm_ = Term._≟-AbsTerm_
{-# WARNING_ON_USAGE _≟-AbsTerm_
"Warning: _≟-AbsTerm_ was deprecated in v1.3.
Please use Reflection.Term's _≟-AbsTerm_ instead."
#-}

_≟-AbsType_ = Term._≟-AbsType_
{-# WARNING_ON_USAGE _≟-AbsType_
"Warning: _≟-AbsType_ was deprecated in v1.3.
Please use Reflection.Term's _≟-AbsType_ instead."
#-}

_≟-ArgTerm_ = Term._≟-ArgTerm_
{-# WARNING_ON_USAGE _≟-ArgTerm_
"Warning: _≟-ArgTerm_ was deprecated in v1.3.
Please use Reflection.Term's _≟-ArgTerm_ instead."
#-}

_≟-ArgType_ = Term._≟-ArgType_
{-# WARNING_ON_USAGE _≟-ArgType_
"Warning: _≟-ArgType_ was deprecated in v1.3.
Please use Reflection.Term's _≟-ArgType_ instead."
#-}

_≟-Args_    = Term._≟-Args_
{-# WARNING_ON_USAGE _≟-Args_
"Warning: _≟-Args_ was deprecated in v1.3.
Please use Reflection.Term's _≟-Args_ instead."
#-}

_≟-Clause_  = Term._≟-Clause_
{-# WARNING_ON_USAGE _≟-Clause_
"Warning: _≟-Clause_ was deprecated in v1.3.
Please use Reflection.Term's _≟-Clause_ instead."
#-}

_≟-Clauses_ = Term._≟-Clauses_
{-# WARNING_ON_USAGE _≟-Clauses_
"Warning: _≟-Clauses_ was deprecated in v1.3.
Please use Reflection.Term's _≟-Clauses_ instead."
#-}

_≟_         = Term._≟_
{-# WARNING_ON_USAGE _≟_
"Warning: _≟_ was deprecated in v1.3.
Please use Reflection.Term's _≟_ instead."
#-}

_≟-Sort_    = Term._≟-Sort_
{-# WARNING_ON_USAGE _≟-Sort_
"Warning: _≟-Sort_ was deprecated in v1.3.
Please use Reflection.Term's _≟-Sort_ instead."
#-}
