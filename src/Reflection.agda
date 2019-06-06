------------------------------------------------------------------------
-- The Agda standard library
--
-- Support for reflection
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection where

open import Data.List.Base using (List); open List

open import Data.Nat    as ℕ      using (ℕ)
open import Data.String as String using (String)

open import Data.Product
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product

import Agda.Builtin.Reflection as Builtin

private
  variable
    a b c d : Level
    A B C D : Set a

------------------------------------------------------------------------
-- Names, Metas, and Literals re-exported publically

open import Reflection.Name as Name using (Name; Names) public
open import Reflection.Meta as Meta using (Meta) public
open import Reflection.Literal as Literal using (Literal) public
open Literal.Literal public
open import Reflection.Argument as Argument
  using ( Arg; arg; Args
        ; vArg; hArg; iArg
        ) public
import Reflection.Argument.Relevance as Relevance
open Relevance.Relevance public
import Reflection.Argument.Visibility as Visibility
open Visibility.Visibility public
import Reflection.Argument.Information as Information
open Information.ArgInfo public
open import Reflection.Term as Term using (Term; Type; Clause; Clauses; Sort) public
open Term.Term public

open import Reflection.Pattern as Pattern using (Pattern) public
open import Reflection.Abstraction as Abstraction using (Abs; abs) public

------------------------------------------------------------------------
-- Fixity

open Builtin public using (non-assoc; related; unrelated; fixity)
  renaming ( left-assoc  to assocˡ
           ; right-assoc to assocʳ
           ; primQNameFixity to getFixity)

------------------------------------------------------------------------
-- Definitions

open Builtin public
  using    ( Definition
           ; function
           ; data-type
           ; axiom
           )
  renaming ( record-type to record′
           ; data-cons   to constructor′
           ; prim-fun    to primitive′ )

------------------------------------------------------------------------
-- Type checking monad

-- Type errors
open Builtin public using (ErrorPart; strErr; termErr; nameErr)

-- The monad
open Builtin public
  using ( TC; bindTC; unify; typeError; inferType; checkType
        ; normalise; reduce
        ; catchTC; quoteTC; unquoteTC
        ; getContext; extendContext; inContext; freshName
        ; declareDef; declarePostulate; defineFun; getType; getDefinition
        ; blockOnMeta; commitTC; isMacro; withNormalisation
        ; debugPrint; noConstraints; runSpeculative)
  renaming (returnTC to return)

infixl 1 _>>=_
infixl 1 _>>_

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
ma >>= f = bindTC ma f

_>>_ :  ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
ma >> mb = ma >>= (λ _ → mb)

newMeta : Type → TC Term
newMeta = checkType unknown

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

lmeta₁ = Literal.meta-injective
{-# WARNING_ON_USAGE lmeta₁
"Warning: lmeta₁ was deprecated in v1.1.
Please use Reflection.Literal's meta-injective instead."
#-}

nat₁ = Literal.nat-injective
{-# WARNING_ON_USAGE nat₁
"Warning: nat₁ was deprecated in v1.1.
Please use Reflection.Literal's nat-injective instead."
#-}

word64₁ = Literal.nat-injective
{-# WARNING_ON_USAGE word64₁
"Warning: word64₁ was deprecated in v1.1.
Please use Reflection.Literal's nat-injective instead."
#-}

float₁ = Literal.nat-injective
{-# WARNING_ON_USAGE float₁
"Warning: float₁ was deprecated in v1.1.
Please use Reflection.Literal's float-injective instead."
#-}

char₁ = Literal.char-injective
{-# WARNING_ON_USAGE char₁
"Warning: char₁ was deprecated in v1.1.
Please use Reflection.Literal's char-injective instead."
#-}

string₁ = Literal.string-injective
{-# WARNING_ON_USAGE string₁
"Warning: string₁ was deprecated in v1.1.
Please use Reflection.Literal's string-injective instead."
#-}

name₁ = Literal.name-injective
{-# WARNING_ON_USAGE name₁
"Warning: name₁ was deprecated in v1.1.
Please use Reflection.Literal's name-injective instead."
#-}

arg₁ = Argument.arg-injective₁
{-# WARNING_ON_USAGE arg₁
"Warning: arg₁ was deprecated in v1.1.
Please use Reflection.Argument's arg-injective₁ instead."
#-}

arg₂ = Argument.arg-injective₂
{-# WARNING_ON_USAGE arg₂
"Warning: arg₂ was deprecated in v1.1.
Please use Reflection.Argument's arg-injective₂ instead."
#-}

pcon₁ = Pattern.con-injective₁
{-# WARNING_ON_USAGE pcon₁
"Warning: pcon₁ was deprecated in v1.1.
Please use Reflection.Pattern's con-injective₁ instead."
#-}

pcon₂ = Pattern.con-injective₂
{-# WARNING_ON_USAGE pcon₂
"Warning: pcon₂ was deprecated in v1.1.
Please use Reflection.Pattern's con-injective₂ instead."
#-}

pvar = Pattern.con-injective₂
{-# WARNING_ON_USAGE pvar
"Warning: pvar was deprecated in v1.1.
Please use Reflection.Pattern's var-injective instead."
#-}

plit₁ = Pattern.con-injective₂
{-# WARNING_ON_USAGE plit₁
"Warning: plit₁ was deprecated in v1.1.
Please use Reflection.Pattern's lit-injective instead."
#-}

pproj₁ = Pattern.con-injective₂
{-# WARNING_ON_USAGE pproj₁
"Warning: pproj₁ was deprecated in v1.1.
Please use Reflection.Pattern's proj-injective instead."
#-}

arg-info₁ = Information.arg-info-injective₁
{-# WARNING_ON_USAGE arg-info₁
"Warning: arg-info₁ was deprecated in v1.1.
Please use Reflection.Argument.Information's arg-info-injective₁ instead."
#-}

arg-info₂ = Information.arg-info-injective₂
{-# WARNING_ON_USAGE arg-info₂
"Warning: arg-info₁ was deprecated in v1.1.
Please use Reflection.Argument.Information's arg-info-injective₂ instead."
#-}

abs₁ = Abstraction.abs-injective₁
{-# WARNING_ON_USAGE abs₁
"Warning: abs₁ was deprecated in v1.1.
Please use Reflection.Abstraction's abs-injective₁ instead."
#-}

abs₂ = Abstraction.abs-injective₂
{-# WARNING_ON_USAGE abs₂
"Warning: abs₁ was deprecated in v1.1.
Please use Reflection.Abstraction's abs-injective₂ instead."
#-}

Arg-info = Information.ArgInfo
{-# WARNING_ON_USAGE Arg-info
"Warning: Arg-info was deprecated in v1.1.
Please use Reflection.Argument.Information's ArgInfo instead."
#-}

infix 4 _≟-Lit_ _≟-Name_ _≟-Meta_ _≟-Visibility_ _≟-Relevance_ _≟-Arg-info_
        _≟-Pattern_ _≟-ArgPatterns_

_≟-Lit_ = Literal._≟_
{-# WARNING_ON_USAGE _≟-Lit_
"Warning: _≟-Lit_ was deprecated in v1.1.
Please use Reflection.Literal's _≟_ instead."
#-}

_≟-Name_ = Name._≟_
{-# WARNING_ON_USAGE _≟-Name_
"Warning: _≟-Name_ was deprecated in v1.1.
Please use Reflection.Name's _≟_ instead."
#-}

_≟-Meta_ = Meta._≟_
{-# WARNING_ON_USAGE _≟-Meta_
"Warning: _≟-Meta_ was deprecated in v1.1.
Please use Reflection.Meta's _≟_ instead."
#-}

_≟-Visibility_ = Visibility._≟_
{-# WARNING_ON_USAGE _≟-Visibility_
"Warning: _≟-Visibility_ was deprecated in v1.1.
Please use Reflection.Argument.Visibility's _≟_ instead."
#-}

_≟-Relevance_ = Relevance._≟_
{-# WARNING_ON_USAGE _≟-Relevance_
"Warning: _≟-Relevance_ was deprecated in v1.1.
Please use Reflection.Argument.Relevance's _≟_ instead."
#-}

_≟-Arg-info_ = Information._≟_
{-# WARNING_ON_USAGE _≟-Arg-info_
"Warning: _≟-Arg-info_ was deprecated in v1.1.
Please use Reflection.Argument.Information's _≟_ instead."
#-}

_≟-Pattern_ = Pattern._≟_
{-# WARNING_ON_USAGE _≟-Pattern_
"Warning: _≟-Pattern_ was deprecated in v1.1.
Please use Reflection.Pattern's _≟_ instead."
#-}

_≟-ArgPatterns_ = Pattern._≟s_
{-# WARNING_ON_USAGE _≟-ArgPatterns_
"Warning: _≟-ArgPatterns_ was deprecated in v1.1.
Please use Reflection.Pattern's _≟s_ instead."
#-}

showLiteral = Literal.show
{-# WARNING_ON_USAGE showLiteral
"Warning: showLiteral was deprecated in v1.1.
Please use Reflection.Literal's show instead."
#-}

showName = Name.show
{-# WARNING_ON_USAGE showName
"Warning: showName was deprecated in v1.1.
Please use Reflection.Name's show instead."
#-}

showMeta = Meta.show
{-# WARNING_ON_USAGE showMeta
"Warning: showMeta was deprecated in v1.1.
Please use Reflection.Meta's show instead."
#-}

map-Abs = Abstraction.map
{-# WARNING_ON_USAGE map-Abs
"Warning: map-Abs was deprecated in v1.1.
Please use Reflection.Abstraction's map instead."
#-}

map-Arg = Argument.map
{-# WARNING_ON_USAGE map-Arg
"Warning: map-Arg was deprecated in v1.1.
Please use Reflection.Argument's map instead."
#-}

map-Args = Argument.map-Args
{-# WARNING_ON_USAGE map-Args
"Warning: map-Args was deprecated in v1.1.
Please use Reflection.Argument's map-Args instead."
#-}

visibility = Information.visibility
{-# WARNING_ON_USAGE visibility
"Warning: visibility was deprecated in v1.1.
Please use Reflection.Argument.Information's visibility instead."
#-}

relevance = Information.relevance
{-# WARNING_ON_USAGE relevance
"Warning: relevance was deprecated in v1.1.
Please use Reflection.Argument.Information's relevance instead."
#-}
