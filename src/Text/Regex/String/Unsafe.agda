------------------------------------------------------------------------
-- The Agda standard library
--
-- Regular expressions acting on strings, using unsafe features
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Text.Regex.String.Unsafe where

open import Data.String.Base using (String; toList; fromList)
import Data.String.Unsafe as Stringₚ
open import Function.Base using (_on_; id)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import Relation.Nullary.Decidable using (map′)

------------------------------------------------------------------------
-- Re-exporting safe definitions

open import Text.Regex.String as Regex public
  hiding (_∈_; _∉_; _∈?_; _∉?_; Span; Match; search)

------------------------------------------------------------------------
-- Specialised definitions

_∈_ : String → Exp → Set
str ∈ e = toList str Regex.∈ e

_∉_ : String → Exp → Set
str ∉ e = toList str Regex.∉ e

_∈?_ : Decidable _∈_
str ∈? e = toList str Regex.∈? e

_∉?_ : Decidable _∉_
str ∉? e = toList str Regex.∉? e

Span : Regex → Rel String 0ℓ
Span e = Regex.Span e _≡_ on toList

-- A match is a string, a proof it matches the regular expression,
-- and a proof it appears as the right sort of substring.
record Match (str : String) (e : Regex) : Set where
  constructor mkMatch
  field
    string  : String
    match   : string ∈ Regex.expression e
    related : Span e string str
open Match public

search : Decidable Match
search str e = map′ from to (Regex.search input e) where

  input = toList str
  exp = Regex.expression e

  from : Regex.Match (Regex.Span e _≡_) input exp → Match str e
  from (Regex.mkMatch list match related) =
    let eq = sym (Stringₚ.toList∘fromList list) in
    mkMatch (fromList list)
            (subst (Regex._∈ exp) eq match)
            (subst (λ str → Regex.Span e _≡_ str input) eq related)

  to : Match str e → Regex.Match (Regex.Span e _≡_) input exp
  to (mkMatch string match related) =
    Regex.mkMatch (toList string) match related
