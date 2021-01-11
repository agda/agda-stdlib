------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of regular expressions and matching
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module README.Text.Regex where

open import Data.Bool using (true; false)
open import Data.List using (_∷_; [])
open import Data.String
open import Function.Base using () renaming (_$′_ to _$_)
open import Relation.Nullary using (yes)
open import Relation.Nullary.Decidable using (True; False; from-yes)

-- Our library available via the Text.Regex module is safe but it works on
-- lists of characters.

-- To use it on strings we have to rely on unsafe theorems about the
-- conversions between strings and lists of characters being inverses.
-- For convenience we use the following unsafe module for this README.
open import Text.Regex.String.Unsafe

------------------------------------------------------------------------
-- Defining regular expressions

-- The type of regular expressions is Exp.

-- Some examples of regular expressions using:

-- [_]        for the union of ranges it contains
-- _─_        for a range
-- singleton  for an exact character
-- _∙_        for the concatenation of two regular expressions
-- _∣_        for the sum of two regular expressions
-- _⋆         for the Kleene star (zero or more matches of the regular expression)
-- _⁇         for an optional regular expression

ℕ* : Exp
ℕ* = [ '1' ─ '9' ∷ [] ]   -- a non-zero digit
   ∙ [ '0' ─ '9' ∷ [] ] ⋆ -- followed by zero or more digits

ℕ : Exp
ℕ = ℕ* ∣ singleton '0' -- ℕ* or exactly 0

ℤ : Exp
ℤ = ((singleton '-') ⁇ ∙ ℕ*) -- an optional minus sign followed by a ℕ*
  ∣ singleton '0'            -- or exactly 0

------------------------------------------------------------------------
-- An expression's semantics

-- The semantics of these regular expression is defined in terms of the
-- lists of characters they match. The type (str ∈ e) states that the
-- string str matches the expression e.

-- It is decidable, and the proof is called _∈?_.
-- We can run it on a few examples to check that it matches our intuition:

-- Valid: starts with a non-zero digit, followed by 3 digits
_ : True ("1848" ∈? ℕ*)
_ = _

-- Valid: exactly 0
_ : True ("0" ∈? ℕ)
_ = _

-- Invalid: starts with a leading 0
_ : False ("007" ∈? ℕ)
_ = _

-- Invalid: no negative ℕ number
_ : False ("-666" ∈? ℕ)
_ = _

-- Valid: a negative integer
_ : True ("-666" ∈? ℤ)
_ = _

-- Invalid: no negative 0
_ : False ("-0" ∈? ℤ)
_ = _

------------------------------------------------------------------------
-- Matching algorithms

-- The proof that _∈_ is decidable gives us the ability to check whether
-- a whole string matches a regular expression. But we may want to use
-- other matching algorithms detecting a prefix, infix, or suffix of the
-- input string that matches the regular expression.

-- This is what the Regex type gives us.

-- For instance, the following value corresponds to finding an infix
-- substring matching the string "agda" or "agdai"

agda : Exp
agda = singleton 'a'
     ∙ singleton 'g'
     ∙ singleton 'd'
     ∙ singleton 'a'
     ∙ (singleton 'i' ⁇)

infixAgda : Regex
infixAgda = record
  { fromStart  = false
  ; tillEnd    = false
  ; expression = agda
  }

-- The search function gives us the ability to look for matches

-- Valid: agda in the middle
_ : True (search "Maria Magdalena" infixAgda)
_ = _

-- By changing the value of fromStart and tillEnd we can control where the
-- substring should be. We can insist on the match being at the end of the
-- input for instance:

suffixAgda : Regex
suffixAgda = record
  { fromStart  = false
  ; tillEnd    = true
  ; expression = agda
  }

-- Invalid: agda is in the middle
_ : False (search "Maria Magdalena" suffixAgda)
_ = _

-- Valid: agda as a suffix
_ : True (search "README.agda" suffixAgda)
_ = _

-- Valid: agdai as a suffix
_ : True (search "README.agdai" suffixAgda)
_ = _


------------------------------------------------------------------------
-- Advanced uses

-- Search does not just return a boolean, it returns an informative answer.
-- Infix matches are for instance represented using the `Infix` relation on
-- list. Such a proof pinpoints the exact position of the match:

open import Data.List.Relation.Binary.Infix.Heterogeneous
open import Data.List.Relation.Binary.Infix.Heterogeneous.Properties
open import Data.List.Relation.Binary.Pointwise using (≡⇒Pointwise-≡)
open import Relation.Binary.PropositionalEquality

-- Here is an example of a match: it gives back the substring, the inductive
-- proof that it is accepted by the regular expression and its precise location
-- inside the input string
mariamAGDAlena : Match "Maria Magdalena" infixAgda
mariamAGDAlena = record
  { string  = "agda"                     -- we have found "agda"
  ; match   = from-yes ("agda" ∈? agda)  -- a proof of the match
  ; related = proof                      -- and its location
  }

  where

    proof : Infix _≡_ (toList "agda") (toList "Maria Magdalena")
    proof = toList "Maria M"
        ++ⁱ fromPointwise (≡⇒Pointwise-≡ refl)
        ⁱ++ toList "lena"


-- And here is the proof that search returns such an object
_ : search "Maria Magdalena" infixAgda ≡ yes mariamAGDAlena
_ = refl
