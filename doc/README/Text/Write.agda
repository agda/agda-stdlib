------------------------------------------------------------------------
-- The Agda standard library
--
-- Using and creating instances of the Write class
------------------------------------------------------------------------

open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- The Write class defines an interface for types whose values
-- can be converted into a string. In most cases, especially
-- in which a Text.Read instance (and further, a Text.ReadWrite instance),
-- this string is valid Agda syntax for that value.

-- The Write class, alongside some utility functions, are exported by
open import Text.Write
open Write {{...}}

-- The interface is given by a record, Write, with one field:
--
-- writesPrecList : Precedence → A → List Char → List Char
--
-- and some derived functions:
--
-- writePrecList : Precedence → A → List Char
-- writesPrec    : Precedence → A → String → String
-- writePrec     : Precedence → A → String
-- write         : A → String
-- writeMaybe    : Maybe A → String

-- Any function with 's' after write means it takes in an additional
-- List Char or String and appends it to the end of its result. This
-- allows for often faster implementations than concatenating
-- several results together.

-- Any function with Prec in the name takes in a Precedence value.
-- This is intended to be the Precedence of the operator or function
-- that is applied to the value being written.
--
-- For example, suppose I want to convert a List A to a String, I would need
-- to have ' ∷ ' placed between string representations of each A in the list
-- The fixity of _∷_ specifies its Precedence as 'related 5.0', so calls to
-- writesPrecList on each A would be given 'related 5.0' as its first argument.
--
-- The given instance for Write A can then determine whether or not to surround
-- its result in brackets (or some similar syntax) based on its own fixity.

-- Precedence itself is exported by Reflection.AST.Fixity, and then
-- re-exported by Text.Write. Reflection.AST.Fixity includes some other
-- functions and relations on Precedence:

open import Reflection.AST.Fixity using
  ( _≤ᵇ_ -- Boolean partial order
  ; _≤_  -- Partial order
  )

-- Instances of Write for a particular type are defined within that type's
-- 'Instances' sub-module, for example:

open import Data.Nat.Instances using (NatWrite)
open import Data.List.Instances using (ListWrite)

string-[ℕ] : (write (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])) ≡ "(0 ∷ 1 ∷ 2 ∷ 3 ∷ [])"
string-[ℕ] = refl

string-ℕ : (write 123456789) ≡ "123456789"
string-ℕ = refl

------------------------------------------------------------------------
-- Creating instances of Write

-- suppose a new data type (that looks suspicously like ℕ)

data not-ℕ : Set where
  z : not-ℕ
  s  : not-ℕ → not-ℕ

-- To declare a Write instasnce for this type, we must define
-- a value of type `Write not-ℕ` within an `instance` block:

instance
  not-ℕ-Write : Write not-ℕ
  not-ℕ-Write .Write.writesPrecList prec z str = 'z' ∷ str
  not-ℕ-Write .Write.writesPrecList prec (s x) str = 's' ∷ ' ' ∷ '(' ∷ writesPrecList prec x (')' ∷ str)

-- And now to test its output:
string-not-ℕ : (write (s (s (s (s (z)))))) ≡
                      "s (s (s (s (z))))"
string-not-ℕ = refl

-- Instances can also be derived using Reflection, provided by
open import Text.Write.Deriving using (deriveWrite)

data not-List (A : Set) : Set where
  empty : not-List A
  _cons_ : A → not-List A → not-List A

-- unquoteDecl has to be used to allow the function to introduce new definitions and declarations
-- and the type for which Write is being derived for must be quoted
instance
  unquoteDecl not-ListWrite = deriveWrite not-ListWrite (quote not-List)

string-not-List[not-ℕ] : String
string-not-List[not-ℕ] = write (z cons empty)

-- Or, if you want, you can use the syntax x derives Write as y:

data not-Maybe (A : Set) : Set where
  void : not-Maybe A
  something : A → not-Maybe A

instance
  unquoteDecl not-MaybeWrite = (quote not-Maybe) derives Write as not-MaybeWrite
