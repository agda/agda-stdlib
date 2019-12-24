------------------------------------------------------------------------
-- The Agda standard library
--
-- A simple example of a program using the foreign function interface
------------------------------------------------------------------------

module README.Foreign.Haskell where

-- In order to be considered safe by Agda, the standard library cannot
-- add COMPILE pragmas binding the inductive types it defines to concrete
-- Haskell types.

-- To work around this limitation, we have defined FFI-friendly versions
-- of these types together with a zero-cost coercion `coerce`.

open import Level using (Level)
open import Agda.Builtin.Int
open import Agda.Builtin.Nat
open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Char as Char
open import Data.List.Base as List using (List; _∷_; []; takeWhile; dropWhile)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product
open import Function
open import Relation.Nullary.Decidable

import Foreign.Haskell as FFI
open import Foreign.Haskell.Coerce

private
  variable
    a : Level
    A : Set a

-- Here we use the FFI version of Maybe and Pair.

postulate
  primUncons    : List A → FFI.Maybe (FFI.Pair A (List A))
  primCatMaybes : List (FFI.Maybe A) → List A
  primTestChar  : Char → Bool
  primIntEq     : Int → Int → Bool

{-# COMPILE GHC primUncons = \ _ _ xs -> case xs of
  { []       -> Nothing
  ; (x : xs) -> Just (x, xs)
  }
#-}

{-# FOREIGN GHC import Data.Maybe #-}
{-# COMPILE GHC primCatMaybes = \ _ _ -> catMaybes #-}

{-# COMPILE GHC primTestChar = ('-' /=) #-}

{-# COMPILE GHC primIntEq = (==) #-}

-- We however want to use the notion of Maybe and Pair internal to
-- the standard library. For this we use `coerce` to take use back
-- to the types we are used to.

-- The typeclass mechanism uses the coercion rules for Maybe and Pair,
-- as well as the knowledge that natural numbers are represented as
-- integers.
-- We additionally benefit from the congruence rules for List, Char,
-- Bool, and a reflexivity principle for variable A.

uncons : List A → Maybe (A × List A)
uncons = coerce primUncons

catMaybes : List (Maybe A) → List A
catMaybes = coerce primCatMaybes

testChar : Char → Bool
testChar = coerce primTestChar
  -- note that coerce is useless here but the proof could come from
  -- either `coerce-fun coerce-refl coerce-refl` or `coerce-refl` alone
  -- We (and Agda) do not care which proof we got.

eqNat : Nat → Nat → Bool
eqNat = coerce primIntEq
  -- We can coerce `Nat` to `Int` but not `Int` to `Nat`. This fundamentally
  -- relies on the fact that `Coercible` understands that functions are
  -- contravariant.

open import IO
open import Codata.Musical.Notation
open import Data.String.Base
open import Relation.Nullary.Negation

-- example program using uncons, catMaybes, and testChar

main = run $
  ♯ readFiniteFile "README/Foreign/Haskell.agda" {- read this file -} >>= λ f →
  ♯ let chars   = toList f in
    let cleanup = catMaybes ∘ List.map (λ c → if testChar c then just c else nothing) in
    let cleaned = dropWhile ('\n' ≟_) $ cleanup chars in
  case uncons cleaned of λ where
    nothing         → putStrLn "I cannot believe this file is filed with dashes only!"
    (just (c , cs)) → putStrLn $ unlines
                    $ ("First (non dash) character: " ++ Char.show c)
                    ∷ ("Rest (dash free) of the line: " ++ fromList (takeWhile (¬? ∘ ('\n' ≟_)) cs))
                    ∷ []

-- You can compile and run this test by writing:
-- agda -c Haskell.agda
-- ../../Haskell

-- You should see the following text (without the indentation on the left):
--   First (non dash) character: ' '
--   Rest (dash free) of the line: The Agda standard library
