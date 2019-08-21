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
-- of these types together with zero-cost coercions

open import Level using (Level)
open import Data.List.Base using (List; _∷_; []; takeWhile)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product
open import Function

import Foreign.Haskell as FFI
open import Foreign.Haskell.Coerce

private
  variable
    a : Level
    A : Set a

-- Here we use the FFI version of Maybe and Pair

postulate primUncons : List A → FFI.Maybe (FFI.Pair A (List A))

{-# COMPILE GHC primUncons = \ _ _ xs -> case xs of
  { []       -> Nothing
  ; (x : xs) -> Just (x, xs)
  }
#-}

-- And `coerce` takes us back to the types we are used to

uncons : List A → Maybe (A × List A)
uncons = coerce primUncons

open import IO
open import Codata.Musical.Notation
open import Data.Char as Char
open import Data.String.Base
open import Relation.Nullary.Negation

-- example program using uncons

main = run $
  ♯ readFiniteFile "Haskell.agda" {- read this file -} >>= λ f →
  ♯ let cs = toList f in
  case uncons cs of λ where
    nothing         → putStrLn "I cannot believe this file is empty!"
    (just (c , cs)) → putStrLn $ unlines
                    $ ("First character: " ++ Char.show c)
                    ∷ ("Rest of the line: " ++ fromList (takeWhile (¬? ∘ ('\n' ≟_)) cs))
                    ∷ []

-- You can compile and run this test by writing:
-- agda -c Haskell.agda
-- ../../Haskell

-- You should see the following text (without the indentation on the left):
--   First character: '-'
--   Rest of the line: -----------------------------------------------------------------------
