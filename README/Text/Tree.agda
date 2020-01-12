------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of pretty printing of rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module README.Text.Tree where

open import Data.List.Base
open import Data.String.Base
open import Data.Tree.Rose
open import Function.Base
open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- We import the module defining the pretty printer for rose trees

open import Text.Tree.Linear

------------------------------------------------------------------------
-- Example

_ : unlines (display
  $ node [ "one" ]
      (node [ "two" ] []
     ∷ node ("three" ∷ "and" ∷ "four" ∷ [])
         (node [ "five" ] []
        ∷ node [ "six" ] (node [ "seven" ] [] ∷ [])
        ∷ node [ "eight" ] []
        ∷ [])
     ∷ node [ "nine" ]
         (node [ "ten" ] []
        ∷ node [ "eleven" ] [] ∷ [])
        ∷ []))
  ≡ "one
\   \ ├ two
\   \ ├ three
\   \ │ and
\   \ │ four
\   \ │  ├ five
\   \ │  ├ six
\   \ │  │  └ seven
\   \ │  └ eight
\   \ └ nine
\   \    ├ ten
\   \    └ eleven"
_ = refl
