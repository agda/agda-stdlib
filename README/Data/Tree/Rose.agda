------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing how the Rose tree module can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module README.Data.Tree.Rose where

open import Data.List.Base
open import Data.String.Base using (String; unlines)
open import Data.Tree.Rose using (Rose; node)
open import Function.Base
open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- Pretty-printing

open import Data.Tree.Rose.Show using (display)

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
