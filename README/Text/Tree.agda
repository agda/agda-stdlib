------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of pretty printing of rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module README.Text.Tree where

open import Data.List.Base
open import Data.String.Base using (String; unlines)
open import Function.Base
open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- Pretty-printing trees
------------------------------------------------------------------------

-- We import the module defining the pretty printer for trees

import Text.Tree.Linear as Linear

------------------------------------------------------------------------
-- Rose tree example

open import Data.Tree.Rose using (Rose; node)

_ : unlines (Linear.display
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

------------------------------------------------------------------------
-- Binary tree example

open import Data.Tree.Binary using (Tree; leaf; node)

_ : unlines (Linear.displayBinary
  $ node (node (leaf "plum")
               ("apricot" ∷ "prune" ∷ [])
               (node (leaf "orange")
                     ("peach" ∷ [])
                     (node (leaf "kiwi")
                           ("apple" ∷ "pear" ∷ [])
                           (leaf "pineapple"))))
         ("cherry" ∷ "lemon" ∷ "banana" ∷ [])
         (leaf "yuzu"))
  ≡ "cherry
\   \lemon
\   \banana
\   \ ├ apricot
\   \ │ prune
\   \ │  ├ plum
\   \ │  └ peach
\   \ │     ├ orange
\   \ │     └ apple
\   \ │       pear
\   \ │        ├ kiwi
\   \ │        └ pineapple
\   \ └ yuzu"
_ = refl
