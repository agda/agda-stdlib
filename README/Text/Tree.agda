------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples of pretty printing of rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module README.Text.Tree where

open import Level
open import Data.List.Base
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.String.Base using (String; unlines)
open import Data.Tree.Binary using (Tree; leaf; node)
open import Data.Tree.Rose using (Rose; node)
open import Function.Base
open import Agda.Builtin.Equality

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Pretty-printing rose trees

-- We import the module defining the pretty printer for rose trees

import Text.Tree.Linear as Linear

------------------------------------------------------------------------
-- Example

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
-- Pretty-printing other trees

-- To print any other tree, we can simply embed them into rose trees.
-- We need to be careful about respecting the structure of the tree
-- rather than trying to minimize the size of the representation.

-- For instance, the following example is wrong because leaf are not
-- mapped to anything so will not get printed.

module BUGGY where

  toRose : Tree A → Maybe (Rose A _)
  toRose leaf         = nothing
  toRose (node l a r) = just (node a (lt ++ rt)) where
    lt = fromMaybe (toRose l)
    rt = fromMaybe (toRose r)

-- Instead we should use the function defined in Data.Tree.Binary:

module CORRECT where

  toRose : Tree A → Rose (Maybe A) _
  toRose leaf         = node nothing []
  toRose (node l a r) = node (just a) (toRose l ∷ toRose r ∷ [])

-- This is exactly what we do in the following module:

import Text.Tree.Linear.Binary as Linearᴮ

------------------------------------------------------------------------
-- Example

_ : unlines (Linearᴮ.display
  $ node (node leaf
               ("apricot" ∷ "prune" ∷ [])
               (node leaf
                     ("peach" ∷ [])
                     (node leaf
                           ("apple" ∷ "pear" ∷ [])
                           leaf)))
         ("cherry" ∷ "lemon" ∷ "banana" ∷ [])
         leaf)
  ≡ "cherry
\   \lemon
\   \banana
\   \ ├ apricot
\   \ │ prune
\   \ │  ├ ∙
\   \ │  └ peach
\   \ │     ├ ∙
\   \ │     └ apple
\   \ │       pear
\   \ │        ├ ∙
\   \ │        └ ∙
\   \ └ ∙"
_ = refl
