------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing how the Binary tree module can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module README.Data.Tree.Binary where

open import Data.List.Base
open import Data.String.Base using (String; unlines)
open import Data.Tree.Binary using (Tree; leaf; node)
open import Function.Base
open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- Pretty-printing

open import Data.Tree.Binary.Show using (display)

_ : unlines (display
  $ node (node (leaf [ "plum" ])
               ("apricot" ∷ "prune" ∷ [])
               (node (leaf [ "orange" ])
                     ("peach" ∷ [])
                     (node (leaf [ "kiwi" ])
                           ("apple" ∷ "pear" ∷ [])
                           (leaf [ "pineapple" ]))))
         ("cherry" ∷ "lemon" ∷ "banana" ∷ [])
         (leaf [ "yuzu" ]))
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
