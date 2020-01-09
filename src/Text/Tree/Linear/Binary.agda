------------------------------------------------------------------------
-- The Agda standard library
--
-- Binary Trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Text.Tree.Linear.Binary where

open import Data.List.Base using (List; [_])
open import Data.Maybe.Base
open import Data.String.Base using (String)
import Text.Tree.Linear as Linear
open import Data.Tree.Binary as Binary
open import Data.Tree.Rose as Rose
open import Function.Base

display : Tree (List String) → List String
display = Linear.display
        ∘ Rose.map (fromMaybe [ "∙" ])
        ∘ toRose
