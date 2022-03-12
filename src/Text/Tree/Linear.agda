------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use the Data.Tree.Rose.Show module
-- directly
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Text.Tree.Linear where

open import Data.Tree.Rose.Show public using (display)

{-# WARNING_ON_IMPORT
"Text.Tree.Linear was deprecated in v1.6. Use Data.Tree.Rose.Show instead."
#-}
