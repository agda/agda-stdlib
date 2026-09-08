------------------------------------------------------------------------
-- The Agda standard library
--
-- Regular expressions acting on strings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Regex.String where

import Data.Char.Properties as Char

------------------------------------------------------------------------
-- Re-exporting definitions

open import Text.Regex Char.≤-decPoset public
