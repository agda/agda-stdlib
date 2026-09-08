------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing signs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sign.Show where

open import Data.Sign.Base using (Sign; +; -)
open import Data.String.Base using (String)

show : Sign → String
show + = "+"
show - = "-"
