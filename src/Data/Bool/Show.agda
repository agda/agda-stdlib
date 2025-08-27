------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing booleans
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Bool.Show where

open import Data.Bool.Base using (Bool; false; true)
open import Data.Char.Base using (Char)
open import Data.String.Base using (String)

show : Bool → String
show true  = "true"
show false = "false"

showBit : Bool → Char
showBit true = '1'
showBit false = '0'
