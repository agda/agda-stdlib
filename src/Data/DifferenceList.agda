------------------------------------------------------------------------
-- The Agda standard library
--
-- A DiffList is a List with fast append.
-- Based on Hughes' 'A NOVEL REPRESENTATION OF LISTS AND ITS APPLICATION
-- TO THE FUNCTION "REVERSE"'
-- DiffList is the Cayley representation for the List.++ monoid.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.DifferenceList where

open import Data.DifferenceList.Base public
open import Data.DifferenceList.Properties public
