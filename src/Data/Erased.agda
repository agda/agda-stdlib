------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Erased where

{-# WARNING_ON_IMPORT
"Data.Erased was deprecated in v2.0.
Use Data.Irrelevant instead."
#-}

open import Data.Irrelevant public
  using ([_]; map; pure; _<*>_; _>>=_; zipWith)
  renaming
  ( Irrelevant to Erased
  ; irrelevant to erased
  )
