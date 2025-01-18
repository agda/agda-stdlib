------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use IO.Primitive.Core instead
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module IO.Primitive where

open import IO.Primitive.Core public

{-# WARNING_ON_IMPORT
"IO.Primitive was deprecated in v2.1. Use IO.Primitive.Core instead."
#-}
