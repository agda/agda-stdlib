------------------------------------------------------------------------
-- The Agda standard library
--
-- Support for reflection
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection where

------------------------------------------------------------------------
-- Re-export contents publicly

open import Reflection.AST public
open import Reflection.TCM public
open import Reflection.TCM.Syntax public
  using (_>>=_; _>>_)
