------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED, please use `Data.Record` directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Strict where

{-# WARNING_ON_IMPORT
"Strict was deprecated in v1.8.
Use Function.Strict instead."
#-}

open import Function.Strict public
  using
  ( force ; force-≡ ; force′ ; force′-≡
  ; seq   ; seq-≡
  )
