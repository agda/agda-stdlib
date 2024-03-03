------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED, please use `Function.Strict` directly.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Strict where

{-# WARNING_ON_IMPORT
"Strict was deprecated in v1.8.
Use `Function.Strict instead (also re-exported by `Function`)."
#-}

open import Function.Strict public
  using
  ( force ; force-≡ ; force′ ; force′-≡
  ; seq   ; seq-≡
  )
