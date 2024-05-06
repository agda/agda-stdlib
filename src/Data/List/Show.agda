------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Show where

open import Data.List.Base using (List; map)
open import Data.String.Base using (String; between; intersperse)
open import Function.Base using (_∘_)

show : ∀ {a} {A : Set a} → (A → String) → (List A → String)
show s = between "[" "]" ∘ intersperse ", " ∘ map s
