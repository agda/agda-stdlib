------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists
------------------------------------------------------------------------

-- See README.Data.List for examples of how to use and reason about
-- lists.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List where

import Data.List.NonEmpty.Base as List⁺
open import Function.Base using (_∘_)

------------------------------------------------------------------------
-- Types and basic operations

open import Data.List.Base public hiding (scanr)

------------------------------------------------------------------------
-- scanr

module _ {a b} {A : Set a} {B : Set b} (f : A → B → B) (e : B) where

  open List⁺ using (toList; scanr⁺)

-- definition

  scanr : List A → List B
  scanr = toList ∘ scanr⁺ f e

{-
-- which satisfies the following property:

  scanr-defn : scanr ≗ map (foldr f e) ∘ tails
  scanr-defn = Data.List.NonEmpty.Properties.toList-scanr⁺
-}

