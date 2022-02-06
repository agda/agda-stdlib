------------------------------------------------------------------------
-- The Agda standard library
--
-- ≤-pred definition so as to not cause dependency problems.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Properties.Core where

{-# WARNING_ON_IMPORT
"Data.Nat.Properties.Core was deprecated in v2.0.
Use Data.Nat.Properties instead."
#-}

open import Data.Nat.Base

------------------------------------------------------------------------
-- Properties of _≤_
------------------------------------------------------------------------

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s m≤n) = m≤n

