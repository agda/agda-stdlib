------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for Conats
------------------------------------------------------------------------

module Codata.Conat.Properties where

open import Data.Nat
open import Codata.Thunk
open import Codata.Conat
open import Codata.Conat.Bisimilarity

0ℕ+-identity : ∀ {i n} → i ⊢ 0 ℕ+ n ≈ n
0ℕ+-identity = refl

+ℕ0-identity : ∀ {i n} → i ⊢ n +ℕ 0 ≈ n
+ℕ0-identity {n = zero}  = zero
+ℕ0-identity {n = suc n} = suc λ where .force → +ℕ0-identity
