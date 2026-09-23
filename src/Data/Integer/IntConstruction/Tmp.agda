------------------------------------------------------------------------
-- The Agda standard library
--
-- To be merged into Data.Integer.Base before merging!
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Integer.IntConstruction.Tmp where

open import Data.Integer.Base
import Data.Integer.IntConstruction as INT
import Data.Nat.Base as ℕ

fromINT : INT.ℤ → ℤ
fromINT (m INT.⊖ n) = m ⊖ n

toINT : ℤ → INT.ℤ
toINT (+ n) = n INT.⊖ 0
toINT (-[1+ n ]) = 0 INT.⊖ ℕ.suc n

-- here we have a choice:
-- * either we can show the definitions in Data.Int.Base match those on INT under the above isomorphism;
-- * or we could _redefine_ those operations _as_ the operations on INT under the above isormophism.
