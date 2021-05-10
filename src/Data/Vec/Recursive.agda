------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined by recursion
------------------------------------------------------------------------

-- What is the point of this module? The n-ary products below are
-- intended to be used with a fixed n, in which case the nil constructor
-- can be avoided: pairs are represented as pairs (x , y), not as
-- triples (x , y , unit).
--
-- Additionally, vectors defined by recursion enjoy η-rules. That is to
-- say that two vectors of known length are definitionally equal whenever
-- their elements are.

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Recursive where

open import Level using (Level; lift)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Product as Prod using (_,_)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Unary

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Re-export contents of Base publicly

open import Data.Vec.Recursive.Base public

------------------------------------------------------------------------
-- Conversion

fromVec : ∀[ Vec A ⇒ (A ^_) ]
fromVec = Vec.foldr (_ ^_) (cons _) _

toVec : Π[ (A ^_) ⇒ Vec A ]
toVec 0       xs = Vec.[]
toVec (suc n) xs = Vec.[ xs ]
