------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Tree.AVL.Indexed.Relation.Unary.Any.AnyLookup sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Cast sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Delete sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.HeadTail sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Insert sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.JoinConstFuns sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Join sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Lookup sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Singleton sto public
