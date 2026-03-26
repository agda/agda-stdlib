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

open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Lookup sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Cast sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Delete sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.HeadTail sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Insert sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.JoinConstFuns sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Join sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.LookupFun sto public
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Singleton sto public
