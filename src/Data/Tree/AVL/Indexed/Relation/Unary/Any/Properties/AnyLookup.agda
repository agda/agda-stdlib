------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Any.lookup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AnyLookup
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base as Prod using (_,_)
open import Function.Base using (flip)
open import Level using (Level)
open import Relation.Unary using (Pred; _∩_)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any

private
  variable
    v p : Level
    V : Value v
    l u : Key⁺
    n : ℕ
    P Q : Pred (K& V) p

lookup-result : {t : Tree V l u n} (p : Any P t) → P (Any.lookup p)
lookup-result (here p)  = p
lookup-result (left p)  = lookup-result p
lookup-result (right p) = lookup-result p

lookup-bounded : {t : Tree V l u n} (p : Any P t) → l < Any.lookup p .key < u
lookup-bounded {t = node kv lk ku bal} (here p)  = ordered lk , ordered ku
lookup-bounded {t = node kv lk ku bal} (left p)  =
  Prod.map₂ (flip (trans⁺ _) (ordered ku)) (lookup-bounded p)
lookup-bounded {t = node kv lk ku bal} (right p) =
  Prod.map₁ (trans⁺ _ (ordered lk)) (lookup-bounded p)

lookup-rebuild : {t : Tree V l u n} (p : Any P t) → Q (Any.lookup p) → Any Q t
lookup-rebuild (here _)  q = here q
lookup-rebuild (left p)  q = left (lookup-rebuild p q)
lookup-rebuild (right p) q = right (lookup-rebuild p q)

lookup-rebuild-accum : {t : Tree V l u n} (p : Any P t) → Q (Any.lookup p) → Any (Q ∩ P) t
lookup-rebuild-accum p q = lookup-rebuild p (q , lookup-result p)
