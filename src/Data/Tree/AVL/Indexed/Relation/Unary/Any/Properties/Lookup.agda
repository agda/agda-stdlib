------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Any.lookup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Lookup
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base as Prod using (_,_)
open import Function.Base using (flip)
open import Level using (Level)
open import Relation.Unary using (Pred; _∩_)

open import Data.Tree.AVL.Indexed sto hiding (lookup)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto

private
  variable
    v p : Level
    V : Value v
    l u : Key⁺
    h : ℕ
    P Q : Pred (K& V) p
    t : Tree V l u h


lookup-result : (p : Any P t) → P (lookup p)
lookup-result (here p)  = p
lookup-result (left p)  = lookup-result p
lookup-result (right p) = lookup-result p

lookup-bounded : (p : Any P {l = l} {u = u} t) → l < lookupKey p < u
lookup-bounded {t = node kv lk ku bal} (here p)  = ordered lk , ordered ku
lookup-bounded {t = node kv lk ku bal} (left p)  =
  Prod.map₂ (flip (trans⁺ _) (ordered ku)) (lookup-bounded p)
lookup-bounded {t = node kv lk ku bal} (right p) =
  Prod.map₁ (trans⁺ _ (ordered lk)) (lookup-bounded p)

lookup-rebuild : (p : Any P t) → Q (lookup p) → Any Q t
lookup-rebuild (here _)  q = here q
lookup-rebuild (left p)  q = left (lookup-rebuild p q)
lookup-rebuild (right p) q = right (lookup-rebuild p q)

lookup-rebuild-accum : (p : Any P t) → Q (lookup p) → Any (Q ∩ P) t
lookup-rebuild-accum p q = lookup-rebuild p (q , lookup-result p)
