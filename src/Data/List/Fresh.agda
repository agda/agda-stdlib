------------------------------------------------------------------------
-- The Agda standard library
--
-- Fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh where

open import Level
open import Data.Unit.Base
open import Data.Product
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Relation.Binary.Core

private
  variable
    a b r : Level
    A : Set a
    B : Set b
    R : Rel A r

------------------------------------------------------------------------
-- Basic type

-- If we pick an R such that (R a b) means that a is different from b
-- then we have a list of distinct values.

module _ {a} (A : Set a) (R : Rel A r) where

  data List# : Set (a ⊔ r)
  fresh : (a : A) (as : List#) → Set r

  data List# where
    []   : List#
    cons : (a : A) (as : List#) → fresh a as → List#

  -- Whenever R can be reconstructed by η-expansion (e.g. because it is
  -- the erasure ⌊_⌋ of a decidable predicate, cf. Relation.Nary) or we
  -- do not care about the proof, it is convenient to get back list syntax.

  -- We use a different symbol to avoid conflict when importing both Data.List
  -- and Data.List.Fresh.
  infixr 5 _∷#_
  pattern _∷#_ x xs = cons x xs _

  fresh a []        = Lift _ ⊤
  fresh a (x ∷# xs) = R a x × fresh a xs

-- Convenient notation for freshness making A and R implicit parameters
infix 5 _#_
_#_ : {R : Rel A r} (a : A) (as : List# A R) → Set r
_#_ = fresh _ _

------------------------------------------------------------------------
-- Relationship to List and AllPairs

toList : List# A R → ∃ (AllPairs R)
toAll  : ∀ {a} as → fresh A R a as → All (R a) (proj₁ (toList as))

toList []             = -, []
toList (cons x xs ps) = -, toAll xs ps ∷ proj₂ (toList xs)

toAll []            ps       = []
toAll (cons a as _) (p , ps) = p ∷ toAll as ps
