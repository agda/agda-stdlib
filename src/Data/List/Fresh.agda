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
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function using (_∘′_; flip)
open import Relation.Nullary      using (yes; no)
open import Relation.Unary   as U using (Pred)
open import Relation.Binary  as B using (Rel)
open import Relation.Nary

private
  variable
    a b p r : Level
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
-- Operations for constructing fresh lists

pattern [_] a = a ∷# []

fromMaybe : Maybe A → List# A R
fromMaybe nothing  = []
fromMaybe (just a) = [ a ]

module _ {R : Rel A r} (R-refl : B.Reflexive R) where

  replicate   : ℕ → A → List# A R
  replicate-# : (n : ℕ) (a : A) → a # replicate n a

  replicate zero    a = []
  replicate (suc n) a = cons a (replicate n a) (replicate-# n a)

  replicate-# zero    a = _
  replicate-# (suc n) a = R-refl , replicate-# n a

------------------------------------------------------------------------
-- Operations for deconstructing fresh lists

uncons : List# A R → Maybe (A × List# A R)
uncons []        = nothing
uncons (a ∷# as) = just (a , as)

head : List# A R → Maybe A
head = Maybe.map proj₁ ∘′ uncons

tail : List# A R → Maybe (List# A R)
tail = Maybe.map proj₂ ∘′ uncons

take   : ℕ → List# A R → List# A R
take-# : ∀ (n : ℕ) a (as : List# A R) → a # as → a # take n as

take zero    xs             = []
take (suc n) []             = []
take (suc n) (cons a as ps) = cons a (take n as) (take-# n a as ps)

take-# zero    a xs        _        = _
take-# (suc n) a []        ps       = _
take-# (suc n) a (x ∷# xs) (p , ps) = p , take-# n a xs ps

drop : ℕ → List# A R → List# A R
drop zero    as        = as
drop (suc n) []        = []
drop (suc n) (a ∷# as) = drop n as

module _ {P : Pred A p} (P? : U.Decidable P) where

  takeWhile   : List# A R → List# A R
  takeWhile-# : ∀ a (as : List# A R) → a # as → a # takeWhile as

  takeWhile []             = []
  takeWhile (cons a as ps) with P? a
  ... | yes _ = cons a (takeWhile as) (takeWhile-# a as ps)
  ... | no _  = []

  takeWhile-# a []        _        = _
  takeWhile-# a (x ∷# xs) (p , ps) with P? x
  ... | yes _ = p , takeWhile-# a xs ps
  ... | no _  = _

  dropWhile : List# A R → List# A R
  dropWhile []            = []
  dropWhile aas@(a ∷# as) with P? a
  ... | yes _ = dropWhile as
  ... | no _  = aas

  filter   : List# A R → List# A R
  filter-# : ∀ a (as : List# A R) → a # as → a # filter as

  filter []             = []
  filter (cons a as ps) with P? a
  ... | yes _ = cons a (filter as) (filter-# a as ps)
  ... | no _  = filter as

  filter-# a []        _        = _
  filter-# a (x ∷# xs) (p , ps) with P? x
  ... | yes _ = p , filter-# a xs ps
  ... | no _  = filter-# a xs ps

------------------------------------------------------------------------
-- Relationship to List and AllPairs

toList : List# A R → ∃ (AllPairs R)
toAll  : ∀ {a} as → fresh A R a as → All (R a) (proj₁ (toList as))

toList []             = -, []
toList (cons x xs ps) = -, toAll xs ps ∷ proj₂ (toList xs)

toAll []            ps       = []
toAll (cons a as _) (p , ps) = p ∷ toAll as ps
