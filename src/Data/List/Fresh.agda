------------------------------------------------------------------------
-- The Agda standard library
--
-- Fresh lists, a proof relevant variant of Catarina Coquand's contexts in
-- "A Formalised Proof of the Soundness and Completeness of a Simply Typed
-- Lambda-Calculus with Explicit Substitutions"
------------------------------------------------------------------------

-- See README.Data.List.Fresh and README.Data.Trie.NonDependent for
-- examples of how to use fresh lists.

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh where

open import Level using (Level; _⊔_; Lift)
open import Data.Bool.Base using (true; false)
open import Data.Unit.Base
open import Data.Product using (∃; _×_; _,_; -,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function using (_∘′_; flip; id; _on_)
open import Relation.Nullary      using (does)
open import Relation.Unary   as U using (Pred)
open import Relation.Binary  as B using (Rel)
open import Relation.Nary

private
  variable
    a b p r s : Level
    A : Set a
    B : Set b

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
-- Operations for modifying fresh lists

module _ {R : Rel A r} {S : Rel B s} (f : A → B) (R⇒S : ∀[ R ⇒ (S on f) ]) where

  map   : List# A R → List# B S
  map-# : ∀ {a} as → a # as → f a # map as

  map []             = []
  map (cons a as ps) = cons (f a) (map as) (map-# as ps)

  map-# []        _        = _
  map-# (a ∷# as) (p , ps) = R⇒S p , map-# as ps

module _ {R : Rel B r} (f : A → B) where

  map₁ : List# A (R on f) → List# B R
  map₁ = map f id

module _ {R : Rel A r} {S : Rel A s} (R⇒S : ∀[ R ⇒ S ]) where

  map₂ : List# A R → List# A S
  map₂ = map id R⇒S

------------------------------------------------------------------------
-- Views

data Empty {A : Set a} {R : Rel A r} : List# A R → Set (a ⊔ r) where
  [] : Empty []

data NonEmpty {A : Set a} {R : Rel A r} : List# A R → Set (a ⊔ r) where
  cons : ∀ x xs pr → NonEmpty (cons x xs pr)

------------------------------------------------------------------------
-- Operations for reducing fresh lists

length : {R : Rel A r} → List# A R → ℕ
length []        = 0
length (_ ∷# xs) = suc (length xs)

------------------------------------------------------------------------
-- Operations for constructing fresh lists

pattern [_] a = a ∷# []

fromMaybe : {R : Rel A r} → Maybe A → List# A R
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

uncons : {R : Rel A r} → List# A R → Maybe (A × List# A R)
uncons []        = nothing
uncons (a ∷# as) = just (a , as)

head : {R : Rel A r} → List# A R → Maybe A
head = Maybe.map proj₁ ∘′ uncons

tail : {R : Rel A r} → List# A R → Maybe (List# A R)
tail = Maybe.map proj₂ ∘′ uncons

take   : {R : Rel A r} → ℕ → List# A R → List# A R
take-# : {R : Rel A r} → ∀ n a (as : List# A R) → a # as → a # take n as

take zero    xs             = []
take (suc n) []             = []
take (suc n) (cons a as ps) = cons a (take n as) (take-# n a as ps)

take-# zero    a xs        _        = _
take-# (suc n) a []        ps       = _
take-# (suc n) a (x ∷# xs) (p , ps) = p , take-# n a xs ps

drop : {R : Rel A r} → ℕ → List# A R → List# A R
drop zero    as        = as
drop (suc n) []        = []
drop (suc n) (a ∷# as) = drop n as

module _ {P : Pred A p} (P? : U.Decidable P) where

  takeWhile   : {R : Rel A r} → List# A R → List# A R
  takeWhile-# : ∀ {R : Rel A r} a (as : List# A R) → a # as → a # takeWhile as

  takeWhile []             = []
  takeWhile (cons a as ps) with does (P? a)
  ... | true  = cons a (takeWhile as) (takeWhile-# a as ps)
  ... | false = []

  takeWhile-# a []        _        = _
  takeWhile-# a (x ∷# xs) (p , ps) with does (P? x)
  ... | true  = p , takeWhile-# a xs ps
  ... | false = _

  dropWhile : {R : Rel A r} → List# A R → List# A R
  dropWhile []            = []
  dropWhile aas@(a ∷# as) with does (P? a)
  ... | true  = dropWhile as
  ... | false = aas

  filter   : {R : Rel A r} → List# A R → List# A R
  filter-# : ∀ {R : Rel A r} a (as : List# A R) → a # as → a # filter as

  filter []             = []
  filter (cons a as ps) with does (P? a)
  ... | true  = cons a (filter as) (filter-# a as ps)
  ... | false = filter as

  filter-# a []        _        = _
  filter-# a (x ∷# xs) (p , ps) with does (P? x)
  ... | true  = p , filter-# a xs ps
  ... | false = filter-# a xs ps

------------------------------------------------------------------------
-- Relationship to List and AllPairs

toList : {R : Rel A r} → List# A R → ∃ (AllPairs R)
toAll  : ∀ {R : Rel A r} {a} as → fresh A R a as → All (R a) (proj₁ (toList as))

toList []             = -, []
toList (cons x xs ps) = -, toAll xs ps ∷ proj₂ (toList xs)

toAll []        ps       = []
toAll (a ∷# as) (p , ps) = p ∷ toAll as ps

fromList   : ∀ {R : Rel A r} {xs} → AllPairs R xs → List# A R
fromList-# : ∀ {R : Rel A r} {x xs} (ps : AllPairs R xs) →
             All (R x) xs → x # fromList ps

fromList []       = []
fromList (r ∷ rs) = cons _ (fromList rs) (fromList-# rs r)

fromList-# []       _        = _
fromList-# (p ∷ ps) (r ∷ rs) = r , fromList-# ps rs
