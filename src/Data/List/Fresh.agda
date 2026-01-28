------------------------------------------------------------------------
-- The Agda standard library
--
-- Fresh lists, a proof relevant variant of Catarina Coquand's contexts
-- in "A Formalised Proof of the Soundness and Completeness of a Simply
-- Typed Lambda-Calculus with Explicit Substitutions"
------------------------------------------------------------------------

-- See README.Data.List.Fresh and README.Data.Trie.NonDependent for
-- examples of how to use fresh lists.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Fresh where

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Data.Product.Base using (∃; _×_; _,_; -,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function.Base using (_∘′_; flip; id; _on_)
open import Relation.Nullary using (does)
open import Relation.Unary as Unary using (Pred; Decidable)
open import Relation.Binary.Core using (Rel; REL)
import Relation.Binary.Definitions as B using (Reflexive)
open import Relation.Nary using (_⇒_; ∀[_])


private
  variable
    a b p r s : Level
    A : Set a
    B : Set b
    R : Rel A r
    S : Rel A s
    x y : A


------------------------------------------------------------------------
-- Basic type

-- If we pick an R such that (R a b) means that a is different from b
-- then we have a list of distinct values.

module _ {a} (A : Set a) (R : Rel A r) where

  data List# : Set (a ⊔ r)
  fresh : REL A List# r

  data List# where
    []   : List#
    cons : (x : A) (xs : List#) → fresh x xs → List#

  -- Whenever R can be reconstructed by η-expansion (e.g. because it is
  -- the erasure ⌊_⌋ of a decidable predicate, cf. Relation.Nary) or we
  -- do not care about the proof, it is convenient to get back list syntax.

  -- We use a different symbol to avoid conflict when importing both
  -- Data.List and Data.List.Fresh.
  infixr 5 _∷#_
  pattern _∷#_ x xs = cons x xs _

  fresh a []        = ⊤
  fresh a (x ∷# xs) = R a x × fresh a xs

-- Convenient notation for freshness making A and R implicit parameters
infix 5 _#_
_#_ : REL A (List# A R) _
_#_ = fresh _ _

------------------------------------------------------------------------
-- Operations for modifying fresh lists

module _ (f : A → B) (R⇒S : ∀[ R ⇒ (S on f) ]) where

  map   : List# A R → List# B S
  map-# : ∀ xs → x # xs → f x # map xs

  map []             = []
  map (cons x xs ps) = cons (f x) (map xs) (map-# xs ps)

  map-# []        _        = _
  map-# (x ∷# xs) (p , ps) = R⇒S p , map-# xs ps

module _ (f : A → B) where

  map₁ : List# A (R on f) → List# B R
  map₁ = map f id

module _ {S : Rel A s} (R⇒S : ∀[ R ⇒ S ]) where

  map₂ : List# A R → List# A S
  map₂ = map id R⇒S

------------------------------------------------------------------------
-- Views

data Empty {A : Set a} {R : Rel A r} : Pred (List# A R) (a ⊔ r) where
  [] : Empty []

data NonEmpty {A : Set a} {R : Rel A r} : Pred (List# A R) (a ⊔ r) where
  cons : ∀ x xs pr → NonEmpty (cons x xs pr)

------------------------------------------------------------------------
-- Operations for reducing fresh lists

length : List# A R → ℕ
length []        = 0
length (_ ∷# xs) = suc (length xs)

------------------------------------------------------------------------
-- Operations for constructing fresh lists

pattern [_] x = x ∷# []

fromMaybe : Maybe A → List# A R
fromMaybe nothing  = []
fromMaybe (just x) = [ x ]

module _ (R-refl : B.Reflexive {A = A} R) where

  replicate   : ℕ → A → List# A R
  replicate-# : (n : ℕ) (x : A) → x # replicate n x

  replicate zero    x = []
  replicate (suc n) x = cons x (replicate n x) (replicate-# n x)

  replicate-# zero    x = _
  replicate-# (suc n) x = R-refl , replicate-# n x

------------------------------------------------------------------------
-- Operations for deconstructing fresh lists

uncons : List# A R → Maybe (A × List# A R)
uncons []        = nothing
uncons (x ∷# xs) = just (x , xs)

head : List# A R → Maybe A
head = Maybe.map proj₁ ∘′ uncons

tail : List# A R → Maybe (List# A R)
tail = Maybe.map proj₂ ∘′ uncons

take   : ℕ → List# A R → List# A R
take-# : ∀ n y (xs : List# A R) → y # xs → y # take n xs

take zero    xs             = []
take (suc n) []             = []
take (suc n) (cons x xs ps) = cons x (take n xs) (take-# n x xs ps)

take-# zero    y xs        _        = _
take-# (suc n) y []        ps       = _
take-# (suc n) y (x ∷# xs) (p , ps) = p , take-# n y xs ps

drop : ℕ → List# A R → List# A R
drop zero    xs        = xs
drop (suc n) []        = []
drop (suc n) (x ∷# xs) = drop n xs

module _ {P : Pred A p} (P? : U.Decidable {A = A} P) where

  takeWhile   : List# A R → List# A R
  takeWhile-# : ∀ y (xs : List# A R) → y # xs → y # takeWhile xs

  takeWhile []             = []
  takeWhile (cons x xs ps) =
    if does (P? x) then cons x (takeWhile xs) (takeWhile-# x xs ps) else []

  -- this 'with' is needed to cause reduction in the type of 'takeWhile (a ∷# as)'
  takeWhile-# y []        _        = _
  takeWhile-# y (x ∷# xs) (p , ps) with does (P? x)
  ... | true  = p , takeWhile-# y xs ps
  ... | false = _

  dropWhile : List# A R → List# A R
  dropWhile []            = []
  dropWhile xxs@(x ∷# xs)  = if does (P? x) then dropWhile xs else xxs

  filter   : List# A R → List# A R
  filter-# : ∀ y (xs : List# A R) → y # xs → y # filter xs

  filter []             = []
  filter (cons x xs ps) =
    let l = filter xs in
    if does (P? x) then cons x l (filter-# x xs ps) else l

  -- this 'with' is needed to cause reduction in the type of 'filter-# y (x ∷# xs)'
  filter-# y []        _        = _
  filter-# y (x ∷# xs) (p , ps) with does (P? x)
  ... | true  = p , filter-# y xs ps
  ... | false = filter-# y xs ps

------------------------------------------------------------------------
-- Relationship to List and AllPairs

toList : List# A R → ∃ (AllPairs R)
toAll  : (xs : List# A R) → x # xs → All (R x) (proj₁ (toList xs))

toList []             = -, []
toList (cons x xs ps) = -, toAll xs ps ∷ proj₂ (toList xs)

toAll []        ps       = []
toAll (x ∷# xs) (p , ps) = p ∷ toAll xs ps

fromList   : ∀ {xs} → AllPairs R xs → List# A R
fromList-# : ∀ {xs} (ps : AllPairs R xs) →
             All (R x) xs → x # fromList ps

fromList []       = []
fromList (r ∷ rs) = cons _ (fromList rs) (fromList-# rs r)

fromList-# []       _        = _
fromList-# (p ∷ ps) (r ∷ rs) = r , fromList-# ps rs
