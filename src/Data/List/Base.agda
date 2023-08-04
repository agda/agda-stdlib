------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists, basic types and operations
------------------------------------------------------------------------

-- See README.Data.List for examples of how to use and reason about
-- lists.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Base where

open import Algebra.Bundles.Raw using (RawMagma; RawMonoid)
open import Data.Bool.Base as Bool
  using (Bool; false; true; not; _∧_; _∨_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _*_ ; _≤_ ; s≤s)
open import Data.Product.Base as Prod using (_×_; _,_; map₁; map₂′)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.These.Base as These using (These; this; that; these)
open import Function.Base using (id; _∘_ ; _∘′_; _∘₂_; const; flip)
open import Level using (Level)
open import Relation.Nullary.Decidable.Core using (does; ¬?)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.Core using (Rel)
import Relation.Binary.Definitions as B
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    a b c p ℓ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Types

open import Agda.Builtin.List public
  using (List; []; _∷_)

------------------------------------------------------------------------
-- Operations for transforming lists

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

mapMaybe : (A → Maybe B) → List A → List B
mapMaybe p []       = []
mapMaybe p (x ∷ xs) with p x
... | just y  = y ∷ mapMaybe p xs
... | nothing = mapMaybe p xs

catMaybes : List (Maybe A) → List A
catMaybes = mapMaybe id

infixr 5 _++_

_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

intersperse : A → List A → List A
intersperse x []       = []
intersperse x (y ∷ []) = y ∷ []
intersperse x (y ∷ ys) = y ∷ x ∷ intersperse x ys

intercalate : List A → List (List A) → List A
intercalate xs []         = []
intercalate xs (ys ∷ [])  = ys
intercalate xs (ys ∷ yss) = ys ++ xs ++ intercalate xs yss

cartesianProductWith : (A → B → C) → List A → List B → List C
cartesianProductWith f []       _  = []
cartesianProductWith f (x ∷ xs) ys = map (f x) ys ++ cartesianProductWith f xs ys

cartesianProduct : List A → List B → List (A × B)
cartesianProduct = cartesianProductWith _,_

------------------------------------------------------------------------
-- Aligning and zipping

alignWith : (These A B → C) → List A → List B → List C
alignWith f []       bs       = map (f ∘′ that) bs
alignWith f as       []       = map (f ∘′ this) as
alignWith f (a ∷ as) (b ∷ bs) = f (these a b) ∷ alignWith f as bs

zipWith : (A → B → C) → List A → List B → List C
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
zipWith f _        _        = []

unalignWith : (A → These B C) → List A → List B × List C
unalignWith f []       = [] , []
unalignWith f (a ∷ as) with f a
... | this b    = Prod.map₁ (b ∷_) (unalignWith f as)
... | that c    = Prod.map₂ (c ∷_) (unalignWith f as)
... | these b c = Prod.map (b ∷_) (c ∷_) (unalignWith f as)

unzipWith : (A → B × C) → List A → List B × List C
unzipWith f []         = [] , []
unzipWith f (xy ∷ xys) = Prod.zip _∷_ _∷_ (f xy) (unzipWith f xys)

partitionSumsWith : (A → B ⊎ C) → List A → List B × List C
partitionSumsWith f = unalignWith (These.fromSum ∘′ f)

align : List A → List B → List (These A B)
align = alignWith id

zip : List A → List B → List (A × B)
zip = zipWith (_,_)

unalign : List (These A B) → List A × List B
unalign = unalignWith id

unzip : List (A × B) → List A × List B
unzip = unzipWith id

partitionSums : List (A ⊎ B) → List A × List B
partitionSums = partitionSumsWith id

merge : {R : Rel A ℓ} → B.Decidable R → List A → List A → List A
merge R? []       ys       = ys
merge R? xs       []       = xs
merge R? (x ∷ xs) (y ∷ ys) = if does (R? x y)
  then x ∷ merge R? xs (y ∷ ys)
  else y ∷ merge R? (x ∷ xs) ys

------------------------------------------------------------------------
-- Operations for reducing lists

foldr : (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : (A → B → A) → A → List B → A
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

concat : List (List A) → List A
concat = foldr _++_ []

concatMap : (A → List B) → List A → List B
concatMap f = concat ∘ map f

ap : List (A → B) → List A → List B
ap fs as = concatMap (flip map as) fs

null : List A → Bool
null []       = true
null (x ∷ xs) = false

and : List Bool → Bool
and = foldr _∧_ true

or : List Bool → Bool
or = foldr _∨_ false

any : (A → Bool) → List A → Bool
any p = or ∘ map p

all : (A → Bool) → List A → Bool
all p = and ∘ map p

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

length : List A → ℕ
length = foldr (const suc) 0

------------------------------------------------------------------------
-- Operations for constructing lists

[_] : A → List A
[ x ] = x ∷ []

fromMaybe : Maybe A → List A
fromMaybe (just x) = [ x ]
fromMaybe nothing  = []

replicate : ℕ → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

inits : List A → List (List A)
inits []       = [] ∷ []
inits (x ∷ xs) = [] ∷ map (x ∷_) (inits xs)

tails : List A → List (List A)
tails []       = [] ∷ []
tails (x ∷ xs) = (x ∷ xs) ∷ tails xs

-- Scans

scanr : (A → B → B) → B → List A → List B
scanr f e []       = e ∷ []
scanr f e (x ∷ xs) with scanr f e xs
... | []     = []                -- dead branch
... | y ∷ ys = f x y ∷ y ∷ ys

scanl : (A → B → A) → A → List B → List A
scanl f e []       = e ∷ []
scanl f e (x ∷ xs) = e ∷ scanl f (f e x) xs

-- Tabulation

applyUpTo : (ℕ → A) → ℕ → List A
applyUpTo f zero    = []
applyUpTo f (suc n) = f zero ∷ applyUpTo (f ∘ suc) n

applyDownFrom : (ℕ → A) → ℕ → List A
applyDownFrom f zero    = []
applyDownFrom f (suc n) = f n ∷ applyDownFrom f n

tabulate : ∀ {n} (f : Fin n → A) → List A
tabulate {n = zero}  f = []
tabulate {n = suc n} f = f zero ∷ tabulate (f ∘ suc)

lookup : ∀ (xs : List A) → Fin (length xs) → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

-- Numerical

upTo : ℕ → List ℕ
upTo = applyUpTo id

downFrom : ℕ → List ℕ
downFrom = applyDownFrom id

allFin : ∀ n → List (Fin n)
allFin n = tabulate id

unfold : ∀ (P : ℕ → Set b)
         (f : ∀ {n} → P (suc n) → Maybe (A × P n)) →
         ∀ {n} → P n → List A
unfold P f {n = zero}  s = []
unfold P f {n = suc n} s with f s
... | nothing       = []
... | just (x , s′) = x ∷ unfold P f s′

------------------------------------------------------------------------
-- Operations for reversing lists

reverseAcc : List A → List A → List A
reverseAcc = foldl (flip _∷_)

reverse : List A → List A
reverse = reverseAcc []

-- "Reverse append" xs ʳ++ ys = reverse xs ++ ys

infixr 5 _ʳ++_

_ʳ++_ : List A → List A → List A
_ʳ++_ = flip reverseAcc

-- Snoc: Cons, but from the right.

infixl 6 _∷ʳ_

_∷ʳ_ : List A → A → List A
xs ∷ʳ x = xs ++ [ x ]



-- Backwards initialisation

infixl 5 _∷ʳ′_

data InitLast {A : Set a} : List A → Set a where
  []    : InitLast []
  _∷ʳ′_ : (xs : List A) (x : A) → InitLast (xs ∷ʳ x)

initLast : (xs : List A) → InitLast xs
initLast []               = []
initLast (x ∷ xs)         with initLast xs
... | []       = [] ∷ʳ′ x
... | ys ∷ʳ′ y = (x ∷ ys) ∷ʳ′ y

-- uncons, but from the right
unsnoc : List A → Maybe (List A × A)
unsnoc as with initLast as
... | []       = nothing
... | xs ∷ʳ′ x = just (xs , x)

------------------------------------------------------------------------
-- Operations for deconstructing lists

-- Note that although the following three combinators can be useful for
-- programming, when proving it is often a better idea to manually
-- destruct a list argument as each branch of the pattern-matching will
-- have a refined type.

uncons : List A → Maybe (A × List A)
uncons []       = nothing
uncons (x ∷ xs) = just (x , xs)

head : List A → Maybe A
head []      = nothing
head (x ∷ _) = just x

tail : List A → Maybe (List A)
tail []       = nothing
tail (_ ∷ xs) = just xs

last : List A → Maybe A
last []       = nothing
last (x ∷ []) = just x
last (_ ∷ xs) = last xs

take : ℕ → List A → List A
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

splitAt : ℕ → List A → List A × List A
splitAt zero    xs       = ([] , xs)
splitAt (suc n) []       = ([] , [])
splitAt (suc n) (x ∷ xs) = Prod.map₁ (x ∷_) (splitAt n xs)

-- The following are functions which split a list up using boolean
-- predicates. However, in practice they are difficult to use and
-- prove properties about, and are mainly provided for advanced use
-- cases where one wants to minimise dependencies. In most cases
-- you probably want to use the versions defined below based on
-- decidable predicates. e.g. use `takeWhile (_≤? 10) xs`
-- instead of `takeWhileᵇ (_≤ᵇ 10) xs`

takeWhileᵇ : (A → Bool) → List A → List A
takeWhileᵇ p []       = []
takeWhileᵇ p (x ∷ xs) = if p x then x ∷ takeWhileᵇ p xs else []

dropWhileᵇ : (A → Bool) → List A → List A
dropWhileᵇ p []       = []
dropWhileᵇ p (x ∷ xs) = if p x then dropWhileᵇ p xs else x ∷ xs

filterᵇ : (A → Bool) → List A → List A
filterᵇ p []       = []
filterᵇ p (x ∷ xs) = if p x then x ∷ filterᵇ p xs else filterᵇ p xs

partitionᵇ : (A → Bool) → List A → List A × List A
partitionᵇ p []       = ([] , [])
partitionᵇ p (x ∷ xs) = (if p x then Prod.map₁ else Prod.map₂′) (x ∷_) (partitionᵇ p xs)

spanᵇ : (A → Bool) → List A → List A × List A
spanᵇ p []       = ([] , [])
spanᵇ p (x ∷ xs) = if p x
  then Prod.map₁ (x ∷_) (spanᵇ p xs)
  else ([] , x ∷ xs)

breakᵇ : (A → Bool) → List A → List A × List A
breakᵇ p = spanᵇ (not ∘ p)

linesByᵇ : (A → Bool) → List A → List (List A)
linesByᵇ {A = A} p = go nothing
  where
  go : Maybe (List A) → List A → List (List A)
  go acc []       = maybe′ ([_] ∘′ reverse) [] acc
  go acc (c ∷ cs) with p c
  ... | true  = reverse (Maybe.fromMaybe [] acc) ∷ go nothing cs
  ... | false = go (just (c ∷ Maybe.fromMaybe [] acc)) cs

wordsByᵇ : (A → Bool) → List A → List (List A)
wordsByᵇ {A = A} p = go []
  where
  cons : List A → List (List A) → List (List A)
  cons [] ass = ass
  cons as ass = reverse as ∷ ass

  go : List A → List A → List (List A)
  go acc []       = cons acc []
  go acc (c ∷ cs) with p c
  ... | true  = cons acc (go [] cs)
  ... | false = go (c ∷ acc) cs

derunᵇ : (A → A → Bool) → List A → List A
derunᵇ r []           = []
derunᵇ r (x ∷ [])     = x ∷ []
derunᵇ r (x ∷ y ∷ xs) = if r x y
  then derunᵇ r (y ∷ xs)
  else x ∷ derunᵇ r (y ∷ xs)

deduplicateᵇ : (A → A → Bool) → List A → List A
deduplicateᵇ r [] = []
deduplicateᵇ r (x ∷ xs) = x ∷ filterᵇ (not ∘ r x) (deduplicateᵇ r xs)

-- Equivalent functions that use a decidable predicate instead of a
-- boolean function.

takeWhile : ∀ {P : Pred A p} → Decidable P → List A → List A
takeWhile P? = takeWhileᵇ (does ∘ P?)

dropWhile : ∀ {P : Pred A p} → Decidable P → List A → List A
dropWhile P? = dropWhileᵇ (does ∘ P?)

filter : ∀ {P : Pred A p} → Decidable P → List A → List A
filter P? = filterᵇ (does ∘ P?)

partition : ∀ {P : Pred A p} → Decidable P → List A → (List A × List A)
partition P? = partitionᵇ (does ∘ P?)

span : ∀ {P : Pred A p} → Decidable P → List A → (List A × List A)
span P? = spanᵇ (does ∘ P?)

break : ∀ {P : Pred A p} → Decidable P → List A → (List A × List A)
break P? = breakᵇ (does ∘ P?)

-- The predicate `P` represents the notion of newline character for the
-- type `A`. It is used to split the input list into a list of lines.
-- Some lines may be empty if the input contains at least two
-- consecutive newline characters.
linesBy : ∀ {P : Pred A p} → Decidable P → List A → List (List A)
linesBy P? = linesByᵇ (does ∘ P?)

-- The predicate `P` represents the notion of space character for the
-- type `A`. It is used to split the input list into a list of words.
-- All the words are non empty and the output does not contain any space
-- characters.
wordsBy : ∀ {P : Pred A p} → Decidable P → List A → List (List A)
wordsBy P? = wordsByᵇ (does ∘ P?)

derun : ∀ {R : Rel A p} → B.Decidable R → List A → List A
derun R? = derunᵇ (does ∘₂ R?)

deduplicate : ∀ {R : Rel A p} → B.Decidable R → List A → List A
deduplicate R? = deduplicateᵇ (does ∘₂ R?)

------------------------------------------------------------------------
-- Actions on single elements

infixl 5 _[_]%=_ _[_]∷=_ _─_

_[_]%=_ : (xs : List A) → Fin (length xs) → (A → A) → List A
(x ∷ xs) [ zero  ]%= f = f x ∷ xs
(x ∷ xs) [ suc k ]%= f = x ∷ (xs [ k ]%= f)

_[_]∷=_ : (xs : List A) → Fin (length xs) → A → List A
xs [ k ]∷= v = xs [ k ]%= const v

_─_ : (xs : List A) → Fin (length xs) → List A
(x ∷ xs) ─ zero  = xs
(x ∷ xs) ─ suc k = x ∷ (xs ─ k)

------------------------------------------------------------------------
-- Conditional versions of cons and snoc

infixr 5 _?∷_
_?∷_ : Maybe A → List A → List A
_?∷_ = maybe′ _∷_ id

infixl 6 _∷ʳ?_
_∷ʳ?_ : List A → Maybe A → List A
xs ∷ʳ? x = maybe′ (xs ∷ʳ_) xs x

------------------------------------------------------------------------
-- Raw algebraic bundles

module _ (A : Set a) where
  ++-rawMagma : RawMagma a _
  ++-rawMagma = record
    { Carrier = List A
    ; _≈_ = _≡_
    ; _∙_ = _++_
    }

  ++-[]-rawMonoid : RawMonoid a _
  ++-[]-rawMonoid = record
    { Carrier = List A
    ; _≈_ = _≡_
    ; _∙_ = _++_
    ; ε = []
    }

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.4

infixl 5 _∷ʳ'_
_∷ʳ'_ : (xs : List A) (x : A) → InitLast (xs ∷ʳ x)
_∷ʳ'_ = InitLast._∷ʳ′_
{-# WARNING_ON_USAGE _∷ʳ'_
"Warning: _∷ʳ'_ (ending in an apostrophe) was deprecated in v1.4.
Please use _∷ʳ′_ (ending in a prime) instead."
#-}
