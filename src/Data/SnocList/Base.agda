------------------------------------------------------------------------
-- The Agda standard library
--
-- SnocLists, basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.SnocList.Base where

{-
open import Algebra.Bundles.Raw using (RawMagma; RawMonoid)
-}
open import Data.Bool.Base as Bool using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Product.Base as Product using (_×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_)
open import Data.These.Base as These using (These; this; that; these)
open import Function.Base using (id; _∘′_; flip; _$′_; const)

--  using (id; _∘_ ; _∘′_; _∘₂_; _$_; const; flip)
open import Level using (Level)
{-
open import Relation.Unary using (Pred; Decidable)
-}
open import Relation.Binary.Core using (Rel)
import Relation.Binary.Definitions as B
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (does) -- (T?; does; ¬?)


private
  variable
    a b c p ℓ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Types

-- Standard lists grow on the left and are know as `forwards' lists
-- because their elements are traversed left-to-right. For didactic
-- reasons we rename the type and its constructors in this module so
-- that the type constructor (List>) and the data constructors ([>]
-- and _:>_) all explicitly mention the forwards direction.

open import Data.List.Base as List>
  using ()
  renaming ( List to List>
           ; [] to [>]
           ; _∷_ to _:>_
           )
  public

-- A backwards list (also known as a snoc list in the literature
-- because `snoc' is `cons' backwards is a list that grows on the
-- right, and that is therefore traversed right-to-left.

-- :> a right-to-left cons
-- <: its mirror image to get a left-to-right cons (aka snoc)

infixl 5 _<:_

data List< (A : Set a) : Set a where
  [<] : List< A
  _<:_ : List< A → A → List< A

------------------------------------------------------------------------
-- Operations interacting with lists
--
-- When representing a position in the middle of list (no matter what its
-- direction is), it is convenient to use a pair of a backwards list on
-- the left of the position and a forwards one on its right. This way we
-- can move the position around either left or right in contant time
-- by moving values from one list to the other.
--
-- E.g. if we want to move the position {HERE} one step to the left in
-- the list [1, 2, {HERE}, 3, 4] then we need to be able to take 2
-- out of the right end of the list on the left and push it onto the left
-- end of the list on the right to obtain [1, {HERE}, 2, 3, 4].
--
-- This can be done efficiently if the representation on the left is
-- right-to-left and so gives us constant time access to its right end
-- and vice-versa for the representation on the right.
--
-- The following operations describe how to combine [<1, 2] and
-- [> 3, 4] in a position-respecting manner to obtain a forwards
-- or backwards list respectively.
--
-- These all use the same mnemonic: the symbol used for the operation
-- spells out the direction of the consecutive input lists as well as
-- that of the output.
--
-- E.g. the string for the fish operator "<><" spells out
-- "backwards forwards backwards" and so it:
-- 1. takes a backwards list as its first argument
-- 2. takes a forwards list as its second argument
-- 3. returns a backwards list

-- Fish
infixl 5 _<><_
_<><_ : List< A → List> A → List< A
sx <>< [>]      = sx
sx <>< (x :> xs) = (sx <: x) <>< xs

-- Chips (is Fish's best friend)
infixr 6 _<>>_
_<>>_ : List< A → List> A → List> A
[<]      <>> xs = xs
(sx <: x) <>> xs = sx <>> (x :> xs)

-- Some examples showing that these operations are order-preserving.
private

  [<1,2] : List< ℕ
  [<1,2] = [<] <: 1 <: 2

  [>3,4] : List> ℕ
  [>3,4] = 3 :> 4 :> [>]

  [<1,2,3,4] : List< ℕ
  [<1,2,3,4] = [<] <: 1 <: 2 <: 3 <: 4

  [>1,2,3,4] : List> ℕ
  [>1,2,3,4] = 1 :> 2 :> 3 :> 4 :> [>]

  -- Order-preserving combination producing a backwards list
  _ : [<1,2] <>< [>3,4] ≡ [<1,2,3,4]
  _ = refl

  -- Order-preserving combination producing a forwards list
  _ : [<1,2] <>> [>3,4] ≡ [>1,2,3,4]
  _ = refl

toList> : List< A → List> A
toList> = _<>> [>]

fromList> : List> A → List< A
fromList> = [<] <><_

------------------------------------------------------------------------
-- Operations to transform snoc lists

map : (A → B) → List< A → List< B
map f [<]      = [<]
map f (sx <: x) = map f sx <: f x

infixl 5 _++_
_++_ : List< A → List< A → List< A
xs ++ [<] = xs
xs ++ (ys <: x) = (xs ++ ys) <: x

intersperse : A → List< A → List< A
intersperse x [<]       = [<]
intersperse x xs@([<] <: _) = xs
intersperse x (ys <: y) = intersperse x ys <: x <: y

intercalate : List< A → List< (List< A) → List< A
intercalate xs [<]         = [<]
intercalate xs ([<] <: ys) = ys
intercalate xs (yss <: ys) = intercalate xs yss ++ xs ++ ys

cartesianProductWith : (A → B → C) → List< A → List< B → List< C
cartesianProductWith f [<]       _  = [<]
cartesianProductWith f (xs <: x) ys = cartesianProductWith f xs ys ++ map (f x) ys

cartesianProduct : List< A → List< B → List< (A × B)
cartesianProduct = cartesianProductWith _,_

------------------------------------------------------------------------
-- Aligning and zipping

alignWith : (These A B → C) → List< A → List< B → List< C
alignWith f [<]       bs        = map (f ∘′ that) bs
alignWith f as        [<]       = map (f ∘′ this) as
alignWith f (as <: a) (bs <: b) = alignWith f as bs <: f (these a b)

zipWith : (A → B → C) → List< A → List< B → List< C
zipWith f (xs <: x) (ys <: y) = zipWith f xs ys <: f x y
zipWith f _        _          = [<]

unalignWith : (A → These B C) → List< A → List< B × List< C
unalignWith f [<]       = [<] , [<]
unalignWith f (as <: a) with f a
... | this b    = Product.map₁ (_<: b) (unalignWith f as)
... | that c    = Product.map₂ (_<: c) (unalignWith f as)
... | these b c = Product.map (_<: b) (_<: c) (unalignWith f as)

unzipWith : (A → B × C) → List< A → List< B × List< C
unzipWith f [<]         = [<] , [<]
unzipWith f (xys <: xy) = Product.zip _<:_ _<:_ (unzipWith f xys) (f xy)

partitionSumsWith : (A → B ⊎ C) → List< A → List< B × List< C
partitionSumsWith f = unalignWith (These.fromSum ∘′ f)

align : List< A → List< B → List< (These A B)
align = alignWith id

zip : List< A → List< B → List< (A × B)
zip = zipWith (_,_)

unalign : List< (These A B) → List< A × List< B
unalign = unalignWith id

unzip : List< (A × B) → List< A × List< B
unzip = unzipWith id

partitionSums : List< (A ⊎ B) → List< A × List< B
partitionSums = partitionSumsWith id

merge : {R : Rel A ℓ} → B.Decidable R → List< A → List< A → List< A
merge R? [<]           ys            = ys
merge R? xs            [<]           = xs
merge R? xsx@(xs <: x) ysy@(ys <: y) = if does (R? x y)
  then merge R? xs  ysy <: x
  else merge R? xsx ys  <: y

------------------------------------------------------------------------
-- Operations for reducing lists

foldr : (A → B → B) → B → List< A → B
foldr c n [<]       = n
foldr c n (xs <: x) = foldr c (c x n) xs

foldl : (A → B → A) → A → List< B → A
foldl c n [<]       = n
foldl c n (xs <: x) = c (foldl c n xs) x

concat : List< (List< A) → List< A
concat = foldl _++_ [<]

_ : concat ([<] <: [<1,2] <: (fromList> [>3,4])) ≡ [<1,2,3,4]
_ = refl

concatMap : (A → List< B) → List< A → List< B
concatMap f = concat ∘′ map f

-- Both List>.concatMap & List<.concatMap behave the same
_ :      (concatMap (λ n → [<] <: n <: suc n) [<1,2,3,4]) <>> [>]
  ≡ List>.concatMap (λ n → n :> suc n :> [>]) ([<1,2,3,4] <>> [>])
_ = refl

ap : List< (A → B) → List< A → List< B
ap fs as = concatMap (flip map as) fs

catMaybes : List< (Maybe A) → List< A
catMaybes = foldl (flip $′ maybe′ (flip _<:_) id) [<]

_ : let trash = [<] <: nothing in
    catMaybes (trash ++ map just [<1,2,3,4] ++ trash) ≡ [<1,2,3,4]
_ = refl

mapMaybe : (A → Maybe B) → List< A → List< B
mapMaybe p = catMaybes ∘′ map p

null : List< A → Bool
null [<]      = true
null (_ <: _) = false

length : List< A → ℕ
length = foldl (flip $′ const suc) 0

------------------------------------------------------------------------
-- Operations for constructing lists

fromMaybe : Maybe A → List< A
fromMaybe (just x) = [<] <: x
fromMaybe nothing  = [<]

replicate : ℕ → A → List< A
replicate zero    x = [<]
replicate (suc n) x = replicate n x <: x

iterate : (A → A) → A → ℕ → List< A
iterate f e zero    = [<]
iterate f e (suc n) = iterate f (f e) n <: e

inits : List< A → List< (List< A)
inits {A = A} = λ xs → tail xs <: [<]
  module Inits where
    tail : List< A → List< (List< A)
    tail [<]       = [<]
    tail (xs <: x) = map (_<: x) (tail xs) <: ([<] <: x)

tails : List< A → List< (List< A)
tails {A = A} = λ xs → tail xs <: xs
  module Tails where
    tail : List< A → List< (List< A)
    tail [<]       = [<]
    tail (xs <: _) = tail xs <: xs

insertAt : (xs : List< A) → Fin (suc (length xs)) → A → List< A
insertAt xs        zero    v = xs <: v
insertAt (xs <: x) (suc i) v = insertAt xs i v <: x

updateAt : (xs : List< A) → Fin (length xs) → (A → A) → List< A
updateAt (xs <: x) zero    f = xs <: f x
updateAt (xs <: x) (suc i) f = updateAt xs i f <: x

lookup : ∀ (xs : List< A) → Fin (length xs) → A
lookup (xs <: x) zero    = x
lookup (xs <: x) (suc i) = lookup xs i

-- Tabulation

applyUpTo : (ℕ → A) → ℕ → List< A
applyUpTo f zero    = [<]
applyUpTo f (suc n) = applyUpTo (f ∘′ suc) n <: f zero

applyDownFrom : (ℕ → A) → ℕ → List< A
applyDownFrom f zero    = [<]
applyDownFrom f (suc n) = applyDownFrom f n <: f n

tabulate : ∀ {n} (f : Fin n → A) → List< A
tabulate {n = zero}  f = [<]
tabulate {n = suc n} f = tabulate (f ∘′ suc) <: f zero

-- Numerical

upTo : ℕ → List< ℕ
upTo = applyUpTo id

downFrom : ℕ → List< ℕ
downFrom = applyDownFrom id

allFin : ∀ n → List< (Fin n)
allFin n = tabulate id

unfold : ∀ (P : ℕ → Set b)
         (f : ∀ {n} → P (suc n) → Maybe (A × P n)) →
         ∀ {n} → P n → List< A
unfold P f {n = zero}  s = [<]
unfold P f {n = suc n} s = maybe′ (λ (x , s′) → unfold P f s′ <: x) [<] (f s)

------------------------------------------------------------------------
-- Operations for reversing lists

reverseAcc : List< A → List< A → List< A
reverseAcc = foldr (flip _<:_)

reverse : List< A → List< A
reverse = reverseAcc [<]

_ : toList> (reverse [<1,2,3,4]) ≡ List>.reverse (toList> [<1,2,3,4])
_ = refl

{-
-- "Reverse append" xs ʳ++ ys = reverse xs ++ ys

infixr 5 _ʳ++_

_ʳ++_ : List< A → List< A → List< A
_ʳ++_ = flip reverseAcc

-- Snoc: Cons, but from the right.

infixl 6 _∷ʳ_

_∷ʳ_ : List< A → A → List< A
xs ∷ʳ x = xs ++ [ x ]



-- Backwards initialisation

infixl 5 _∷ʳ′_

data InitLast {A : Set a} : List< A → Set a where
  []    : InitLast []
  _∷ʳ′_ : (xs : List< A) (x : A) → InitLast (xs ∷ʳ x)

initLast : (xs : List< A) → InitLast xs
initLast []               = []
initLast (x ∷ xs)         with initLast xs
... | []       = [] ∷ʳ′ x
... | ys ∷ʳ′ y = (x ∷ ys) ∷ʳ′ y

-- uncons, but from the right
unsnoc : List< A → Maybe (List< A × A)
unsnoc as with initLast as
... | []       = nothing
... | xs ∷ʳ′ x = just (xs , x)

------------------------------------------------------------------------
-- Operations for deconstructing lists

-- Note that although the following three combinators can be useful for
-- programming, when proving it is often a better idea to manually
-- destruct a list argument as each branch of the pattern-matching will
-- have a refined type.

uncons : List< A → Maybe (A × List< A)
uncons []       = nothing
uncons (x ∷ xs) = just (x , xs)

head : List< A → Maybe A
head []      = nothing
head (x ∷ _) = just x

tail : List< A → Maybe (List< A)
tail []       = nothing
tail (_ ∷ xs) = just xs

last : List< A → Maybe A
last []       = nothing
last (x ∷ []) = just x
last (_ ∷ xs) = last xs

take : ℕ → List< A → List< A
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ℕ → List< A → List< A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

splitAt : ℕ → List< A → List< A × List< A
splitAt zero    xs       = ([] , xs)
splitAt (suc n) []       = ([] , [])
splitAt (suc n) (x ∷ xs) = Product.map₁ (x ∷_) (splitAt n xs)

removeAt : (xs : List< A) → Fin (length xs) → List< A
removeAt (x ∷ xs) zero     = xs
removeAt (x ∷ xs) (suc i)  = x ∷ removeAt xs i

------------------------------------------------------------------------
-- Operations for filtering lists

-- The following are a variety of functions that can be used to
-- construct sublists using a predicate.
--
-- Each function has two forms. The first main variant uses a
-- proof-relevant decidable predicate, while the second variant uses
-- a irrelevant boolean predicate and are suffixed with a `ᵇ` character,
-- typed as \^b.
--
-- The decidable versions have several advantages: 1) easier to prove
-- properties, 2) better meta-variable inference and 3) most of the rest
-- of the library is set-up to work with decidable predicates. However,
-- in rare cases the boolean versions can be useful, mainly when one
-- wants to minimise dependencies.
--
-- In summary, in most cases you probably want to use the decidable
-- versions over the boolean versions, e.g. use `takeWhile (_≤? 10) xs`
-- rather than `takeWhileᵇ (_≤ᵇ 10) xs`.

takeWhile : ∀ {P : Pred A p} → Decidable P → List< A → List< A
takeWhile P? []       = []
takeWhile P? (x ∷ xs) with does (P? x)
... | true  = x ∷ takeWhile P? xs
... | false = []

takeWhileᵇ : (A → Bool) → List< A → List< A
takeWhileᵇ p = takeWhile (T? ∘ p)

dropWhile : ∀ {P : Pred A p} → Decidable P → List< A → List< A
dropWhile P? []       = []
dropWhile P? (x ∷ xs) with does (P? x)
... | true  = dropWhile P? xs
... | false = x ∷ xs

dropWhileᵇ : (A → Bool) → List< A → List< A
dropWhileᵇ p = dropWhile (T? ∘ p)

filter : ∀ {P : Pred A p} → Decidable P → List< A → List< A
filter P? [] = []
filter P? (x ∷ xs) with does (P? x)
... | false = filter P? xs
... | true  = x ∷ filter P? xs

filterᵇ : (A → Bool) → List< A → List< A
filterᵇ p = filter (T? ∘ p)

partition : ∀ {P : Pred A p} → Decidable P → List< A → (List< A × List< A)
partition P? []       = ([] , [])
partition P? (x ∷ xs) with does (P? x) | partition P? xs
... | true  | (ys , zs) = (x ∷ ys , zs)
... | false | (ys , zs) = (ys , x ∷ zs)

partitionᵇ : (A → Bool) → List< A → List< A × List< A
partitionᵇ p = partition (T? ∘ p)

span : ∀ {P : Pred A p} → Decidable P → List< A → (List< A × List< A)
span P? []       = ([] , [])
span P? ys@(x ∷ xs) with does (P? x)
... | true  = Product.map (x ∷_) id (span P? xs)
... | false = ([] , ys)


spanᵇ : (A → Bool) → List< A → List< A × List< A
spanᵇ p = span (T? ∘ p)

break : ∀ {P : Pred A p} → Decidable P → List< A → (List< A × List< A)
break P? = span (¬? ∘ P?)

breakᵇ : (A → Bool) → List< A → List< A × List< A
breakᵇ p = break (T? ∘ p)

-- The predicate `P` represents the notion of newline character for the
-- type `A`. It is used to split the input list into a list of lines.
-- Some lines may be empty if the input contains at least two
-- consecutive newline characters.
linesBy : ∀ {P : Pred A p} → Decidable P → List< A → List< (List< A)
linesBy {A = A} P? = go nothing where

  go : Maybe (List< A) → List< A → List< (List< A)
  go acc []       = maybe′ ([_] ∘′ reverse) [] acc
  go acc (c ∷ cs) = if does (P? c)
    then reverse acc′ ∷ go nothing cs
    else go (just (c ∷ acc′)) cs
    where acc′ = Maybe.fromMaybe [] acc

linesByᵇ : (A → Bool) → List< A → List< (List< A)
linesByᵇ p = linesBy (T? ∘ p)

-- The predicate `P` represents the notion of space character for the
-- type `A`. It is used to split the input list into a list of words.
-- All the words are non empty and the output does not contain any space
-- characters.
wordsBy : ∀ {P : Pred A p} → Decidable P → List< A → List< (List< A)
wordsBy {A = A} P? = go [] where

  cons : List< A → List< (List< A) → List< (List< A)
  cons [] ass = ass
  cons as ass = reverse as ∷ ass

  go : List< A → List< A → List< (List< A)
  go acc []       = cons acc []
  go acc (c ∷ cs) = if does (P? c)
    then cons acc (go [] cs)
    else go (c ∷ acc) cs

wordsByᵇ : (A → Bool) → List< A → List< (List< A)
wordsByᵇ p = wordsBy (T? ∘ p)

derun : ∀ {R : Rel A p} → B.Decidable R → List< A → List< A
derun R? [] = []
derun R? (x ∷ []) = x ∷ []
derun R? (x ∷ xs@(y ∷ _)) with does (R? x y) | derun R? xs
... | true  | ys = ys
... | false | ys = x ∷ ys

derunᵇ : (A → A → Bool) → List< A → List< A
derunᵇ r = derun (T? ∘₂ r)

deduplicate : ∀ {R : Rel A p} → B.Decidable R → List< A → List< A
deduplicate R? [] = []
deduplicate R? (x ∷ xs) = x ∷ filter (¬? ∘ R? x) (deduplicate R? xs)

deduplicateᵇ : (A → A → Bool) → List< A → List< A
deduplicateᵇ r = deduplicate (T? ∘₂ r)

-- Finds the first element satisfying the boolean predicate
find : ∀ {P : Pred A p} → Decidable P → List< A → Maybe A
find P? []       = nothing
find P? (x ∷ xs) = if does (P? x) then just x else find P? xs

findᵇ : (A → Bool) → List< A → Maybe A
findᵇ p = find (T? ∘ p)

-- Finds the index of the first element satisfying the boolean predicate
findIndex : ∀ {P : Pred A p} → Decidable P → (xs : List< A) → Maybe $ Fin (length xs)
findIndex P? [] = nothing
findIndex P? (x ∷ xs) = if does (P? x)
  then just zero
  else Maybe.map suc (findIndex P? xs)

findIndexᵇ : (A → Bool) → (xs : List< A) → Maybe $ Fin (length xs)
findIndexᵇ p = findIndex (T? ∘ p)

-- Finds indices of all the elements satisfying the boolean predicate
findIndices : ∀ {P : Pred A p} → Decidable P → (xs : List< A) → List< $ Fin (length xs)
findIndices P? []       = []
findIndices P? (x ∷ xs) = if does (P? x)
  then zero ∷ indices
  else indices
    where indices = map suc (findIndices P? xs)

findIndicesᵇ : (A → Bool) → (xs : List< A) → List< $ Fin (length xs)
findIndicesᵇ p = findIndices (T? ∘ p)

------------------------------------------------------------------------
-- Actions on single elements

infixl 5 _[_]%=_ _[_]∷=_

-- xs [ i ]%= f  modifies the i-th element of xs according to f

_[_]%=_ : (xs : List< A) → Fin (length xs) → (A → A) → List< A
xs [ i ]%= f = updateAt xs i f

-- xs [ i ]≔ y  overwrites the i-th element of xs with y

_[_]∷=_ : (xs : List< A) → Fin (length xs) → A → List< A
xs [ k ]∷= v = xs [ k ]%= const v

------------------------------------------------------------------------
-- Conditional versions of cons and snoc

infixr 5 _?∷_
_?∷_ : Maybe A → List< A → List< A
_?∷_ = maybe′ _∷_ id

infixl 6 _∷ʳ?_
_∷ʳ?_ : List< A → Maybe A → List< A
xs ∷ʳ? x = maybe′ (xs ∷ʳ_) xs x

------------------------------------------------------------------------
-- Raw algebraic bundles

module _ (A : Set a) where
  ++-rawMagma : RawMagma a _
  ++-rawMagma = record
    { Carrier = List< A
    ; _≈_ = _≡_
    ; _∙_ = _++_
    }

  ++-[]-rawMonoid : RawMonoid a _
  ++-[]-rawMonoid = record
    { Carrier = List< A
    ; _≈_ = _≡_
    ; _∙_ = _++_
    ; ε = []
    }
-}
