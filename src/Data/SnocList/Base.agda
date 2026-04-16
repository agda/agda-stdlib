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

open import Function.Base using (id; _∘_; _∘′_; flip; _$′_; const)

open import Level using (Level)
open import Relation.Unary as U using (Pred)
open import Relation.Binary.Core using (Rel)
import Relation.Binary.Definitions as B
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (does; T?; ¬?)


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

-- :> a cons growing the list on the left
-- <: its mirror image to get a cons that grows the list on the right
--    (aka snoc)

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
[<]       <>> xs = xs
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
sx ++ [<] = sx
sx ++ (sy <: x) = (sx ++ sy) <: x

intersperse : A → List< A → List< A
intersperse x [<]       = [<]
intersperse x sx@([<] <: _) = sx
intersperse x (sy <: y) = intersperse x sy <: x <: y

intercalate : List< A → List< (List< A) → List< A
intercalate sx [<]         = [<]
intercalate sx ([<] <: sy) = sy
intercalate sx (sys <: sy) = intercalate sx sys ++ sx ++ sy

cartesianProductWith : (A → B → C) → List< A → List< B → List< C
cartesianProductWith f [<]       _  = [<]
cartesianProductWith f (sx <: x) sy = cartesianProductWith f sx sy ++ map (f x) sy

cartesianProduct : List< A → List< B → List< (A × B)
cartesianProduct = cartesianProductWith _,_

------------------------------------------------------------------------
-- Aligning and zipping

alignWith : (These A B → C) → List< A → List< B → List< C
alignWith f [<]       bs        = map (f ∘′ that) bs
alignWith f as        [<]       = map (f ∘′ this) as
alignWith f (as <: a) (bs <: b) = alignWith f as bs <: f (these a b)

zipWith : (A → B → C) → List< A → List< B → List< C
zipWith f (sx <: x) (sy <: y) = zipWith f sx sy <: f x y
zipWith f _        _          = [<]

unalignWith : (A → These B C) → List< A → List< B × List< C
unalignWith f [<]       = [<] , [<]
unalignWith f (as <: a) with f a
... | this b    = Product.map₁ (_<: b) (unalignWith f as)
... | that c    = Product.map₂ (_<: c) (unalignWith f as)
... | these b c = Product.map (_<: b) (_<: c) (unalignWith f as)

unzipWith : (A → B × C) → List< A → List< B × List< C
unzipWith f [<]         = [<] , [<]
unzipWith f (xsy <: xy) = Product.zip _<:_ _<:_ (unzipWith f xsy) (f xy)

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
merge R? [<]           sy            = sy
merge R? sx            [<]           = sx
merge R? sxx@(sx <: x) syy@(sy <: y) = if does (R? x y)
  then merge R? sx  syy <: x
  else merge R? sxx sy  <: y

------------------------------------------------------------------------
-- Operations for reducing lists

foldr : (A → B → B) → B → List< A → B
foldr c n [<]       = n
foldr c n (sx <: x) = foldr c (c x n) sx

foldl : (A → B → A) → A → List< B → A
foldl c n [<]       = n
foldl c n (sx <: x) = c (foldl c n sx) x

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
inits {A = A} = λ sx → tail sx <: [<]
  module Inits where
    tail : List< A → List< (List< A)
    tail [<]       = [<]
    tail (sx <: x) = map (_<: x) (tail sx) <: ([<] <: x)

tails : List< A → List< (List< A)
tails {A = A} = λ sx → tail sx <: sx
  module Tails where
    tail : List< A → List< (List< A)
    tail [<]       = [<]
    tail (sx <: _) = tail sx <: sx

insertAt : (sx : List< A) → Fin (suc (length sx)) → A → List< A
insertAt sx        zero    v = sx <: v
insertAt (sx <: x) (suc i) v = insertAt sx i v <: x

updateAt : (sx : List< A) → Fin (length sx) → (A → A) → List< A
updateAt (sx <: x) zero    f = sx <: f x
updateAt (sx <: x) (suc i) f = updateAt sx i f <: x

lookup : ∀ (sx : List< A) → Fin (length sx) → A
lookup (sx <: x) zero    = x
lookup (sx <: x) (suc i) = lookup sx i

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

-- "Reverse append" sx ++ʳ sy = sx ++ reverse sy

infixr 5 _++ʳ_

_++ʳ_ : List< A → List< A → List< A
_++ʳ_ = reverseAcc

_ : let [<3,4] = fromList> [>3,4] in
    [<1,2] ++ʳ [<3,4] ≡ [<1,2] ++ reverse [<3,4]
_ = refl

-- Cons: Snoc but from the left.

infixr 6 _ˡ∷_

_ˡ∷_ : A → List< A → List< A
x ˡ∷ sx = ([<] <: x) ++ sx

-- Backwards initialisation

infixr 5 _ˡ∷′_

data InitLast {A : Set a} : List< A → Set a where
  []    : InitLast [<]
  _ˡ∷′_ : (x : A) (sx : List< A) → InitLast (x ˡ∷ sx)

initLast : (sx : List< A) → InitLast sx
initLast [<]       = []
initLast (sx <: x) with initLast sx
... | []       = x ˡ∷′ [<]
... | y ˡ∷′ sy = y ˡ∷′ (sy <: x)

-- unsnoc, but from the left
uncons : List< A → Maybe (A × List< A)
uncons as with initLast as
... | []       = nothing
... | x ˡ∷′ sx = just (x , sx)

------------------------------------------------------------------------
-- Operations for deconstructing lists

-- Note that although the following three combinators can be useful for
-- programming, when proving it is often a better idea to manually
-- destruct a list argument as each branch of the pattern-matching will
-- have a refined type.

unsnoc : List< A → Maybe (List< A × A)
unsnoc [<]       = nothing
unsnoc (sx <: x) = just (sx , x)

head : List< A → Maybe A
head [<]      = nothing
head (_ <: x) = just x

tail : List< A → Maybe (List< A)
tail [<]       = nothing
tail (sx <: _) = just sx

last : List< A → Maybe A
last [<]        = nothing
last ([<] <: x) = just x
last (sx <: _)  = last sx

take : ℕ → List< A → List< A
take zero    sx        = [<]
take (suc n) [<]       = [<]
take (suc n) (sx <: x) = take n sx <: x

drop : ℕ → List< A → List< A
drop zero    sx        = sx
drop (suc n) [<]       = [<]
drop (suc n) (sx <: x) = drop n sx

splitAt : ℕ → List< A → List< A × List< A
splitAt zero    sx        = (sx , [<])
splitAt (suc n) [<]       = ([<] , [<])
splitAt (suc n) (sx <: x) = Product.map₂ (_<: x) (splitAt n sx)

removeAt : (sx : List< A) → Fin (length sx) → List< A
removeAt (sx <: _) zero     = sx
removeAt (sx <: x) (suc i)  = removeAt sx i <: x

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
-- versions over the boolean versions, e.g. use `takeWhile (_≤? 10) sx`
-- rather than `takeWhileᵇ (_≤ᵇ 10) sx`.

takeWhile : ∀ {P : Pred A p} → U.Decidable P → List< A → List< A
takeWhile P? [<]       = [<]
takeWhile P? (sx <: x) =
 if does (P? x) then takeWhile P? sx <: x else [<]

takeWhileᵇ : (A → Bool) → List< A → List< A
takeWhileᵇ p = takeWhile (T? ∘ p)

dropWhile : ∀ {P : Pred A p} → U.Decidable P → List< A → List< A
dropWhile P? [<]           = [<]
dropWhile P? sxx@(sx <: x) =
  if does (P? x) then dropWhile P? sx else sxx

dropWhileᵇ : (A → Bool) → List< A → List< A
dropWhileᵇ p = dropWhile (T? ∘ p)

filter : ∀ {P : Pred A p} → U.Decidable P → List< A → List< A
filter P? [<]       = [<]
filter P? (sx <: x) =
  let ih = filter P? sx in
  if does (P? x) then ih <: x else ih

filterᵇ : (A → Bool) → List< A → List< A
filterᵇ p = filter (T? ∘ p)

partition : ∀ {P : Pred A p} → U.Decidable P → List< A → (List< A × List< A)
partition P? [<]       = ([<] , [<])
partition P? (sx <: x) with does (P? x) | partition P? sx
... | true  | (sy , sz) = (sy <: x , sz)
... | false | (sy , sz) = (sy , sz <: x)

partitionᵇ : (A → Bool) → List< A → List< A × List< A
partitionᵇ p = partition (T? ∘ p)

span : ∀ {P : Pred A p} → U.Decidable P → List< A → (List< A × List< A)
span P? [<]           = ([<] , [<])
span P? sxx@(sx <: x) with does (P? x)
... | true  = Product.map₂ (_<: x) (span P? sx)
... | false = (sxx , [<])

spanᵇ : (A → Bool) → List< A → List< A × List< A
spanᵇ p = span (T? ∘ p)

break : ∀ {P : Pred A p} → U.Decidable P → List< A → (List< A × List< A)
break P? = span (¬? ∘ P?)

breakᵇ : (A → Bool) → List< A → List< A × List< A
breakᵇ p = break (T? ∘ p)

-- The predicate `P` represents the notion of newline character for the
-- type `A`. It is used to split the input list into a list of lines.
-- Some lines may be empty if the input contains at least two
-- consecutive newline characters.
linesBy : ∀ {P : Pred A p} → U.Decidable P → List< A → List< (List< A)
linesBy {A = A} P? cs = go cs [>] where

  go : List< A → List> A → List< (List< A)
  go [<]       l = [<] <: fromList> l
  go (cs <: c) l = if does (P? c)
    then go cs [>] <: fromList> l
    else go cs (c :> l)

linesByᵇ : (A → Bool) → List< A → List< (List< A)
linesByᵇ p = linesBy (T? ∘ p)

_ : linesByᵇ (ℕ._≤ᵇ 0) ([<] <: 0 <: 1 <: 2 <: 0 <: 3 <: 0 <: 0 <: 4) ≡
   [<] <: [<] <: ([<] <: 1 <: 2) <: ([<] <: 3) <: [<] <: ([<] <: 4)
_ = refl

_ : linesByᵇ (ℕ._≤ᵇ 0) ([<] <: 1 <: 2 <: 0 <: 3 <: 0 <: 0 <: 4) ≡
   [<] <: ([<] <: 1 <: 2) <: ([<] <: 3) <: [<] <: ([<] <: 4)
_ = refl

-- The predicate `P` represents the notion of space character for the
-- type `A`. It is used to split the input list into a list of words.
-- All the words are non empty and the output does not contain any space
-- characters.
wordsBy : ∀ {P : Pred A p} → U.Decidable P → List< A → List< (List< A)
wordsBy {A = A} P? cs = go cs [>] where

  snoc : List< (List< A) → List> A → List< (List< A)
  snoc sas [>] = sas
  snoc sas as  = sas <: fromList> as

  go : List< A → List> A → List< (List< A)
  go [<]       w = snoc [<] w
  go (cs <: c) w = if does (P? c)
    then snoc (go cs [>]) w
    else go cs (c :> w)
    -- notice that the order cs - c - w in go's LHS
    -- stays the same in the recursive call

{-
wordsByᵇ : (A → Bool) → List< A → List< (List< A)
wordsByᵇ p = wordsBy (T? ∘ p)

derun : ∀ {R : Rel A p} → B.Decidable R → List< A → List< A
derun R? [] = []
derun R? (x ∷ []) = x ∷ []
derun R? (x ∷ sx@(y ∷ _)) with does (R? x y) | derun R? sx
... | true  | sy = sy
... | false | sy = x ∷ sy

derunᵇ : (A → A → Bool) → List< A → List< A
derunᵇ r = derun (T? ∘₂ r)

deduplicate : ∀ {R : Rel A p} → B.Decidable R → List< A → List< A
deduplicate R? [] = []
deduplicate R? (x ∷ sx) = x ∷ filter (¬? ∘ R? x) (deduplicate R? sx)

deduplicateᵇ : (A → A → Bool) → List< A → List< A
deduplicateᵇ r = deduplicate (T? ∘₂ r)

-- Finds the first element satisfying the boolean predicate
find : ∀ {P : Pred A p} → Decidable P → List< A → Maybe A
find P? []       = nothing
find P? (x ∷ sx) = if does (P? x) then just x else find P? sx

findᵇ : (A → Bool) → List< A → Maybe A
findᵇ p = find (T? ∘ p)

-- Finds the index of the first element satisfying the boolean predicate
findIndex : ∀ {P : Pred A p} → Decidable P → (sx : List< A) → Maybe $ Fin (length sx)
findIndex P? [] = nothing
findIndex P? (x ∷ sx) = if does (P? x)
  then just zero
  else Maybe.map suc (findIndex P? sx)

findIndexᵇ : (A → Bool) → (sx : List< A) → Maybe $ Fin (length sx)
findIndexᵇ p = findIndex (T? ∘ p)

-- Finds indices of all the elements satisfying the boolean predicate
findIndices : ∀ {P : Pred A p} → Decidable P → (sx : List< A) → List< $ Fin (length sx)
findIndices P? []       = []
findIndices P? (x ∷ sx) = if does (P? x)
  then zero ∷ indices
  else indices
    where indices = map suc (findIndices P? sx)

findIndicesᵇ : (A → Bool) → (sx : List< A) → List< $ Fin (length sx)
findIndicesᵇ p = findIndices (T? ∘ p)

------------------------------------------------------------------------
-- Actions on single elements

infixl 5 _[_]%=_ _[_]∷=_

-- sx [ i ]%= f  modifies the i-th element of sx according to f

_[_]%=_ : (sx : List< A) → Fin (length sx) → (A → A) → List< A
sx [ i ]%= f = updateAt sx i f

-- sx [ i ]≔ y  overwrites the i-th element of sx with y

_[_]∷=_ : (sx : List< A) → Fin (length sx) → A → List< A
sx [ k ]∷= v = sx [ k ]%= const v

------------------------------------------------------------------------
-- Conditional versions of cons and snoc

infixr 5 _?∷_
_?∷_ : Maybe A → List< A → List< A
_?∷_ = maybe′ _∷_ id

infixl 6 _∷ʳ?_
_∷ʳ?_ : List< A → Maybe A → List< A
sx ∷ʳ? x = maybe′ (sx ∷ʳ_) sx x

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
