------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists, basic types and operations
------------------------------------------------------------------------

module Data.List.Base where

open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base as Bool
  using (Bool; false; true; not; _∧_; _∨_; if_then_else_)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Product as Prod using (_×_; _,_)
open import Data.These as These using (These; this; that; these)
open import Function using (id; _∘_ ; _∘′_; const; flip)

open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Unary.Properties using (∁?)

------------------------------------------------------------------------
-- Types

open import Agda.Builtin.List public
  using (List; []; _∷_)

------------------------------------------------------------------------
-- Operations for transforming lists

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

mapMaybe : ∀ {a b} {A : Set a} {B : Set b} → (A → Maybe B) → List A → List B
mapMaybe p []       = []
mapMaybe p (x ∷ xs) with p x
... | just y  = y ∷ mapMaybe p xs
... | nothing =     mapMaybe p xs

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

intersperse : ∀ {a} {A : Set a} → A → List A → List A
intersperse x []       = []
intersperse x (y ∷ []) = y ∷ []
intersperse x (y ∷ ys) = y ∷ x ∷ intersperse x ys

------------------------------------------------------------------------
-- Aligning and zipping

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

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

module _ {a b} {A : Set a} {B : Set b} where

  align : List A → List B → List (These A B)
  align = alignWith id

  zip : List A → List B → List (A × B)
  zip = zipWith (_,_)

  unalign : List (These A B) → List A × List B
  unalign = unalignWith id

  unzip : List (A × B) → List A × List B
  unzip = unzipWith id

------------------------------------------------------------------------
-- Operations for reducing lists

foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : ∀ {a b} {A : Set a} {B : Set b} → (A → B → A) → A → List B → A
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

concat : ∀ {a} {A : Set a} → List (List A) → List A
concat = foldr _++_ []

concatMap : ∀ {a b} {A : Set a} {B : Set b} →
            (A → List B) → List A → List B
concatMap f = concat ∘ map f

null : ∀ {a} {A : Set a} → List A → Bool
null []       = true
null (x ∷ xs) = false

and : List Bool → Bool
and = foldr _∧_ true

or : List Bool → Bool
or = foldr _∨_ false

any : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
any p = or ∘ map p

all : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
all p = and ∘ map p

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

length : ∀ {a} {A : Set a} → List A → ℕ
length = foldr (const suc) 0

------------------------------------------------------------------------
-- Operations for constructing lists

[_] : ∀ {a} {A : Set a} → A → List A
[ x ] = x ∷ []

fromMaybe : ∀ {a} {A : Set a} → Maybe A → List A
fromMaybe (just x) = [ x ]
fromMaybe nothing  = []

replicate : ∀ {a} {A : Set a} → ℕ → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

inits : ∀ {a} {A : Set a} → List A → List (List A)
inits []       = [] ∷ []
inits (x ∷ xs) = [] ∷ map (x ∷_) (inits xs)

tails : ∀ {a} {A : Set a} → List A → List (List A)
tails []       = [] ∷ []
tails (x ∷ xs) = (x ∷ xs) ∷ tails xs

-- Scans

scanr : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → B) → B → List A → List B
scanr f e []       = e ∷ []
scanr f e (x ∷ xs) with scanr f e xs
... | []     = []                -- dead branch
... | y ∷ ys = f x y ∷ y ∷ ys

scanl : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → A) → A → List B → List A
scanl f e []       = e ∷ []
scanl f e (x ∷ xs) = e ∷ scanl f (f e x) xs

module _ {a} {A : Set a} where

-- Tabulation

  applyUpTo : (ℕ → A) → ℕ → List A
  applyUpTo f zero    = []
  applyUpTo f (suc n) = f zero ∷ applyUpTo (f ∘ suc) n

  applyDownFrom : (ℕ → A) → ℕ → List A
  applyDownFrom f zero = []
  applyDownFrom f (suc n) = f n ∷ applyDownFrom f n

  tabulate : ∀ {n} (f : Fin n → A) → List A
  tabulate {zero}  f = []
  tabulate {suc n} f = f Fin.zero ∷ tabulate (f ∘ Fin.suc)

  lookup : ∀ (xs : List A) → Fin (length xs) → A
  lookup [] ()
  lookup (x ∷ xs) Fin.zero    = x
  lookup (x ∷ xs) (Fin.suc i) = lookup xs i

-- Numerical

upTo : ℕ → List ℕ
upTo = applyUpTo id

downFrom : ℕ → List ℕ
downFrom = applyDownFrom id

allFin : ∀ n → List (Fin n)
allFin n = tabulate id

-- Other

unfold : ∀ {a b} {A : Set a} (B : ℕ → Set b)
         (f : ∀ {n} → B (suc n) → Maybe (A × B n)) →
         ∀ {n} → B n → List A
unfold B f {n = zero}  s = []
unfold B f {n = suc n} s with f s
... | nothing       = []
... | just (x , s') = x ∷ unfold B f s'

------------------------------------------------------------------------
-- Operations for deconstructing lists

-- Note that although these combinators can be useful for programming, when
-- proving it is often a better idea to manually destruct a list argument:
-- each branch of the pattern-matching will have a refined type.

module _ {a} {A : Set a} where

  uncons : List A → Maybe (A × List A)
  uncons []       = nothing
  uncons (x ∷ xs) = just (x , xs)

  head : List A → Maybe A
  head []      = nothing
  head (x ∷ _) = just x

  tail : List A → Maybe (List A)
  tail []       = nothing
  tail (_ ∷ xs) = just xs

take : ∀ {a} {A : Set a} → ℕ → List A → List A
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ∀ {a} {A : Set a} → ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

splitAt : ∀ {a} {A : Set a} → ℕ → List A → (List A × List A)
splitAt zero    xs       = ([] , xs)
splitAt (suc n) []       = ([] , [])
splitAt (suc n) (x ∷ xs) with splitAt n xs
... | (ys , zs) = (x ∷ ys , zs)

takeWhile : ∀ {a p} {A : Set a} {P : Pred A p} →
            Decidable P → List A → List A
takeWhile P? []       = []
takeWhile P? (x ∷ xs) with P? x
... | yes _ = x ∷ takeWhile P? xs
... | no  _ = []

dropWhile : ∀ {a p} {A : Set a} {P : Pred A p} →
            Decidable P → List A → List A
dropWhile P? []       = []
dropWhile P? (x ∷ xs) with P? x
... | yes _ = dropWhile P? xs
... | no  _ = x ∷ xs

filter : ∀ {a p} {A : Set a} {P : Pred A p} →
         Decidable P → List A → List A
filter P? [] = []
filter P? (x ∷ xs) with P? x
... | no  _ = filter P? xs
... | yes _ = x ∷ filter P? xs

partition : ∀ {a p} {A : Set a} {P : Pred A p} →
            Decidable P → List A → (List A × List A)
partition P? []       = ([] , [])
partition P? (x ∷ xs) with P? x | partition P? xs
... | yes _ | (ys , zs) = (x ∷ ys , zs)
... | no  _ | (ys , zs) = (ys , x ∷ zs)

span : ∀ {a p} {A : Set a} {P : Pred A p} →
       Decidable P → List A → (List A × List A)
span P? []       = ([] , [])
span P? (x ∷ xs) with P? x
... | yes _ = Prod.map (x ∷_) id (span P? xs)
... | no  _ = ([] , x ∷ xs)

break : ∀ {a p} {A : Set a} {P : Pred A p} →
        Decidable P → List A → (List A × List A)
break P? = span (∁? P?)

------------------------------------------------------------------------
-- Actions on single elements

module _ {a} {A : Set a} where

  infixl 5 _[_]%=_ _[_]∷=_ _─_

  _[_]%=_ : (xs : List A) → Fin (length xs) → (A → A) → List A
  []       [ ()    ]%= f
  (x ∷ xs) [ zero  ]%= f = f x ∷ xs
  (x ∷ xs) [ suc k ]%= f = x ∷ (xs [ k ]%= f)

  _[_]∷=_ : (xs : List A) → Fin (length xs) → A → List A
  xs [ k ]∷= v = xs [ k ]%= const v

  _─_ : (xs : List A) → Fin (length xs) → List A
  []       ─ ()
  (x ∷ xs) ─ zero  = xs
  (x ∷ xs) ─ suc k = x ∷ (xs ─ k)

------------------------------------------------------------------------
-- Operations for reversing lists

module _ {a} {A : Set a} where

  reverseAcc : List A → List A → List A
  reverseAcc = foldl (flip _∷_)

  reverse : List A → List A
  reverse = reverseAcc []

-- Snoc.

infixl 5 _∷ʳ_

_∷ʳ_ : ∀ {a} {A : Set a} → List A → A → List A
xs ∷ʳ x = xs ++ [ x ]

-- Backwards initialisation

infixl 5 _∷ʳ'_

data InitLast {a} {A : Set a} : List A → Set a where
  []    : InitLast []
  _∷ʳ'_ : (xs : List A) (x : A) → InitLast (xs ∷ʳ x)

initLast : ∀ {a} {A : Set a} → (xs : List A) → InitLast xs
initLast []               = []
initLast (x ∷ xs)         with initLast xs
initLast (x ∷ .[])        | []       = [] ∷ʳ' x
initLast (x ∷ .(ys ∷ʳ y)) | ys ∷ʳ' y = (x ∷ ys) ∷ʳ' y

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.
--
-- Note that the `boolX` functions are not given warnings as they are
-- used by other deprecated proofs throughout the library.

-- Version 0.15

gfilter = mapMaybe
{-# WARNING_ON_USAGE gfilter
"Warning: gfilter was deprecated in v0.15.
Please use mapMaybe instead."
#-}

boolFilter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
boolFilter p = mapMaybe (λ x → if p x then just x else nothing)

boolPartition : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
boolPartition p []       = ([] , [])
boolPartition p (x ∷ xs) with p x | boolPartition p xs
... | true  | (ys , zs) = (x ∷ ys , zs)
... | false | (ys , zs) = (ys , x ∷ zs)

-- Version 0.16

boolTakeWhile : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
boolTakeWhile p []       = []
boolTakeWhile p (x ∷ xs) with p x
... | true  = x ∷ boolTakeWhile p xs
... | false = []

boolDropWhile : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
boolDropWhile p []       = []
boolDropWhile p (x ∷ xs) with p x
... | true  = boolDropWhile p xs
... | false = x ∷ xs

boolSpan : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
boolSpan p []       = ([] , [])
boolSpan p (x ∷ xs) with p x
... | true  = Prod.map (x ∷_) id (boolSpan p xs)
... | false = ([] , x ∷ xs)

boolBreak : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
boolBreak p = boolSpan (not ∘ p)
