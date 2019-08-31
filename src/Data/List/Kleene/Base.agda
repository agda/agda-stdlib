------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists, based on the Kleene star and plus, basic types and operations.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Kleene.Base where

open import Data.Product as Product using (_×_; _,_; map₂; map₁; proj₁; proj₂)
open import Data.Nat     as ℕ       using (ℕ; suc; zero)
open import Data.Maybe   as Maybe   using (Maybe; just; nothing)
open import Data.Sum     as Sum     using (_⊎_; inj₁; inj₂)
open import Level        as Level   using (Level)

open import Algebra.FunctionProperties using (Op₂)
open import Function.Core

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definitions
--
-- These lists are exactly equivalent to normal lists, except the "cons"
-- case is split into its own data type. This lets us write all the same
-- functions as before, but it has 2 advantages:
--
-- * Some functions are easier to express on the non-empty type. Head,
--   for instance, has a natural safe implementation. Having the
--   non-empty type be defined mutually with the normal type makes the
--   use of this non-empty type occasionally more ergonomic.
-- * It can make some proofs easier. By using the non-empty type where
--   possible, we can avoid an extra pattern match, which can really
--   simplify certain proofs.

infixr 5 _&_ ∹_

record _+ {a} (A : Set a) : Set a
data _* {a} (A : Set a) : Set a

-- Non-Empty Lists
record _+ A where
  inductive
  constructor _&_
  field
    head : A
    tail : A *

-- Possibly Empty Lists
data _* A where
  [] : A *
  ∹_ : A + → A *
open _+ public

------------------------------------------------------------------------
-- Uncons

uncons : A * → Maybe (A +)
uncons []     = nothing
uncons (∹ xs) = just xs

------------------------------------------------------------------------
-- FoldMap

foldMap+ : Op₂ B → (A → B) → A + → B
foldMap+ _∙_ f (x & [])   = f x
foldMap+ _∙_ f (x & ∹ xs) = f x ∙ foldMap+ _∙_ f xs

foldMap* : Op₂ B → B → (A → B) → A * → B
foldMap* _∙_ ε f []     = ε
foldMap* _∙_ ε f (∹ xs) = foldMap+ _∙_ f xs

------------------------------------------------------------------------
-- Folds

module _ (f : A → B → B) (b : B) where
  foldr+ : A + → B
  foldr* : A * → B

  foldr+ (x & xs) = f x (foldr* xs)

  foldr* []     = b
  foldr* (∹ xs) = foldr+ xs

module _ (f : B → A → B) where
  foldl+ : B → A + → B
  foldl* : B → A * → B

  foldl+ b (x & xs) = foldl* (f b x) xs

  foldl* b []     = b
  foldl* b (∹ xs) = foldl+ b xs

------------------------------------------------------------------------
-- Concatenation

module Concat where
  _++++_ : A + → A + → A +
  _+++*_ : A + → A * → A +
  _*+++_ : A * → A + → A +
  _*++*_ : A * → A * → A *

  head (xs +++* ys) = head xs
  tail (xs +++* ys) = tail xs *++* ys

  xs *++* ys = foldr* (λ x zs → ∹ x & zs) ys xs

  xs ++++ ys = foldr+ (λ x zs → x & ∹ zs) ys xs

  []     *+++ ys = ys
  (∹ xs) *+++ ys = xs ++++ ys
open Concat public using () renaming (_++++_ to _+++_; _*++*_ to _++*_)

------------------------------------------------------------------------
-- Mapping

module _  (f : A → B) where
  map+ : A + → B +
  map* : A * → B *

  head (map+ xs) = f (head xs)
  tail (map+ xs) = map* (tail xs)

  map* []     = []
  map* (∹ xs) = ∹ map+ xs

module _ (f : A → Maybe B) where
  mapMaybe+ : A + → B *
  mapMaybe* : A * → B *

  mapMaybe+ (x & xs) with f x
  ... | just y  = ∹ y & mapMaybe* xs
  ... | nothing = mapMaybe* xs

  mapMaybe* []     = []
  mapMaybe* (∹ xs) = mapMaybe+ xs

------------------------------------------------------------------------
-- Applicative Operations

pure+ : A → A +
head (pure+ x) = x
tail (pure+ x) = []

pure* : A → A *
pure* x = ∹ pure+ x

module Apply where
  _*<*>*_ : (A → B) * → A * → B *
  _+<*>*_ : (A → B) + → A * → B *
  _*<*>+_ : (A → B) * → A + → B *
  _+<*>+_ : (A → B) + → A + → B +

  []     *<*>* xs = []
  (∹ fs) *<*>* xs = fs +<*>* xs

  fs +<*>* xs = map* (head fs) xs ++* (tail fs *<*>* xs)

  []     *<*>+ xs = []
  (∹ fs) *<*>+ xs = ∹ fs +<*>+ xs

  fs +<*>+ xs = map+ (head fs) xs Concat.+++* (tail fs *<*>+ xs)
open Apply public using () renaming (_*<*>*_ to _<*>*_; _+<*>+_ to _<*>+_)

------------------------------------------------------------------------
-- Monadic Operations

module Bind where
  _+>>=+_ : A + → (A → B +) → B +
  _+>>=*_ : A + → (A → B *) → B *
  _*>>=+_ : A * → (A → B +) → B *
  _*>>=*_ : A * → (A → B *) → B *

  (x & xs) +>>=+ k = k x Concat.+++* (xs *>>=+ k)

  (x & xs) +>>=* k = k x Concat.*++* (xs *>>=* k)

  []     *>>=* k = []
  (∹ xs) *>>=* k = xs +>>=* k

  []     *>>=+ k = []
  (∹ xs) *>>=+ k = ∹ xs +>>=+ k
open Bind public using () renaming (_*>>=*_ to _>>=*_; _+>>=+_ to _>>=+_)

------------------------------------------------------------------------
-- Scans

module Scanr (f : A → B → B) (b : B) where
  cons : A → B + → B +
  head (cons x xs) = f x (head xs)
  tail (cons x xs) = ∹ xs

  scanr+ : A + → B +
  scanr* : A * → B +

  scanr* = foldr* cons (b & [])
  scanr+ = foldr+ cons (b & [])
open Scanr public using (scanr+; scanr*)

module _ (f : B → A → B) where
  scanl* : B → A * → B +
  head (scanl* b xs)     = b
  tail (scanl* b [])     = []
  tail (scanl* b (∹ xs)) = ∹ scanl* (f b (head xs)) (tail xs)

  scanl+ : B → A + → B +
  head (scanl+ b xs) = b
  tail (scanl+ b xs) = ∹ scanl* (f b (head xs)) (tail xs)

  scanl₁ : B → A + → B +
  scanl₁ b xs = scanl* (f b (head xs)) (tail xs)

------------------------------------------------------------------------
-- Accumulating maps

module _ (f : B → A → (B × C)) where
  mapAccumˡ* : B → A * → (B × C *)
  mapAccumˡ+ : B → A + → (B × C +)

  mapAccumˡ* b []     = b , []
  mapAccumˡ* b (∹ xs) = map₂ ∹_ (mapAccumˡ+ b xs)

  mapAccumˡ+ b (x & xs) =
    let y , ys = f b x
        z , zs = mapAccumˡ* y xs
    in z , ys & zs

module _ (f : A → B → (C × B)) (b : B) where
  mapAccumʳ* : A * → (C * × B)
  mapAccumʳ+ : A + → (C + × B)

  mapAccumʳ* [] = [] , b
  mapAccumʳ* (∹ xs) = map₁ ∹_ (mapAccumʳ+ xs)

  mapAccumʳ+ (x & xs) =
    let ys , y = mapAccumʳ* xs
        zs , z = f x y
    in zs & ys , z

------------------------------------------------------------------------
-- Non-Empty Folds

last : A + → A
last (x & [])   = x
last (_ & ∹ xs) = last xs

module _ (f : A → A → A) where
  foldr₁ : A + → A
  foldr₁ (x & [])   = x
  foldr₁ (x & ∹ xs) = f x (foldr₁ xs)

  foldl₁ : A + → A
  foldl₁ (x & xs) = foldl* f x xs

module _ (f : A → Maybe B → B) where
  foldrMaybe* : A * → Maybe B
  foldrMaybe+ : A + → B

  foldrMaybe* []     = nothing
  foldrMaybe* (∹ xs) = just (foldrMaybe+ xs)

  foldrMaybe+ xs = f (head xs) (foldrMaybe* (tail xs))

------------------------------------------------------------------------
-- Indexing

_[_]* : A * → ℕ → Maybe A
_[_]+ : A + → ℕ → Maybe A

[]     [ _ ]* = nothing
(∹ xs) [ i ]* = xs [ i ]+

xs [ zero  ]+ = just (head xs)
xs [ suc i ]+ = tail xs [ i ]*

applyUpTo* : (ℕ → A) → ℕ → A *
applyUpTo+ : (ℕ → A) → ℕ → A +

applyUpTo* f zero    = []
applyUpTo* f (suc n) = ∹ applyUpTo+ f n

head (applyUpTo+ f n) = f zero
tail (applyUpTo+ f n) = applyUpTo* (f ∘ suc) n

upTo* : ℕ → ℕ *
upTo* = applyUpTo* id

upTo+ : ℕ → ℕ +
upTo+ = applyUpTo+ id

------------------------------------------------------------------------
-- Manipulation

module ZipWith (f : A → B → C) where
  +zipWith+ : A + → B + → C +
  *zipWith+ : A * → B + → C *
  +zipWith* : A + → B * → C *
  *zipWith* : A * → B * → C *

  head (+zipWith+ xs ys) = f (head xs) (head ys)
  tail (+zipWith+ xs ys) = *zipWith* (tail xs) (tail ys)

  *zipWith+ [] ys     = []
  *zipWith+ (∹ xs) ys = ∹ +zipWith+ xs ys

  +zipWith* xs []     = []
  +zipWith* xs (∹ ys) = ∹ +zipWith+ xs ys

  *zipWith* [] ys     = []
  *zipWith* (∹ xs) ys = +zipWith* xs ys
open ZipWith public renaming (+zipWith+ to zipWith+; *zipWith* to zipWith*)

module Unzip (f : A → B × C) where
  cons : B × C → B * × C * → B + × C +
  cons = Product.zip′ _&_ _&_

  unzipWith* : A * → B * × C *
  unzipWith+ : A + → B + × C +

  unzipWith* = foldr* (λ x xs → Product.map ∹_ ∹_ (cons (f x) xs)) ([] , [])

  unzipWith+ xs = cons (f (head xs)) (unzipWith* (tail xs))
open Unzip using (unzipWith+; unzipWith*) public

module Partition (f : A → B ⊎ C) where
  cons : B ⊎ C → B * × C * → B * × C *
  proj₁ (cons (inj₁ x) xs) = ∹ x & proj₁ xs
  proj₂ (cons (inj₁ x) xs) = proj₂ xs
  proj₂ (cons (inj₂ x) xs) = ∹ x & proj₂ xs
  proj₁ (cons (inj₂ x) xs) = proj₁ xs

  partitionSumsWith* : A * → B * × C *
  partitionSumsWith+ : A + → B * × C *

  partitionSumsWith* = foldr* (cons ∘ f) ([] , [])

  partitionSumsWith+ = foldr+ (cons ∘ f) ([] , [])
open Partition using (partitionSumsWith+; partitionSumsWith*) public

tails* : A * → (A +) *
tails+ : A + → (A +) +

head (tails+ xs) = xs
tail (tails+ xs) = tails* (tail xs)

tails* []     = []
tails* (∹ xs) = ∹ tails+ xs

reverse* : A * → A *
reverse* = foldl* (λ xs x → ∹ x & xs) []

reverse+ : A + → A +
reverse+ (x & xs) = foldl* (λ ys y → y & ∹ ys) (x & []) xs
