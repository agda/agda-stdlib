------------------------------------------------------------------------
-- The Agda standard library
--
-- The Covec type and some operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Covec where

open import Size using (Size ; ∞)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Conat as Conat
  using (Conat ; zero ; suc; _+_; infinity; fromℕ; _ℕ+_)
open import Codata.Sized.Conat.Bisimilarity using (_⊢_≈_; zero; suc)
open import Codata.Sized.Conat.Properties using (0ℕ+-identity)
open import Codata.Sized.Cofin as Cofin using (Cofin; zero; suc)
open import Codata.Sized.Colist as Colist using (Colist ; [] ; _∷_)
open import Codata.Sized.Stream as Stream using (Stream ; _∷_)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

data Covec (A : Set a) (i : Size) : Conat ∞ → Set a where
  []  : Covec A i zero
  _∷_ : ∀ {n} → A → Thunk (λ i → Covec A i (n .force)) i → Covec A i (suc n)

infixr 5 _∷_

head : ∀ {n i} → Covec A i (suc n) → A
head (x ∷ _) = x

tail : ∀ {n} → Covec A ∞ (suc n) → Covec A ∞ (n .force)
tail (_ ∷ xs) = xs .force

lookup : ∀ {n} → Covec A ∞ n → Cofin n → A
lookup as zero    = head as
lookup as (suc k) = lookup (tail as) k

replicate : ∀ {i} → (n : Conat ∞) → A → Covec A i n
replicate zero    a = []
replicate (suc n) a = a ∷ λ where .force → replicate (n .force) a

cotake : ∀ {i} → (n : Conat ∞) → Stream A i → Covec A i n
cotake zero    xs       = []
cotake (suc n) (x ∷ xs) = x ∷ λ where .force → cotake (n .force) (xs .force)

infixr 5 _++_
_++_ : ∀ {i m n} → Covec A i m → Covec A i n → Covec A i (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ λ where .force → xs .force ++ ys

fromColist : ∀ {i} → (xs : Colist A ∞) → Covec A i (Colist.length xs)
fromColist []       = []
fromColist (x ∷ xs) = x ∷ λ where .force → fromColist (xs .force)

toColist : ∀ {i n} → Covec A i n → Colist A i
toColist []       = []
toColist (x ∷ xs) = x ∷ λ where .force → toColist (xs .force)

fromStream : ∀ {i} → Stream A i → Covec A i infinity
fromStream = cotake infinity

cast : ∀ {i} {m n} → i ⊢ m ≈ n → Covec A i m → Covec A i n
cast zero     []       = []
cast (suc eq) (a ∷ as) = a ∷ λ where .force → cast (eq .force) (as .force)

module _ {a b} {A : Set a} {B : Set b} where

 map : ∀ {i n} (f : A → B) → Covec A i n → Covec B i n
 map f []       = []
 map f (a ∷ as) = f a ∷ λ where .force → map f (as .force)

 ap : ∀ {i n} → Covec (A → B) i n → Covec A i n → Covec B i n
 ap []       []       = []
 ap (f ∷ fs) (a ∷ as) = (f a) ∷ λ where .force → ap (fs .force) (as .force)

 scanl : ∀ {i n} → (B → A → B) → B → Covec A i n → Covec B i (1 ℕ+ n)
 scanl c n []       = n ∷ λ where .force → []
 scanl c n (a ∷ as) = n ∷ λ where
   .force → cast (suc λ where .force → 0ℕ+-identity)
                 (scanl c (c n a) (as .force))

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 zipWith : ∀ {i n} → (A → B → C) → Covec A i n → Covec B i n → Covec C i n
 zipWith f []       []       = []
 zipWith f (a ∷ as) (b ∷ bs) =
   f a b ∷ λ where .force → zipWith f (as .force) (bs .force)
