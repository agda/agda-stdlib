------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive lists: base type and functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Codata.Musical.Colist.Base where

open import Level using (Level)
open import Codata.Musical.Notation
open import Codata.Musical.Conat.Base using (Coℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty.Base using (List⁺; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Colist (A : Set a) : Set a where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

{-# FOREIGN GHC
  data AgdaColist a    = Nil | Cons a (MAlonzo.RTE.Inf (AgdaColist a))
  type AgdaColist' l a = AgdaColist a
  #-}
{-# COMPILE GHC Colist = data AgdaColist' (Nil | Cons) #-}
{-# COMPILE UHC Colist = data __LIST__ (__NIL__ | __CONS__) #-}

------------------------------------------------------------------------
-- Some operations

null : Colist A → Bool
null []      = true
null (_ ∷ _) = false

length : Colist A → Coℕ
length []       = zero
length (x ∷ xs) = suc (♯ length (♭ xs))

map : (A → B) → Colist A → Colist B
map f []       = []
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

fromList : List A → Colist A
fromList []       = []
fromList (x ∷ xs) = x ∷ ♯ fromList xs

replicate : Coℕ → A → Colist A
replicate zero    x = []
replicate (suc n) x = x ∷ ♯ replicate (♭ n) x

lookup : ℕ → Colist A → Maybe A
lookup n       []       = nothing
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : Colist A → Colist A → Colist A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

-- Interleaves the two colists (until the shorter one, if any, has
-- been exhausted).

infixr 5 _⋎_

_⋎_ : Colist A → Colist A → Colist A
[]       ⋎ ys = ys
(x ∷ xs) ⋎ ys = x ∷ ♯ (ys ⋎ ♭ xs)

concat : Colist (List⁺ A) → Colist A
concat []                     = []
concat ((x ∷ [])       ∷ xss) = x ∷ ♯ concat (♭ xss)
concat ((x ∷ (y ∷ xs)) ∷ xss) = x ∷ ♯ concat ((y ∷ xs) ∷ xss)

[_] : A → Colist A
[ x ] = x ∷ ♯ []
