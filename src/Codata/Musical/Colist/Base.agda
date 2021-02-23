------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive lists: base type and functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types --guardedness #-}

module Codata.Musical.Colist.Base where

open import Codata.Musical.Notation
open import Codata.Musical.Conat.Base using (Coℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc)

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Colist {a} (A : Set a) : Set a where
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

null : ∀ {a} {A : Set a} → Colist A → Bool
null []      = true
null (_ ∷ _) = false

length : ∀ {a} {A : Set a} → Colist A → Coℕ
length []       = zero
length (x ∷ xs) = suc (♯ length (♭ xs))

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Colist A → Colist B
map f []       = []
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

fromList : ∀ {a} {A : Set a} → List A → Colist A
fromList []       = []
fromList (x ∷ xs) = x ∷ ♯ fromList xs

replicate : ∀ {a} {A : Set a} → Coℕ → A → Colist A
replicate zero    x = []
replicate (suc n) x = x ∷ ♯ replicate (♭ n) x

lookup : ∀ {a} {A : Set a} → ℕ → Colist A → Maybe A
lookup n       []       = nothing
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → Colist A → Colist A → Colist A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)
