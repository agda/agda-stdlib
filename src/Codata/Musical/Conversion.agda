------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion between coinductive data structures using "musical"
-- coinduction and the ones using sized types.
--
-- Warning: the combination of --sized-types and --guardedness is
-- known to be unsound, so use these conversions at your own risk.
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types --guardedness #-}

module Codata.Musical.Conversion where

open import Level using (Level)
import Codata.Cofin as Sized
import Codata.Colist as Sized
import Codata.Conat as Sized
import Codata.Covec as Sized
import Codata.M
import Codata.Stream as Sized
open import Codata.Musical.Cofin
open import Codata.Musical.Colist
open import Codata.Musical.Conat
open import Codata.Musical.Covec
open import Codata.Musical.M
open import Codata.Musical.Notation
open import Codata.Musical.Stream
open import Codata.Thunk
open import Data.Product
open import Data.Container.Core as C using (Container)
import Size

private
  variable
    a : Level
    A : Set a

fromMusicalColist : ∀ {i} → Colist A → Sized.Colist A i
fromMusicalColist []       = Sized.[]
fromMusicalColist (x ∷ xs) = x Sized.∷ λ where .force → fromMusicalColist (♭ xs)

toMusicalColist : Sized.Colist A Size.∞ → Colist A
toMusicalColist Sized.[]       = []
toMusicalColist (x Sized.∷ xs) = x ∷ ♯ toMusicalColist (xs .force)

fromMusicalConat : ∀ {i} → Coℕ → Sized.Conat i
fromMusicalConat zero    = Sized.zero
fromMusicalConat (suc n) = Sized.suc λ where .force → fromMusicalConat (♭ n)

toMusicalConat : Sized.Conat Size.∞ → Coℕ
toMusicalConat Sized.zero    = zero
toMusicalConat (Sized.suc n) = suc (♯ toMusicalConat (n .force))

fromMusicalCofin : ∀ {n} → Cofin n → Sized.Cofin (fromMusicalConat n)
fromMusicalCofin zero    = Sized.zero
fromMusicalCofin (suc n) = Sized.suc (fromMusicalCofin n)

toMusicalCofin : ∀ {n} → Sized.Cofin n → Cofin (toMusicalConat n)
toMusicalCofin Sized.zero    = zero
toMusicalCofin (Sized.suc n) = suc (toMusicalCofin n)

fromMusicalCovec : ∀ {i n} → Covec A n → Sized.Covec A i (fromMusicalConat n)
fromMusicalCovec []       = Sized.[]
fromMusicalCovec (x ∷ xs) = x Sized.∷ λ where .force → fromMusicalCovec (♭ xs)

toMusicalCovec : ∀ {n} → Sized.Covec A Size.∞ n → Covec A (toMusicalConat n)
toMusicalCovec Sized.[]       = []
toMusicalCovec (x Sized.∷ xs) = x ∷ ♯ toMusicalCovec (xs .force)

module _ {s p} {C : Container s p} where

  fromMusicalM : ∀ {i} → M C → Codata.M.M C i
  fromMusicalM (inf t) = Codata.M.inf (C.map rec t) where
    rec = λ x → λ where .force → fromMusicalM (♭ x)

  toMusicalM : Codata.M.M C Size.∞ → M C
  toMusicalM (Codata.M.inf (s , f)) = inf (s , λ p → ♯ toMusicalM (f p .force))

fromMusicalStream : ∀ {i} → Stream A → Sized.Stream A i
fromMusicalStream (x ∷ xs) = x Sized.∷ λ where .force → fromMusicalStream (♭ xs)

toMusicalStream : Sized.Stream A Size.∞ → Stream A
toMusicalStream (x Sized.∷ xs) = x ∷ ♯ toMusicalStream (xs .force)
