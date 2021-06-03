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
open import Codata.Musical.Cofin hiding (module Cofin)
open import Codata.Musical.Colist hiding (module Colist)
open import Codata.Musical.Conat
open import Codata.Musical.Covec hiding (module Covec)
open import Codata.Musical.M hiding (module M)
open import Codata.Musical.Notation
open import Codata.Musical.Stream hiding (module Stream)
open import Codata.Thunk
open import Data.Product
open import Data.Container.Core as C using (Container)
import Size

private
  variable
    a : Level
    A : Set a

module Colist where

  fromMusical : ∀ {i} → Colist A → Sized.Colist A i
  fromMusical []       = Sized.[]
  fromMusical (x ∷ xs) = x Sized.∷ λ where .force → fromMusical (♭ xs)

  toMusical : Sized.Colist A Size.∞ → Colist A
  toMusical Sized.[]       = []
  toMusical (x Sized.∷ xs) = x ∷ ♯ toMusical (xs .force)

module Conat where

  fromMusical : ∀ {i} → Coℕ → Sized.Conat i
  fromMusical zero    = Sized.zero
  fromMusical (suc n) = Sized.suc λ where .force → fromMusical (♭ n)

  toMusical : Sized.Conat Size.∞ → Coℕ
  toMusical Sized.zero    = zero
  toMusical (Sized.suc n) = suc (♯ toMusical (n .force))

module Cofin where

  fromMusical : ∀ {n} → Cofin n → Sized.Cofin (Conat.fromMusical n)
  fromMusical zero    = Sized.zero
  fromMusical (suc n) = Sized.suc (fromMusical n)

  toMusical : ∀ {n} → Sized.Cofin n → Cofin (Conat.toMusical n)
  toMusical Sized.zero    = zero
  toMusical (Sized.suc n) = suc (toMusical n)

module Covec where

  fromMusical : ∀ {i n} → Covec A n → Sized.Covec A i (Conat.fromMusical n)
  fromMusical []       = Sized.[]
  fromMusical (x ∷ xs) = x Sized.∷ λ where .force → fromMusical (♭ xs)

  toMusical : ∀ {n} → Sized.Covec A Size.∞ n → Covec A (Conat.toMusical n)
  toMusical Sized.[]       = []
  toMusical (x Sized.∷ xs) = x ∷ ♯ toMusical (xs .force)

module M {s p} {C : Container s p} where

  fromMusical : ∀ {i} → M C → Codata.M.M C i
  fromMusical (inf t) = Codata.M.inf (C.map rec t) where
    rec = λ x → λ where .force → fromMusical (♭ x)

  toMusical : Codata.M.M C Size.∞ → M C
  toMusical (Codata.M.inf (s , f)) = inf (s , λ p → ♯ toMusical (f p .force))

module Stream where

  fromMusical : ∀ {i} → Stream A → Sized.Stream A i
  fromMusical (x ∷ xs) = x Sized.∷ λ where .force → fromMusical (♭ xs)

  toMusical : Sized.Stream A Size.∞ → Stream A
  toMusical (x Sized.∷ xs) = x ∷ ♯ toMusical (xs .force)
