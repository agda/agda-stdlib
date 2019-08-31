------------------------------------------------------------------------
-- The Agda standard library
--
-- A different interface to the Kleene lists, designed to mimic
-- Data.List.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Kleene.AsList where

open import Level as Level using (Level)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

import Data.List.Kleene.Base as Kleene

-- Here we import half of the functions from Data.KleeneList: the half
-- for possibly-empty lists.
open import Data.List.Kleene.Base
  using
    ( []
    )
  renaming
    ( _⋆ to List
    ; foldr⋆ to foldr
    ; foldl⋆ to foldl
    ; _++⋆_ to _++_
    ; map⋆ to map
    ; mapMaybe⋆ to mapMaybe
    ; pure⋆ to pure
    ; _<*>⋆_ to _<*>_
    ; _>>=⋆_ to _>>=_
    ; mapAccumˡ⋆ to mapAccumˡ
    ; mapAccumʳ⋆ to mapAccumʳ
    ; _[_]⋆ to _[_]
    ; applyUpTo⋆ to applyUpTo
    ; upTo⋆ to upTo
    ; zipWith⋆ to zipWith
    ; unzipWith⋆ to unzipWith
    ; partitionSumsWith⋆ to partitionSumsWith
    ; reverse⋆ to reverse
    )
  public

-- A pattern which mimics Data.List._∷_
infixr 5 _∷_
pattern _∷_ x xs = Kleene.∹ x Kleene.& xs

-- The following functions change the type of the list (from ⁺ to ⋆ or vice
-- versa) in Data.KleeneList, so we reimplement them here to keep the
-- type the same.
scanr : (A → B → B) → B → List A → List B
scanr f b xs = Kleene.∹ Kleene.scanr⋆ f b xs

scanl : (B → A → B) → B → List A → List B
scanl f b xs = Kleene.∹ Kleene.scanl⋆ f b xs

tails : List A → List (List A)
tails xs = foldr (λ x xs → (Kleene.∹ x) ∷ xs) ([] ∷ []) (Kleene.tails⋆ xs)
