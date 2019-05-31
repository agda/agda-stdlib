------------------------------------------------------------------------
-- The Agda standard library
--
-- Format strings for Printf and Scanf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Format where

open import Level using (0ℓ)
open import Data.List.Base as List
open import Function.Nary.NonDependent
open import Data.Product.Nary.NonDependent
open import Function

open import Data.Char.Base
open import Data.Integer.Base
open import Data.Float
open import Data.Nat.Base
open import Data.Product
open import Data.String.Base

data Chunk : Set where
  `ℕ `ℤ `Float `Char `String : Chunk
  Raw : String → Chunk

Format = List Chunk

size : Format → ℕ
size = List.sum ∘′ List.map λ { (Raw _) → 0; _ → 1 }

⟦_⟧ : (fmt : Format) → Sets (size fmt) 0ℓs
⟦ []           ⟧ = _
⟦ `ℕ      ∷ cs ⟧ = ℕ      , ⟦ cs ⟧
⟦ `ℤ      ∷ cs ⟧ = ℤ      , ⟦ cs ⟧
⟦ `Float  ∷ cs ⟧ = Float  , ⟦ cs ⟧
⟦ `Char   ∷ cs ⟧ = Char   , ⟦ cs ⟧
⟦ `String ∷ cs ⟧ = String , ⟦ cs ⟧
⟦ Raw _   ∷ cs ⟧ =          ⟦ cs ⟧

{-
format : List Char → List Chunk
format = go [] where

  push : List Char → List Chunk → List Chunk
  push [] ks = ks
  push cs ks = Raw (fromList (reverse cs)) ∷ ks

  go : List Char → List Char → List Chunk
  go acc []               = push acc []
  go acc ('%' ∷ '%' ∷ cs) = go ('%' ∷ acc) cs
  go acc ('%' ∷ 'd' ∷ cs) = push acc (`ℕ ∷ go [] cs)
  go acc (c ∷ cs) = go (c ∷ acc) cs
-}
