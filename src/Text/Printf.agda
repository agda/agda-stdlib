------------------------------------------------------------------------
-- The Agda standard library
--
-- Printf
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Text.Printf where

open import Level using (0ℓ; Lift)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Product.Nary.NonDependent
open import Data.String.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Function.Nary.NonDependent
open import Function
open import Strict

import Data.Char.Base    as Cₛ
import Data.Integer.Show as ℤₛ
import Data.Float        as Fₛ
import Data.Nat.Show     as ℕₛ

open import Text.Format as Format hiding (Error)
open import Text.Printf.Generic

printfSpec : PrintfSpec formatSpec String
printfSpec .PrintfSpec.renderArg ℕArg      = ℕₛ.show
printfSpec .PrintfSpec.renderArg ℤArg      = ℤₛ.show
printfSpec .PrintfSpec.renderArg FloatArg  = Fₛ.show
printfSpec .PrintfSpec.renderArg CharArg   = fromChar
printfSpec .PrintfSpec.renderArg StringArg = id
printfSpec .PrintfSpec.renderStr           = id

module Printf = Type formatSpec
open Printf public hiding (map)
open Render printfSpec public renaming (printf to gprintf)

printf : (fmt : String) → Printf (lexer fmt) String
printf fmt = Printf.map (lexer fmt) concat (gprintf fmt)
