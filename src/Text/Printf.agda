------------------------------------------------------------------------
-- The Agda standard library
--
-- Printf
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Text.Printf where

open import Data.String.Base using (String; fromChar; concat)
open import Function.Base using (id)

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
