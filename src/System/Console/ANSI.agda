------------------------------------------------------------------------
-- The Agda standard library
--
-- ANSI escape codes
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module System.Console.ANSI where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; _+_)
import Data.Nat.Show as ℕ
open import Data.String.Base using (String; concat; intersperse)
open import Function.Base using (_$_)

data Layer : Set where
  foreground background : Layer

data Colour : Set where
  black red green yellow blue magenta cyan white : Colour

data Intensity : Set where
  normal bright : Intensity

record Command : Set where
  constructor mkCommand
  field
    layer : Layer
    intensity : Intensity
    colour : Colour

private

  escape : String → String
  escape txt = concat $ "\x1b[" ∷ txt ∷ "m" ∷ []

reset : String
reset = escape "0"

encode : Command → String
encode (mkCommand l i c) = ℕ.show (layer l + colour c + intensity i)

  where

  layer : Layer → ℕ
  layer foreground = 30
  layer background = 40

  colour : Colour → ℕ
  colour black   = 0
  colour red     = 1
  colour green   = 2
  colour yellow  = 3
  colour blue    = 4
  colour magenta = 5
  colour cyan    = 6
  colour white   = 7

  intensity : Intensity → ℕ
  intensity normal = 0
  intensity bright = 60

command : Command → String
command c = escape (encode c)

withCommand : Command → String → String
withCommand c txt = concat (command c ∷ txt ∷ reset ∷ [])

commands : List Command → String
commands [] = reset
commands cs = escape (intersperse ";" $ List.map encode cs)

withCommands : List Command → String → String
withCommands cs txt = concat (commands cs ∷ txt ∷ reset ∷ [])
