------------------------------------------------------------------------
-- The Agda standard library
--
-- ANSI escape codes
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module System.Console.ANSI where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; _+_)
import Data.Nat.Show as ℕ
open import Data.String.Base using (String; concat; intersperse)
open import Function.Base using (_$_; case_of_)

data Layer : Set where
  foreground background : Layer

data Colour : Set where
  black red green yellow blue magenta cyan white : Colour

data Intensity : Set where
  classic bright : Intensity

data Weight : Set where
  bold faint normal : Weight

data Underlining : Set where
  single double : Underlining

data Style : Set where
  italic straight : Style

data Blinking : Set where
  slow rapid : Blinking

data Command : Set where
  reset : Command
  setColour : Layer → Intensity → Colour → Command
  setWeight : Weight → Command
  setStyle : Style → Command
  setUnderline : Underlining → Command
  setBlinking : Blinking → Command

private

  escape : String → String
  escape txt = concat $ "\x1b[" ∷ txt ∷ "m" ∷ []

encode : Command → String
encode reset = "0"
encode (setColour l i c) = ℕ.show (layer l + colour c + intensity i)

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
  intensity classic = 0
  intensity bright  = 60

encode (setWeight w) = case w of λ where
  bold   → "1"
  faint  → "2"
  normal → "22"

encode (setStyle s) = case s of λ where
  italic → "3"
  straight → "23"

encode (setUnderline i) = case i of λ where
  single → "4"
  double → "21"

encode (setBlinking b) = case b of λ where
  slow → "5"
  rapid → "6"

command : Command → String
command c = escape (encode c)

withCommand : Command → String → String
withCommand c txt = concat (command c ∷ txt ∷ command reset ∷ [])

commands : List Command → String
commands [] = command reset
commands cs = escape (intersperse ";" $ List.map encode cs)

withCommands : List Command → String → String
withCommands cs txt = concat (commands cs ∷ txt ∷ command reset ∷ [])
