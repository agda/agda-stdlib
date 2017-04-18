------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for Characters
------------------------------------------------------------------------
module Data.Char.Base where

open import Data.Nat.Base    using (ℕ)
open import Data.Bool.Base   using (Bool)
open import Data.String.Base using (String)
open import Data.Int

------------------------------------------------------------------------
-- Re-export the type from the Core module

open import Data.Char.Core using (Char) public

------------------------------------------------------------------------
-- Primitive operations

open import Agda.Builtin.Char   public using (primCharToNat; primCharEquality)
open import Agda.Builtin.String public using (primShowChar)

show : Char → String
show = primShowChar

toNat : Char → ℕ
toNat = primCharToNat

{-# IMPORT Data.Char #-}

data GeneralCategory : Set where
  uppercaseLetter : GeneralCategory
  lowercaseLetter : GeneralCategory
  titlecaseLetter : GeneralCategory
  modifierLetter : GeneralCategory
  otherLetter : GeneralCategory
  nonSpacingMark : GeneralCategory
  spacingCombiningMark : GeneralCategory
  enclosingMark : GeneralCategory
  decimalNumber : GeneralCategory
  letterNumber : GeneralCategory
  otherNumber : GeneralCategory
  connectorPunctuation : GeneralCategory
  dashPunctuation : GeneralCategory
  openPunctuation : GeneralCategory
  closePunctuation : GeneralCategory
  initialQuote : GeneralCategory
  finalQuote : GeneralCategory
  otherPunctuation : GeneralCategory
  mathSymbol : GeneralCategory
  currencySymbol : GeneralCategory
  modifierSymbol : GeneralCategory
  otherSymbol : GeneralCategory
  space : GeneralCategory
  lineSeparator : GeneralCategory
  paragraphSeparator : GeneralCategory
  control : GeneralCategory
  format : GeneralCategory
  surrogate : GeneralCategory
  privateUse : GeneralCategory
  notAssigned : GeneralCategory

{-# COMPILED_DATA GeneralCategory Data.Char.GeneralCategory
  Data.Char.UppercaseLetter
  Data.Char.LowercaseLetter
  Data.Char.TitlecaseLetter
  Data.Char.ModifierLetter
  Data.Char.OtherLetter
  Data.Char.NonSpacingMark
  Data.Char.SpacingCombiningMark
  Data.Char.EnclosingMark
  Data.Char.DecimalNumber
  Data.Char.LetterNumber
  Data.Char.OtherNumber
  Data.Char.ConnectorPunctuation
  Data.Char.DashPunctuation
  Data.Char.OpenPunctuation
  Data.Char.ClosePunctuation
  Data.Char.InitialQuote
  Data.Char.FinalQuote
  Data.Char.OtherPunctuation
  Data.Char.MathSymbol
  Data.Char.CurrencySymbol
  Data.Char.ModifierSymbol
  Data.Char.OtherSymbol
  Data.Char.Space
  Data.Char.LineSeparator
  Data.Char.ParagraphSeparator
  Data.Char.Control
  Data.Char.Format
  Data.Char.Surrogate
  Data.Char.PrivateUse
  Data.Char.NotAssigned
#-}

postulate
  isControl : Char -> Bool
  isSpace : Char -> Bool
  isLower : Char -> Bool
  isUpper : Char -> Bool
  isAlpha : Char -> Bool
  isAlphaNum : Char -> Bool
  isPrint : Char -> Bool
  isDigit : Char -> Bool
  isOctDigit : Char -> Bool
  isHexDigit : Char -> Bool
  isLetter : Char -> Bool
  isMark : Char -> Bool
  isNumber : Char -> Bool
  isPunctuation : Char -> Bool
  isSymbol : Char -> Bool
  isSeparator : Char -> Bool
  isAscii : Char -> Bool
  isLatin1 : Char -> Bool
  isAsciiUpper : Char -> Bool
  isAsciiLower : Char -> Bool
  generalCategory : Char -> GeneralCategory
  toUpper : Char -> Char
  toLower : Char -> Char
  toTitle : Char -> Char
  digitToInt : Char -> Int
  intToDigit : Int -> Char
  ord : Char -> Int
  chr : Int -> Char

{-# COMPILED isControl Data.Char.isControl #-}
{-# COMPILED isSpace Data.Char.isSpace #-}
{-# COMPILED isLower Data.Char.isLower #-}
{-# COMPILED isUpper Data.Char.isUpper #-}
{-# COMPILED isAlpha Data.Char.isAlpha #-}
{-# COMPILED isAlphaNum Data.Char.isAlphaNum #-}
{-# COMPILED isPrint Data.Char.isPrint #-}
{-# COMPILED isDigit Data.Char.isDigit #-}
{-# COMPILED isOctDigit Data.Char.isOctDigit #-}
{-# COMPILED isHexDigit Data.Char.isHexDigit #-}
{-# COMPILED isLetter Data.Char.isLetter #-}
{-# COMPILED isMark Data.Char.isMark #-}
{-# COMPILED isNumber Data.Char.isNumber #-}
{-# COMPILED isPunctuation Data.Char.isPunctuation #-}
{-# COMPILED isSymbol Data.Char.isSymbol #-}
{-# COMPILED isSeparator Data.Char.isSeparator #-}
{-# COMPILED isAscii Data.Char.isAscii #-}
{-# COMPILED isLatin1 Data.Char.isLatin1 #-}
{-# COMPILED isAsciiUpper Data.Char.isAsciiUpper #-}
{-# COMPILED isAsciiLower Data.Char.isAsciiLower #-}
{-# COMPILED generalCategory Data.Char.generalCategory #-}
{-# COMPILED toUpper Data.Char.toUpper #-}
{-# COMPILED toLower Data.Char.toLower #-}
{-# COMPILED toTitle Data.Char.toTitle #-}
{-# COMPILED digitToInt Data.Char.digitToInt #-}
{-# COMPILED intToDigit Data.Char.intToDigit #-}
{-# COMPILED ord Data.Char.ord #-}
{-# COMPILED chr Data.Char.chr #-}
