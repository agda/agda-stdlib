module System.FilePath where

open import Data.String.Base

postulate
  RawFilePath : Set
  fromString : String → RawFilePath
