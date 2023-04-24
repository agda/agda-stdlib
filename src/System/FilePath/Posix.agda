------------------------------------------------------------------------
-- The Agda standard library
--
-- Posix filepaths
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module System.FilePath.Posix where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import IO.Base using (IO; lift)
open import Data.Maybe.Base using (Maybe)
open import Data.Product using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Function

open import Foreign.Haskell.Coerce

open import System.FilePath.Posix.Primitive as Prim
  public
  -- Some of these functions are not directly re-exported because their
  -- respective types mentions FFI-friendly versions of the stdlib's types
  -- e.g. `Pair` instead of `_×_`.
  -- A wrapper is systematically defined below using Foreign.Haskell.Coerce's
  -- zero-cost coercion to expose a more useful function to users.
  using ( module Nature
        ; Nature
        ; FilePath
        ; mkFilePath
        ; getFilePath
        ; AbsolutePath
        ; RelativePath
        ; SomePath
        ; Extension
        ; mkExtension
        ; getExtension
     -- Separator predicates
        ; pathSeparator
        ; pathSeparators
        ; isPathSeparator
        ; searchPathSeparator
        ; isSearchPathSeparator
        ; extSeparator
        ; isExtSeparator
     -- $PATH methods
        ; splitSearchPath
     -- ; getSearchPath see below: lift needed
     -- Extension functions
     -- ; splitExtension see below: coerce needed
        ; takeExtension
        ; replaceExtension
        ; dropExtension
        ; addExtension
        ; hasExtension
        ; takeExtensions
        ; replaceExtensions
        ; dropExtensions
        ; isExtensionOf
     -- ; stripExtension see below: coerce needed
     -- Filename/directory functions
     -- ; splitFileName see below: coerce needed
        ; takeFileName
        ; replaceFileName
        ; dropFileName
        ; takeBaseName
        ; replaceBaseName
        ; takeDirectory
        ; replaceDirectory
        ; combine
        ; splitPath
        ; joinPath
        ; splitDirectories
      -- Trailing slash functions
        ; hasTrailingPathSeparator
        ; addTrailingPathSeparator
        ; dropTrailingPathSeparator
     -- File name manipulations
        ; normalise
        ; equalFilePath
        ; makeRelative
     -- ; checkFilePath see below: coerce needed
        ; isRelative
        ; isAbsolute
        ; isValid
        ; makeValid
        )

private
  variable
    m n : Nature

-- singleton type for Nature
data KnownNature : Nature → Set where
  instance
    absolute : KnownNature Nature.absolute
    relative : KnownNature Nature.relative

currentDirectory : SomePath
currentDirectory = mkFilePath "."

splitExtension  : FilePath n → FilePath n × Extension
splitExtension = coerce Prim.splitExtension

splitExtensions : FilePath n → FilePath n × Extension
splitExtensions = coerce Prim.splitExtensions

stripExtension : Extension → FilePath n → Maybe (FilePath n)
stripExtension = coerce Prim.stripExtension

getSearchPath : IO (List SomePath)
getSearchPath = lift Prim.getSearchPath

splitFileName : FilePath n → FilePath n × RelativePath
splitFileName = coerce Prim.splitFileName

checkFilePath : FilePath n → RelativePath ⊎ AbsolutePath
checkFilePath = coerce Prim.checkFilePath
