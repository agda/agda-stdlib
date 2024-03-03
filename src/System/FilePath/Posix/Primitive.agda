------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive System.FilePath.Posix simple bindings to Haskell functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module System.FilePath.Posix.Primitive where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.String using (String)
open import Foreign.Haskell as FFI using (Pair; Either)
open import IO.Primitive using (IO)

-- A filepath has a nature: it can be either relative or absolute.
-- We postulate this nature rather than defining it as an inductive
-- type so that the user cannot inspect it. The only way to cast an
-- arbitrary filepath nature @n@ to either @relative@ or @absolute@
-- is to use @checkFilePath@.

module Nature where

  postulate
    Nature : Set
    relative absolute unknown : Nature

-- In the Haskell backend these @natures@ are simply erased as the
-- libraries represent all filepaths in the same way.

  {-# FOREIGN GHC import Data.Kind     #-}
  {-# COMPILE GHC Nature   = type Type #-}
  {-# COMPILE GHC relative = type ()   #-}
  {-# COMPILE GHC absolute = type ()   #-}
  {-# COMPILE GHC unknown  = type ()   #-}

open Nature using (Nature) public

private
  variable
    m n : Nature

postulate

  FilePath     : Nature → Set
  getFilePath  : FilePath n → String

  Extension    : Set
  mkExtension  : String → Extension
  getExtension : Extension → String

{-# FOREIGN GHC import Data.Text                        #-}
{-# FOREIGN GHC import System.FilePath.Posix            #-}
{-# FOREIGN GHC type AgdaFilePath n = FilePath          #-}
{-# COMPILE GHC FilePath            = type AgdaFilePath #-}
{-# COMPILE GHC getFilePath         = const pack        #-}
{-# COMPILE GHC Extension           = type String       #-}
{-# COMPILE GHC mkExtension         = unpack            #-}
{-# COMPILE GHC getExtension        = pack              #-}

-- We provide convenient short names for the two types of filepaths

AbsolutePath = FilePath Nature.absolute
RelativePath = FilePath Nature.relative
SomePath     = FilePath Nature.unknown

-- In order to prevent users from picking whether a string gets
-- converted to a @relative@ or an @absolute@ path we have:
-- * a postulated @unknown@ nature
-- * a function @mkFilePath@ producing filepaths of this postulated nature

postulate
  mkFilePath : String → SomePath

{-# COMPILE GHC mkFilePath = unpack #-}

postulate

  -- Separator predicates

  pathSeparator         : Char
  pathSeparators        : List Char
  isPathSeparator       : Char → Bool
  searchPathSeparator   : Char
  isSearchPathSeparator : Char → Bool
  extSeparator          : Char
  isExtSeparator        : Char → Bool

  -- $PATH methods

  splitSearchPath : String → List SomePath
  getSearchPath   : IO (List SomePath)

  -- Extension functions

  splitExtension    : FilePath n → Pair (FilePath n) Extension
  takeExtension     : FilePath n → Extension
  replaceExtension  : FilePath n → Extension → FilePath n
  dropExtension     : FilePath n → FilePath n
  addExtension      : FilePath n → Extension → FilePath n
  hasExtension      : FilePath n → Bool
  splitExtensions   : FilePath n → Pair (FilePath n) Extension
  takeExtensions    : FilePath n → Extension
  replaceExtensions : FilePath n → Extension → FilePath n
  dropExtensions    : FilePath n → FilePath n
  isExtensionOf     : Extension → FilePath n → Bool
  stripExtension    : Extension → FilePath n → Maybe (FilePath n)

  -- Filename/directory functions

  splitFileName    : FilePath n → Pair (FilePath n) RelativePath
  takeFileName     : FilePath n → String
  replaceFileName  : FilePath n → String → FilePath n
  dropFileName     : FilePath n → FilePath n
  takeBaseName     : FilePath n → String
  replaceBaseName  : FilePath n → String → FilePath n
  takeDirectory    : FilePath n → FilePath n
  replaceDirectory : FilePath m → FilePath n → FilePath n
  combine          : FilePath n → RelativePath → FilePath n
  splitPath        : FilePath n → List RelativePath
  joinPath         : List RelativePath → RelativePath
  splitDirectories : FilePath n → List RelativePath

  -- Drive functions

  splitDrive : FilePath n → Pair (FilePath n) RelativePath
  joinDrive  : FilePath n → RelativePath → FilePath n
  takeDrive  : FilePath n → FilePath n
  hasDrive   : FilePath n → Bool
  dropDrive  : FilePath n → RelativePath
  isDrive    : FilePath n → Bool

  -- Trailing slash functions

  hasTrailingPathSeparator  : FilePath n → Bool
  addTrailingPathSeparator  : FilePath n → FilePath n
  dropTrailingPathSeparator : FilePath n → FilePath n

  -- File name manipulations

  normalise     : FilePath n → FilePath n
  equalFilePath : FilePath m → FilePath n → Bool
  makeRelative  : FilePath m → FilePath n → RelativePath
  checkFilePath : FilePath n → Either RelativePath AbsolutePath
  isRelative    : FilePath n → Bool
  isAbsolute    : FilePath n → Bool
  isValid       : FilePath n → Bool
  makeValid     : FilePath n → FilePath n


{-# FOREIGN GHC
checkFilePath fp
  | isRelative fp = Left fp
  | otherwise     = Right fp
#-}

{-# COMPILE GHC pathSeparator         = pathSeparator         #-}
{-# COMPILE GHC pathSeparators        = pathSeparators        #-}
{-# COMPILE GHC isPathSeparator       = isPathSeparator       #-}
{-# COMPILE GHC searchPathSeparator   = searchPathSeparator   #-}
{-# COMPILE GHC isSearchPathSeparator = isSearchPathSeparator #-}
{-# COMPILE GHC extSeparator          = extSeparator          #-}
{-# COMPILE GHC isExtSeparator        = isExtSeparator        #-}

{-# COMPILE GHC splitSearchPath = splitSearchPath . unpack #-}
{-# COMPILE GHC getSearchPath   = getSearchPath            #-}

{-# COMPILE GHC splitExtension    = const splitExtension    #-}
{-# COMPILE GHC takeExtension     = const takeExtension     #-}
{-# COMPILE GHC replaceExtension  = const replaceExtension  #-}
{-# COMPILE GHC dropExtension     = const dropExtension     #-}
{-# COMPILE GHC addExtension      = const addExtension      #-}
{-# COMPILE GHC hasExtension      = const hasExtension      #-}
{-# COMPILE GHC splitExtensions   = const splitExtensions   #-}
{-# COMPILE GHC takeExtensions    = const takeExtensions    #-}
{-# COMPILE GHC replaceExtensions = const replaceExtensions #-}
{-# COMPILE GHC dropExtensions    = const dropExtensions    #-}
{-# COMPILE GHC isExtensionOf     = const isExtensionOf     #-}
{-# COMPILE GHC stripExtension    = const stripExtension    #-}

{-# COMPILE GHC splitFileName    = const splitFileName                     #-}
{-# COMPILE GHC takeFileName     = const $ pack . takeFileName             #-}
{-# COMPILE GHC replaceFileName  = const $ fmap (. unpack) replaceFileName #-}
{-# COMPILE GHC dropFileName     = const dropFileName                      #-}
{-# COMPILE GHC takeBaseName     = const $ pack . takeBaseName             #-}
{-# COMPILE GHC replaceBaseName  = const $ fmap (. unpack) replaceBaseName #-}
{-# COMPILE GHC takeDirectory    = const takeDirectory                     #-}
{-# COMPILE GHC replaceDirectory = \ _ _ -> replaceDirectory               #-}
{-# COMPILE GHC combine          = const combine                           #-}
{-# COMPILE GHC splitPath        = const splitPath                         #-}
{-# COMPILE GHC joinPath         = joinPath                                #-}
{-# COMPILE GHC splitDirectories = const splitDirectories                  #-}

{-# COMPILE GHC splitDrive = const splitDrive #-}
{-# COMPILE GHC joinDrive  = const joinDrive  #-}
{-# COMPILE GHC takeDrive  = const takeDrive  #-}
{-# COMPILE GHC hasDrive   = const hasDrive   #-}
{-# COMPILE GHC dropDrive  = const dropDrive  #-}
{-# COMPILE GHC isDrive    = const isDrive    #-}

{-# COMPILE GHC hasTrailingPathSeparator  = const hasTrailingPathSeparator  #-}
{-# COMPILE GHC addTrailingPathSeparator  = const addTrailingPathSeparator  #-}
{-# COMPILE GHC dropTrailingPathSeparator = const dropTrailingPathSeparator #-}

{-# COMPILE GHC normalise     = const normalise        #-}
{-# COMPILE GHC equalFilePath = \ _ _ -> equalFilePath #-}
{-# COMPILE GHC makeRelative  = \ _ _ -> makeRelative  #-}
{-# COMPILE GHC isRelative    = const isRelative       #-}
{-# COMPILE GHC isAbsolute    = const isAbsolute       #-}
{-# COMPILE GHC checkFilePath = const checkFilePath    #-}
{-# COMPILE GHC isValid       = const isValid          #-}
{-# COMPILE GHC makeValid     = const makeValid        #-}
