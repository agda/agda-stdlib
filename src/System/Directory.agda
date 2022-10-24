------------------------------------------------------------------------
-- The Agda standard library
--
-- Directory manipulation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module System.Directory where

open import Level
open import IO.Base
open import Data.Unit.Polymorphic.Base using (⊤)
open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String)
open import Foreign.Haskell.Coerce using (coerce)
open import Function
open import System.FilePath.Posix hiding (makeRelative)

open import System.Directory.Primitive as Prim
  public
  using ( XdgDirectory
        ; XdgData
        ; XdgConfig
        ; XdgCache
        ; XdgDirectoryList
        ; XdgDataDirs
        ; XdgConfigDirs
        ; exeExtension
        )

private
  variable
    a  : Level
    m n : Nature

-- Actions on directories

createDirectory           : FilePath n → IO {a} ⊤
createDirectoryIfMissing  : Bool → FilePath n → IO {a} ⊤
removeDirectory           : FilePath n → IO {a} ⊤
removeDirectoryRecursive  : FilePath n → IO {a} ⊤
removePathForcibly        : FilePath n → IO {a} ⊤
renameDirectory           : FilePath n → FilePath n → IO {a} ⊤
listDirectory             : FilePath n → IO (List RelativePath)

-- Current working directory

getDirectoryContents      : FilePath n → IO (List RelativePath)
getCurrentDirectory       : IO AbsolutePath
setCurrentDirectory       : FilePath n → IO {a} ⊤
withCurrentDirectory      : {A : Set a} → FilePath n → IO A → IO A

-- Pre-defined directories

getHomeDirectory          : IO AbsolutePath
getXdgDirectory           : XdgDirectory → RelativePath → IO AbsolutePath
getXdgDirectoryList       : XdgDirectoryList → IO (List AbsolutePath)
getAppUserDataDirectory   : RelativePath → IO AbsolutePath
getUserDocumentsDirectory : IO AbsolutePath
getTemporaryDirectory     : IO AbsolutePath

-- Action on files
removeFile           : FilePath m → IO {a} ⊤
renameFile           : FilePath m → FilePath n → IO {a} ⊤
renamePath           : FilePath m → FilePath n → IO {a} ⊤
copyFile             : FilePath m → FilePath n → IO {a} ⊤
copyFileWithMetadata : FilePath m → FilePath n → IO {a} ⊤
getFileSize          : FilePath n → IO ℕ
canonicalizePath     : FilePath n → IO AbsolutePath
makeAbsolute         : FilePath n → IO AbsolutePath
makeRelative         : FilePath n → IO RelativePath

toKnownNature : KnownNature m → FilePath n → IO (FilePath m)
toKnownNature absolute = makeAbsolute
toKnownNature relative = makeRelative

relativeToKnownNature : KnownNature n → RelativePath → IO (FilePath n)
absoluteToKnownNature : KnownNature n → AbsolutePath → IO (FilePath n)

relativeToKnownNature absolute = makeAbsolute
relativeToKnownNature relative = pure

absoluteToKnownNature absolute = pure
absoluteToKnownNature relative = makeRelative

-- Existence tests

doesPathExist                : FilePath n → IO Bool
doesFileExist                : FilePath n → IO Bool
doesDirectoryExist           : FilePath n → IO Bool
findExecutable               : String → IO (Maybe AbsolutePath)
findExecutables              : String → IO (List AbsolutePath)
findExecutablesInDirectories : List (FilePath n) → String → IO (List (FilePath n))
findFile                     : List (FilePath n) → String → IO (Maybe (FilePath n))
findFiles                    : List (FilePath n) → String → IO (List (FilePath n))
findFileWith                 : (FilePath n → IO Bool) → List (FilePath n) → String → IO (Maybe (FilePath n))
findFilesWith                : (FilePath n → IO Bool) → List (FilePath n) → String → IO (List (FilePath n))

-- Symbolic links

createFileLink        : FilePath m → FilePath n → IO {a} ⊤
createDirectoryLink   : FilePath m → FilePath n → IO {a} ⊤
removeDirectoryLink   : FilePath n → IO {a} ⊤
pathIsSymbolicLink    : FilePath n → IO Bool
getSymbolicLinkTarget : FilePath n → IO SomePath

createDirectory          = lift! ∘′ lift ∘′  Prim.createDirectory
createDirectoryIfMissing = λ b → lift! ∘′ lift ∘′ Prim.createDirectoryIfMissing b
removeDirectory          = lift! ∘′ lift ∘′ Prim.removeDirectory
removeDirectoryRecursive = lift! ∘′ lift ∘′ Prim.removeDirectoryRecursive
removePathForcibly       = lift! ∘′ lift ∘′ Prim.removePathForcibly
renameDirectory          = λ fp → lift! ∘′ lift ∘′ Prim.renameDirectory fp
listDirectory            = lift ∘′ Prim.listDirectory
getDirectoryContents     = lift ∘′ Prim.getDirectoryContents

getCurrentDirectory  = lift Prim.getCurrentDirectory
setCurrentDirectory  = lift! ∘′ lift ∘′ Prim.setCurrentDirectory
withCurrentDirectory = λ fp ma → lift (Prim.withCurrentDirectory fp (run ma))

getHomeDirectory          = lift Prim.getHomeDirectory
getXdgDirectory           = λ d fp → lift (Prim.getXdgDirectory d fp)
getXdgDirectoryList       = lift ∘′ Prim.getXdgDirectoryList
getAppUserDataDirectory   = lift ∘′ Prim.getAppUserDataDirectory
getUserDocumentsDirectory = lift Prim.getUserDocumentsDirectory
getTemporaryDirectory     = lift Prim.getTemporaryDirectory

removeFile           = lift! ∘′ lift ∘′ Prim.removeFile
renameFile           = λ a b → lift! (lift (Prim.renameFile a b))
renamePath           = λ a b → lift! (lift (Prim.renamePath a b))
copyFile             = λ a b → lift! (lift (Prim.copyFile a b))
copyFileWithMetadata = λ a b → lift! (lift (Prim.copyFileWithMetadata a b))
getFileSize          = lift ∘′ Prim.getFileSize
canonicalizePath     = lift ∘′ Prim.canonicalizePath
makeAbsolute         = lift ∘′ Prim.makeAbsolute
makeRelative         = lift ∘′ Prim.makeRelativeToCurrentDirectory

doesPathExist                = lift ∘′ Prim.doesPathExist
doesFileExist                = lift ∘′ Prim.doesFileExist
doesDirectoryExist           = lift ∘′ Prim.doesDirectoryExist
findExecutable               = lift ∘′ coerce ∘′ Prim.findExecutable
findExecutables              = lift ∘′ Prim.findExecutables
findExecutablesInDirectories = λ fps str → lift (Prim.findExecutablesInDirectories fps str)
findFile                     = λ fps str → lift (coerce Prim.findFile fps str)
findFiles                    = λ fps str → lift (Prim.findFiles fps str)
findFileWith                 = λ p fps str → lift (coerce Prim.findFileWith (run ∘′ p) fps str)
findFilesWith                = λ p fps str → lift (Prim.findFilesWith (run ∘′ p) fps str)

createFileLink        = λ fp → lift! ∘′ lift ∘′ Prim.createFileLink fp
createDirectoryLink   = λ fp → lift! ∘′ lift ∘′ Prim.createDirectoryLink fp
removeDirectoryLink   = lift! ∘′ lift ∘′ Prim.removeDirectoryLink
pathIsSymbolicLink    = lift ∘′ Prim.pathIsSymbolicLink
getSymbolicLinkTarget = lift ∘′ Prim.getSymbolicLinkTarget
