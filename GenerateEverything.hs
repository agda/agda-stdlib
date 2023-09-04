{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}

import Control.Applicative
import Control.Monad
import Control.Monad.Except

import qualified Data.List as List
import qualified Data.List.NonEmpty as List1
import Data.List.NonEmpty ( pattern (:|) )
import Data.Maybe

import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.FilePath.Find
import System.IO

headerFile     = "Header"
allOutputFile  = "Everything"
safeOutputFile = "EverythingSafe"
srcDir         = "src"

---------------------------------------------------------------------------
-- Files with a special status

-- | Checks whether a module is declared (un)safe

unsafeModules :: [FilePath]
unsafeModules = map modToFile
  [ "Codata.Musical.Colist"
  , "Codata.Musical.Colist.Base"
  , "Codata.Musical.Colist.Properties"
  , "Codata.Musical.Colist.Bisimilarity"
  , "Codata.Musical.Colist.Relation.Unary.All"
  , "Codata.Musical.Colist.Relation.Unary.All.Properties"
  , "Codata.Musical.Colist.Relation.Unary.Any"
  , "Codata.Musical.Colist.Relation.Unary.Any.Properties"
  , "Codata.Musical.Colist.Infinite-merge"
  , "Codata.Musical.Costring"
  , "Codata.Musical.Covec"
  , "Codata.Musical.Conversion"
  , "Codata.Musical.Stream"
  , "Debug.Trace"
  , "Effect.Monad.IO"
  , "Effect.Monad.IO.Instances"
  , "Foreign.Haskell"
  , "Foreign.Haskell.Coerce"
  , "Foreign.Haskell.Either"
  , "Foreign.Haskell.Maybe"
  , "Foreign.Haskell.List.NonEmpty"
  , "Foreign.Haskell.Pair"
  , "IO"
  , "IO.Base"
  , "IO.Categorical"
  , "IO.Infinite"
  , "IO.Instances"
  , "IO.Effectful"
  , "IO.Finite"
  , "IO.Primitive"
  , "IO.Primitive.Infinite"
  , "IO.Primitive.Finite"
  , "Relation.Binary.PropositionalEquality.TrustMe"
  , "System.Clock"
  , "System.Clock.Primitive"
  , "System.Directory"
  , "System.Directory.Primitive"
  , "System.Environment"
  , "System.Environment.Primitive"
  , "System.Exit"
  , "System.Exit.Primitive"
  , "System.FilePath.Posix"
  , "System.FilePath.Posix.Primitive"
  , "System.Process"
  , "System.Process.Primitive"
  , "Test.Golden"
  , "Text.Pretty.Core"
  , "Text.Pretty"
  ] ++ sizedTypesModules

isUnsafeModule :: FilePath -> Bool
isUnsafeModule fp =
    unqualifiedModuleName fp == "Unsafe"
    || fp `elem` unsafeModules

-- | Checks whether a module is declared as using K

withKModules :: [FilePath]
withKModules = map modToFile
  [ "Axiom.Extensionality.Heterogeneous"
  , "Data.Star.BoundedVec"
  , "Data.Star.Decoration"
  , "Data.Star.Environment"
  , "Data.Star.Fin"
  , "Data.Star.Pointer"
  , "Data.Star.Vec"
  , "Data.String.Unsafe"
  , "Reflection.AnnotatedAST"
  , "Reflection.AnnotatedAST.Free"
  , "Relation.Binary.HeterogeneousEquality"
  , "Relation.Binary.HeterogeneousEquality.Core"
  , "Relation.Binary.HeterogeneousEquality.Quotients.Examples"
  , "Relation.Binary.HeterogeneousEquality.Quotients"
  , "Relation.Binary.PropositionalEquality.TrustMe"
  , "Text.Pretty.Core"
  , "Text.Pretty"
  , "Text.Regex.String.Unsafe"
  ]

isWithKModule :: FilePath -> Bool
isWithKModule =
  -- GA 2019-02-24: it is crucial to use an anonymous lambda
  -- here so that `withKModules` is shared between all calls
  -- to `isWithKModule`.
  \ fp -> unqualifiedModuleName fp == "WithK"
       || fp `elem` withKModules

sizedTypesModules :: [FilePath]
sizedTypesModules = map modToFile
  [ "Codata.Sized.Cofin"
  , "Codata.Sized.Cofin.Literals"
  , "Codata.Sized.Colist"
  , "Codata.Sized.Colist.Bisimilarity"
  , "Codata.Sized.Colist.Categorical"
  , "Codata.Sized.Colist.Effectful"
  , "Codata.Sized.Colist.Properties"
  , "Codata.Sized.Conat"
  , "Codata.Sized.Conat.Bisimilarity"
  , "Codata.Sized.Conat.Literals"
  , "Codata.Sized.Conat.Properties"
  , "Codata.Sized.Covec"
  , "Codata.Sized.Covec.Bisimilarity"
  , "Codata.Sized.Covec.Categorical"
  , "Codata.Sized.Covec.Effectful"
  , "Codata.Sized.Covec.Instances"
  , "Codata.Sized.Covec.Properties"
  , "Codata.Sized.Cowriter"
  , "Codata.Sized.Cowriter.Bisimilarity"
  , "Codata.Sized.Delay"
  , "Codata.Sized.Delay.Bisimilarity"
  , "Codata.Sized.Delay.Categorical"
  , "Codata.Sized.Delay.Effectful"
  , "Codata.Sized.Delay.Properties"
  , "Codata.Sized.M"
  , "Codata.Sized.M.Bisimilarity"
  , "Codata.Sized.M.Properties"
  , "Codata.Sized.Stream"
  , "Codata.Sized.Stream.Bisimilarity"
  , "Codata.Sized.Stream.Categorical"
  , "Codata.Sized.Stream.Effectful"
  , "Codata.Sized.Stream.Instances"
  , "Codata.Sized.Stream.Properties"
  , "Codata.Sized.Thunk"
  , "Data.Container.Fixpoints.Sized"
  , "Data.W.Sized"
  , "Data.Nat.PseudoRandom.LCG.Unsafe"
  , "Data.Tree.Binary.Show"
  , "Data.Tree.Rose"
  , "Data.Tree.Rose.Properties"
  , "Data.Tree.Rose.Show"
  , "Data.Trie"
  , "Data.Trie.NonEmpty"
  , "Relation.Unary.Sized"
  , "Size"
  , "Text.Tree.Linear"
  ]

isSizedTypesModule :: FilePath -> Bool
isSizedTypesModule =
  \ fp -> fp `elem` sizedTypesModules

unqualifiedModuleName :: FilePath -> String
unqualifiedModuleName = dropExtension . takeFileName

-- | Returns 'True' for all Agda files except for core modules.

isLibraryModule :: FilePath -> Bool
isLibraryModule f =
  takeExtension f `elem` [".agda", ".lagda"]
  && unqualifiedModuleName f /= "Core"

---------------------------------------------------------------------------
-- Analysing library files

type Exc = Except String

-- | Extracting the header.

-- It needs to have the form:
-- ------------------------------------------------------------------------
-- -- The Agda standard library
-- --
-- -- Description of the module
-- ------------------------------------------------------------------------

extractHeader :: FilePath -> [String] -> Exc [String]
extractHeader mod = extract
  where
  delimiter = all (== '-')

  extract :: [String] -> Exc [String]
  extract (d1 : "-- The Agda standard library" : "--" : ss)
    | delimiter d1
    , (info, d2 : rest) <- span ("-- " `List.isPrefixOf`) ss
    , delimiter d2
    = pure $ info
  extract (d1@(c:cs) : _)
    | not (delimiter d1)
      -- Andreas, issue #1510: there is a haunting of Prelude.last, so use List1.last instead.
      -- See https://gitlab.haskell.org/ghc/ghc/-/issues/19917.
      -- Update: The haunting is also resolved by 'throwError' instead of 'error',
      -- but still I dislike Prelude.last.
    , List1.last (c :| cs) == '\r'
    = throwError $ unwords
      [ mod
      , "contains \\r, probably due to git misconfiguration;"
      , "maybe set autocrf to input?"
      ]
  extract _ = throwError $ unwords
      [ mod
      , "is malformed."
      , "It needs to have a module header."
      , "Please see other existing files or consult HACKING.md."
      ]

-- | A crude classifier looking for lines containing options

data Status = Deprecated | Unsafe | Safe
  deriving (Eq)

classify :: FilePath -> [String] -> [String] -> Exc Status
classify fp hd ls
  -- We start with sanity checks
  | isUnsafe && safe          = throwError $ fp ++ contradiction "unsafe" "safe"
  | not (isUnsafe || safe)    = throwError $ fp ++ uncategorized "unsafe" "safe"
  | isWithK && cubicalC       = throwError $ fp ++ contradiction "as relying on K" "cubical-compatible"
  | isWithK && not withK      = throwError $ fp ++ missingWithK
  | not (isWithK || cubicalC) = throwError $ fp ++ uncategorized "as relying on K" "cubical-compatible"
  -- And then perform the actual classification
  | deprecated                = pure $ Deprecated
  | isUnsafe                  = pure $ Unsafe
  | safe                      = pure $ Safe
  -- We know that @not (isUnsafe || safe)@, all cases are covered
  | otherwise                 = error "IMPOSSIBLE"

  where

    -- based on declarations
    isWithK  = isWithKModule fp
    isUnsafe = isUnsafeModule fp

    -- based on detected OPTIONS
    safe        = option "--safe"
    withK       = option "--with-K"
    cubicalC    = option "--cubical-compatible"

    -- based on detected comment in header
    deprecated  = let detect = List.isSubsequenceOf "This module is DEPRECATED."
                  in any detect hd

    -- GA 2019-02-24: note that we do not reprocess the whole module for every
    -- option check: the shared @options@ definition ensures we only inspect a
    -- handful of lines (at most one, ideally)
    option str = let detect = List.isSubsequenceOf ["{-#", "OPTIONS", str, "#-}"]
                  in any detect options
    options    = words <$> filter (List.isInfixOf "OPTIONS") ls

    -- formatting error messages
    contradiction d o = unwords
      [ " is declared", d, "but uses the", "--" ++ o, "option." ]
    uncategorized d o = unwords
      [ " is not declared", d, "but not using the", "--" ++ o, "option either." ]

    missingWithK = " is declared as relying on K but not using the --with-K option."

-- | Analyse a file: extracting header and classifying it.

data LibraryFile = LibraryFile
  { filepath   :: FilePath -- ^ FilePath of the source file
  , header     :: [String] -- ^ All lines in the headers are already prefixed with \"-- \".
  , status     :: Status   -- ^ Safety options used by the module
  }

analyse :: FilePath -> IO LibraryFile
analyse fp = do
  ls <- lines <$> readFileUTF8 fp
  hd <- runExc $ extractHeader fp ls
  cl <- runExc $ classify fp hd ls
  return $ LibraryFile
    { filepath   = fp
    , header     = hd
    , status     = cl
    }

checkFilePaths :: String -> [FilePath] -> IO ()
checkFilePaths cat fps = forM_ fps $ \ fp -> do
  b <- doesFileExist fp
  unless b $
    die $ fp ++ " is listed as " ++ cat ++ " but does not exist."

---------------------------------------------------------------------------
-- Collecting all non-Core library files, analysing them and generating
-- 4 files:
-- Everything.agda                 all the modules
-- EverythingSafe.agda             all the safe modules

main = do
  args <- getArgs
  includeDeprecated <- case args of
    [] -> return False
    ["--include-deprecated"] -> return True
    _  -> hPutStr stderr usage >> exitFailure

  checkFilePaths "unsafe" unsafeModules
  checkFilePaths "using K" withKModules

  header  <- readFileUTF8 headerFile
  modules <- filter isLibraryModule . List.sort <$>
               find always
                    (extension ==? ".agda" ||? extension ==? ".lagda")
                    srcDir
  libraryfiles <- (if includeDeprecated then id
    else (filter ((Deprecated /=) . status) <$>)) (mapM analyse modules)

  let mkModule str = "module " ++ str ++ " where"

  writeFileUTF8 (allOutputFile ++ ".agda") $
    unlines [ header
            , "{-# OPTIONS --rewriting --guardedness --sized-types #-}\n"
            , mkModule allOutputFile
            , format libraryfiles
            ]

  writeFileUTF8 (safeOutputFile ++ ".agda") $
    unlines [ header
            , "{-# OPTIONS --safe --guardedness #-}\n"
            , mkModule safeOutputFile
            , format $ filter ((Unsafe /=) . status) libraryfiles
            ]

-- | Usage info.

usage :: String
usage = unlines
  [ "GenerateEverything: A utility program for Agda's standard library."
  , ""
  , "Usage: GenerateEverything"
  , ""
  , "This program should be run in the base directory of a clean checkout of"
  , "the library."
  , ""
  , "The program generates documentation for the library by extracting"
  , "headers from library modules. The output is written to " ++ allOutputFile
  , "with the file " ++ headerFile ++ " inserted verbatim at the beginning."
  ]


-- | Formats the extracted module information.

format :: [LibraryFile] -> String
format = unlines . concatMap fmt
  where
  fmt lf = "" : header lf ++ ["import " ++ fileToMod (filepath lf)]

-- | Translates back and forth between a file name and the corresponding module
--   name. We assume that the file name corresponds to an Agda module under
--   'srcDir'.

fileToMod :: FilePath -> String
fileToMod = map slashToDot . dropExtension . makeRelative srcDir
  where
  slashToDot c | isPathSeparator c = '.'
               | otherwise         = c

modToFile :: String -> FilePath
modToFile name = concat [ srcDir, [pathSeparator], map dotToSlash name, ".agda" ]
  where
  dotToSlash c | c == '.'  = pathSeparator
               | otherwise = c

-- | A variant of 'readFile' which uses the 'utf8' encoding.

readFileUTF8 :: FilePath -> IO String
readFileUTF8 f = do
  h <- openFile f ReadMode
  hSetEncoding h utf8
  s <- hGetContents h
  length s `seq` return s

-- | A variant of 'writeFile' which uses the 'utf8' encoding.

writeFileUTF8 :: FilePath -> String -> IO ()
writeFileUTF8 f s = withFile f WriteMode $ \h -> do
  hSetEncoding h utf8
  hPutStr h s

-- | Turning exceptions into fatal errors.

runExc :: Exc a -> IO a
runExc = either die return . runExcept
