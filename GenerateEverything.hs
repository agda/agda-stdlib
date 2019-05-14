{-# LANGUAGE PatternGuards #-}

import Control.Applicative

import qualified Data.List as List

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
unsafeModules = map toAgdaFilePath
  [ "Codata.Musical.Cofin"
  , "Codata.Musical.Colist"
  , "Codata.Musical.Colist.Infinite-merge"
  , "Codata.Musical.Conat"
  , "Codata.Musical.Costring"
  , "Codata.Musical.Covec"
  , "Codata.Musical.M"
  , "Codata.Musical.Stream"
  , "Data.Char.Unsafe"
  , "Data.Float.Unsafe"
  , "Data.Nat.Unsafe"
  , "Data.Nat.DivMod.Unsafe"
  , "Data.String.Unsafe"
  , "Data.Word.Unsafe"
  , "Debug.Trace"
  , "Foreign.Haskell"
  , "IO"
  , "IO.Primitive"
  , "Reflection"
  , "Relation.Binary.PropositionalEquality.TrustMe"
  ] where

  toAgdaFilePath :: String -> FilePath
  toAgdaFilePath name = concat
    [ "src/"
    , map (\ c -> if c == '.' then '/' else c) name
    , ".agda"
    ]

isUnsafeModule :: FilePath -> Bool
isUnsafeModule =
  -- GA 2019-02-24: it is crucial to use an anonymous lambda
  -- here so that `unsafeModules` is shared between all calls
  -- to `isUnsafeModule`.
  \ fp -> unqualifiedModuleName fp == "Unsafe"
       || fp `elem` unsafeModules

-- | Checks whether a module is declared as using K

isWithKModule :: FilePath -> Bool
isWithKModule =
  -- GA 2019-02-24: it is crucial to use an anonymous lambda
  -- here so that `withKModules` is shared between all calls
  -- to `isWithKModule`.
  \ fp -> unqualifiedModuleName fp == "WithK"
       || fp `elem` withKModules

  where

  withKModules :: [FilePath]
  withKModules = map modToFile
    [ "Axiom.Extensionality.Heterogeneous"
    , "Data.Char.Unsafe"
    , "Data.Float.Unsafe"
    , "Data.Nat.Unsafe"
    , "Data.Nat.DivMod.Unsafe"
    , "Data.Star.BoundedVec"
    , "Data.Star.Decoration"
    , "Data.Star.Environment"
    , "Data.Star.Fin"
    , "Data.Star.Pointer"
    , "Data.Star.Vec"
    , "Data.String.Unsafe"
    , "Data.Word.Unsafe"
    , "Reflection"
    , "Relation.Binary.HeterogeneousEquality"
    , "Relation.Binary.HeterogeneousEquality.Core"
    , "Relation.Binary.HeterogeneousEquality.Quotients.Examples"
    , "Relation.Binary.HeterogeneousEquality.Quotients"
    , "Relation.Binary.PropositionalEquality.TrustMe"
    ]

unqualifiedModuleName :: FilePath -> String
unqualifiedModuleName = dropExtension . takeFileName

-- | Returns 'True' for all Agda files except for core modules.

isLibraryModule :: FilePath -> Bool
isLibraryModule f =
  takeExtension f `elem` [".agda", ".lagda"]
  && unqualifiedModuleName f /= "Core"


---------------------------------------------------------------------------
-- Analysing library files

-- | Extracting the header.

-- It needs to have the form:
-- ------------------------------------------------------------------------
-- -- The Agda standard library
-- --
-- -- Description of the module
-- ------------------------------------------------------------------------

-- | Reads a module and extracts the header.

extractHeader :: FilePath -> [String] -> [String]
extractHeader mod = extract
  where
  delimiter = all (== '-')

  extract (d1 : "-- The Agda standard library" : "--" : ss)
    | delimiter d1
    , (info, d2 : rest) <- span ("-- " `List.isPrefixOf`) ss
    , delimiter d2
    = info
  extract (d1 : _)
    | not (delimiter d1)
    , last d1 == '\r'
    = error $ mod ++ " contains \\r, probably due to git misconfiguration; maybe set autocrf to input?"
  extract _ = error $ unwords [ mod ++ " is malformed."
                              , "It needs to have a module header."
                              , "Please see other existing files or consult HACKING.md."
                              ]

-- | A crude classifier looking for lines containing options & trying to guess
--   whether the safe file is using either @--guardedness@ or @--sized-types@

data Safety = Unsafe | Safe | SafeGuardedness | SafeSizedTypes
  deriving (Eq)

classify :: FilePath -> [String] -> Safety
classify fp ls
  -- We start with sanity checks
  | isUnsafe && safe          = error $ fp ++ contradiction "unsafe" "safe"
  | not (isUnsafe || safe)    = error $ fp ++ uncategorized "unsafe" "safe"
  | isWithK && withoutK       = error $ fp ++ contradiction "as relying on K" "without-K"
  | isWithK && not withK      = error $ fp ++ missingWithK
  | not (isWithK || withoutK) = error $ fp ++ uncategorized "as relying on K" "without-K"
  -- And then perform the actual classification
  | isUnsafe                  = Unsafe
  | guardedness               = SafeGuardedness
  | sizedtypes                = SafeSizedTypes
  | safe                      = Safe
  -- We know that @not (isUnsafe || safe)@, all cases are covered
  | otherwise                 = error "IMPOSSIBLE"

  where

    -- based on declarations
    isWithK  = isWithKModule fp
    isUnsafe = isUnsafeModule fp

    -- based on detected OPTIONS
    guardedness = option "--guardedness"
    sizedtypes  = option "--sized-types"
    safe        = option "--safe"
    withK       = option "--with-K"
    withoutK    = option "--without-K"

    -- GA 2019-02-24: note that we do not reprocess the whole module for every
    -- option check: the shared @options@ definition ensures we only inspect a
    -- handful of lines (at most one, ideally)
    option str = let detect = List.isSubsequenceOf ["{-#", "OPTIONS", str, "#-}"]
                  in not $ null $ filter detect options
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
  , safety     :: Safety   -- ^ Safety options used by the module
  }

analyse :: FilePath -> IO LibraryFile
analyse fp = do
  ls <- lines <$> readFileUTF8 fp
  return $ LibraryFile
    { filepath   = fp
    , header     = extractHeader fp ls
    , safety     = classify fp ls
    }

---------------------------------------------------------------------------
-- Collecting all non-Core library files, analysing them and generating
-- 4 files:
-- Everything.agda                 all the modules
-- EverythingSafe.agda             all the safe modules (may be incompatible)
-- EverythingSafeGuardedness.agda  all the safe modules using --guardedness
-- EverythingSafeSizedTypes.agda   all the safe modules using --sized-types

main = do
  args <- getArgs
  case args of
    [] -> return ()
    _  -> hPutStr stderr usage >> exitFailure

  header  <- readFileUTF8 headerFile
  modules <- filter isLibraryModule . List.sort <$>
               find always
                    (extension ==? ".agda" ||? extension ==? ".lagda")
                    srcDir
  libraryfiles <- mapM analyse modules

  let mkModule str = "module " ++ str ++ " where"

  writeFileUTF8 (allOutputFile ++ ".agda") $
    unlines [ header
            , mkModule allOutputFile
            , format libraryfiles
            ]

  writeFileUTF8 (safeOutputFile ++ ".agda") $
    unlines [ header
            , "{-# OPTIONS --guardedness --sized-types #-}\n"
            , mkModule safeOutputFile
            , format $ filter ((Unsafe /=) . safety) libraryfiles
            ]

  let safeGuardednessOutputFile = safeOutputFile ++ "Guardedness"
  writeFileUTF8 (safeGuardednessOutputFile ++ ".agda") $
    unlines [ header
            , "{-# OPTIONS --safe --guardedness #-}\n"
            , mkModule safeGuardednessOutputFile
            , format $ filter ((SafeGuardedness ==) . safety) libraryfiles
            ]

  let safeSizedTypesOutputFile = safeOutputFile ++ "SizedTypes"
  writeFileUTF8 (safeSizedTypesOutputFile ++ ".agda") $
    unlines [ header
            , "{-# OPTIONS --safe --sized-types #-}\n"
            , mkModule safeSizedTypesOutputFile
            , format $ filter ((SafeSizedTypes ==) . safety) libraryfiles
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
format = unlines . concat . map fmt
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
