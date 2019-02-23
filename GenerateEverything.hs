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

-- | Checks whether a module is declared (un)safe

isUnsafeModule :: FilePath -> Bool
isUnsafeModule = flip elem $ map toAgdaFilePath
  [ "Data.Char.Unsafe"
  , "Data.Float.Unsafe"
  , "Data.Nat.Unsafe"
  , "Data.Nat.DivMod.Unsafe"
  , "Data.String.Unsafe"
  , "Data.Word.Unsafe"
  , "Debug.Trace"
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

-- | Returns 'True' for all Agda files except for core modules.

isLibraryModule :: FilePath -> Bool
isLibraryModule f =
  takeExtension f `elem` [".agda", ".lagda"]
  && dropExtension (takeFileName f) /= "Core"


-- | Extracts the header.

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
  | unsafe && safe = error $ fp ++ contradiction
  | unsafe         = Unsafe
  | guardedness    = SafeGuardedness
  | sizedtypes     = SafeSizedTypes
  | safe           = Safe
  | otherwise      = error $ fp ++ uncategorized

  where

    unsafe      = isUnsafeModule fp
    option str  = List.isSubsequenceOf ["{-#", "OPTIONS", str, "#-}"]
    options     = words <$> filter (List.isInfixOf "OPTIONS") ls
    guardedness = not $ null $ filter (option "--guardedness") options
    sizedtypes  = not $ null $ filter (option "--sized-types") options
    safe        = not $ null $ filter (option "--safe") options

    contradiction = " is declared unsafe but uses the --safe option."
    uncategorized = " is not declared unsafe but not using the --safe option either."

-- | Analyse a file

data LibraryFile = LibraryFile
  { filepath   :: FilePath
  , header     :: [String]
  , safety     :: Safety
  }

analyse :: FilePath -> IO LibraryFile
analyse fp = do
  ls <- lines <$> readFileUTF8 fp
  let safe = not $ isUnsafeModule fp
  return $ LibraryFile
    { filepath   = fp
    , header     = extractHeader fp ls
    , safety     = classify fp ls
    }


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

format :: [LibraryFile]
          -- ^ Pairs of module names and headers. All lines in the
          -- headers are already prefixed with \"-- \".
       -> String
format = unlines . concat . map fmt
  where
  fmt lf = "" : header lf ++ ["import " ++ fileToMod (filepath lf)]

-- | Translates a file name to the corresponding module name. It is
-- assumed that the file name corresponds to an Agda module under
-- 'srcDir'.

fileToMod :: FilePath -> String
fileToMod = map slashToDot . dropExtension . makeRelative srcDir
  where
  slashToDot c | isPathSeparator c = '.'
               | otherwise         = c

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
