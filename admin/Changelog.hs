{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Changelog where

import Control.Applicative
import Control.Monad
import Control.Monad.State

import Data.Char
import Data.Functor
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import System.Directory
import System.FilePath

import Debug.Trace

changesFP :: FilePath
changesFP = "changes"

bugfixesFP :: FilePath
bugfixesFP = "bugfixes"

highlightsFP :: FilePath
highlightsFP = "highlights"

newFP :: FilePath
newFP = "new"

deprecatedFP :: FilePath
deprecatedFP = "deprecated"

type HIGHLIGHTS = [[String]]
type BUGFIXES = [[String]]
  -- Items

type DEPRECATED = Map String [(String,String)]
  -- ^ map of module name * renamings
type NEW = Map String [String]
  -- ^ map of module name * new definitions

data CHANGELOG = CHANGELOG
  { highlights :: HIGHLIGHTS
  , bugfixes   :: BUGFIXES
  , deprecated :: DEPRECATED
  , new        :: NEW
  }

data STATE = STATE
  { pullRequests :: [String]  -- one directory per PR
  }

newtype ChangeM a = ChangeM { runChangeM :: StateT STATE IO a }
  deriving (Functor, Applicative, Monad, MonadState STATE, MonadIO)

evalChangeM :: ChangeM a -> STATE -> IO a
evalChangeM = evalStateT . runChangeM

getFilePaths :: (FilePath -> IO Bool) -> FilePath -> IO [FilePath]
getFilePaths p fp = do
  b  <- doesDirectoryExist fp
  if not b then pure [] else do
    fps <- map (fp </>) <$> listDirectory fp
    filterM p fps

getDirectories :: FilePath -> IO [FilePath]
getDirectories = getFilePaths doesDirectoryExist

getFiles :: FilePath -> IO [FilePath]
getFiles = getFilePaths (\ fp -> (check fp &&) <$> doesFileExist fp)

  where check = all (\ c -> isAlphaNum c || c `elem` "./")

initSTATE :: IO STATE
initSTATE = do
  -- one directory per PR
  dirs <- getDirectories changesFP
  pure $ STATE dirs

inspect :: FilePath -> ChangeM [FilePath]
inspect fp = do
  dirs <- map (</> fp) . pullRequests <$> get
  fps <- liftIO (mapM getFiles dirs)
  pure $ concat fps

nonEmptyLinesOf :: FilePath -> IO [String]
nonEmptyLinesOf fp = do
  ls <- lines <$> readFile fp
  pure $ filter (not . all isSpace) ls

paragraphs :: [String] -> [[String]]
paragraphs [] = []
paragraphs xs = case break (all isSpace) xs of
  ([], p:ps) -> paragraphs ps
  (p , []  ) -> [p]
  (p , _:ps) -> p : paragraphs ps

items :: FilePath -> ChangeM [[String]]
items fp = do
  fps <- map (</> fp) . pullRequests <$> get
  fps <- liftIO $ filterM doesFileExist fps
  fmap concat $ forM fps $ \ fp -> do
    ls <- liftIO (lines <$> readFile fp)
    pure (paragraphs ls)

mkHIGHLIGHTS :: ChangeM HIGHLIGHTS
mkHIGHLIGHTS = items highlightsFP

mkBUGFIXES :: ChangeM BUGFIXES
mkBUGFIXES = items bugfixesFP

mkDEPRECATED :: ChangeM DEPRECATED
mkDEPRECATED = fmap ($ []) <$> do
  fps  <- inspect deprecatedFP
  rens <- forM fps $ \ fp -> do
    ls  <- liftIO $ nonEmptyLinesOf fp
    pqs <- forM ls $ \ l -> case words l of
      [p,q] -> pure (p,q)
      _     -> error $ unlines [ "ERROR: invalid line"
                               , l
                               , "in file " ++ fp
                               ]
    pure $ Map.singleton (takeFileName fp) (pqs ++)
  pure $ foldr (Map.unionWith (.)) Map.empty rens

mkNEW :: ChangeM NEW
mkNEW = fmap ($ []) <$> do
  fps  <- inspect newFP
  news <- forM fps $ \ fp -> do
    ls <- liftIO $ nonEmptyLinesOf fp
    pure $ Map.singleton (takeFileName fp) (ls ++)
  pure $ foldr (Map.unionWith (.)) Map.empty news

mkCHANGELOG :: ChangeM CHANGELOG
mkCHANGELOG = CHANGELOG
          <$> mkHIGHLIGHTS
          <*> mkBUGFIXES
          <*> mkDEPRECATED
          <*> mkNEW

prAGDA :: [String] -> [String]
prAGDA ls = concat
  [ [ "  ```agda" ]
  , ls
  , [ "  ```" ]
  ]

prItems :: [[String]] -> [String]
prItems is = intercalate [""] $ do
  ls <- is
  pure $ zipWith (++) ("* " : repeat "  ") ls

prHIGHLIGHTS :: HIGHLIGHTS -> [String]
prHIGHLIGHTS h = preamble ++ prItems h where

  preamble =
    [ ""
    , "Highlights"
    , "----------"
    , ""
    ]

prBUGFIXES :: BUGFIXES -> [String]
prBUGFIXES h = preamble ++ prItems h where

  preamble =
    [ ""
    , "Bug fixes"
    , "---------"
    , ""
    ]

prNEW :: NEW -> [String]
prNEW n = (preamble ++) $ intercalate [""] $ do
  (mod, defs) <- Map.toAscList n
  pure $ concat ["* New definitions in `", mod, "`:"]
       : prAGDA (map additions defs)
  where
  additions = ("  " ++)
  preamble =
    [ ""
    , "Other minor additions"
    , "---------------------"
    , ""
    ]

prDEPRECATED :: DEPRECATED -> [String]
prDEPRECATED d = (preamble ++) $ intercalate [""] $ do
  (mod, pairs) <- Map.toAscList d
  pure $ concat [ "* In `", mod, "`:" ]
       : prAGDA (map renamings pairs)
  where
  renamings (p, q) = concat [ "  ", p, " ↦ ", q ]
  preamble =
    [ ""
    , "Deprecated names"
    , "----------------"
    , ""
    , "The following deprecations have occurred as part of a drive to improve"
    , "consistency across the library. The deprecated names still exist and"
    , "therefore all existing code should still work, however use of the new"
    , "names is encouraged. Although not anticipated any time soon, they may"
    , "eventually be removed in some future release of the library. Automated"
    , "warnings are attached to all deprecated names to discourage their use."
    , ""
    ]

unlessNull :: Foldable t => (t a -> [b]) -> t a -> [b]
unlessNull f t = if null t then [] else f t

pretty :: CHANGELOG -> [String]
pretty c = concat
  [ unlessNull prHIGHLIGHTS (highlights c)
  , unlessNull prBUGFIXES   (bugfixes c)
  , unlessNull prDEPRECATED (deprecated c)
  , unlessNull prNEW        (new c)
  ]

main :: IO ()
main = do
  st <- initSTATE
  ch <- evalChangeM mkCHANGELOG st
  let txt = unlines $ pretty ch
  trace txt $ pure ()
  writeFile "CHANGELOG.md" txt
