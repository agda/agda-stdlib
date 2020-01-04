module Changelog where

import Control.Monad.State

import qualified Data.Map.Strict as Map

import System.Directory
import System.FilePath

import Debug.Trace

import Changelog.Configuration
import Changelog.Types
import Changelog.Utils
import Changelog.Pretty

getPRFiles :: FilePath -> ChangeM [FilePath]
getPRFiles fp = do
  fps <- map (</> fp) . pullRequests <$> get
  liftIO $ filterM doesFileExist fps

inspect :: FilePath -> ChangeM [FilePath]
inspect fp = do
  dirs <- map (</> fp) . pullRequests <$> get
  fps <- liftIO (mapM getFiles dirs)
  pure $ concat fps

items :: FilePath -> ChangeM [[String]]
items fp = do
  fps <- getPRFiles fp
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

main :: IO ()
main = do
  st <- initSTATE
  ch <- evalChangeM mkCHANGELOG st
  let txt = unlines $ pretty ch
  trace txt $ pure ()
  writeFile "CHANGELOG.md" txt
