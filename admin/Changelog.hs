module Changelog where

import Control.Monad.State

import Data.Char
import Data.List
import qualified Data.Map.Strict as Map

import System.Directory
import System.FilePath

import Debug.Trace

import Changelog.Configuration
import Changelog.Types
import Changelog.Utils
import Changelog.Pretty

items :: FilePath -> ChangeM [[String]]
items fp = do
  fps <- liftIO $ getFiles fp
  fmap concat $ forM fps $ \ fp -> do
    ls <- liftIO (lines <$> readFile fp)
    pure (paragraphs ls)

oneOrTheOther :: FilePath -> ChangeM (OneOrTheOther String)
oneOrTheOther fp = do
  fps <- liftIO $ getFiles fp
  bfs <- forM fps $ \ fp -> case takeFileName fp of
    "others" -> do
      ls <- liftIO (lines <$> readFile fp)
      pure ([], paragraphs ls)
    _ -> do
      ls <- liftIO (lines <$> readFile fp)
      pure (ls, [])
  let (rs, iss) = unzip bfs
  let raw = filter (not . null) rs
  pure $ OneOrTheOther (intercalate [""] raw) (concat iss)

mkHIGHLIGHTS :: ChangeM HIGHLIGHTS
mkHIGHLIGHTS = items highlightsFP

mkBUGFIXES :: ChangeM BUGFIXES
mkBUGFIXES = oneOrTheOther bugfixesFP

mkBREAKING :: ChangeM BREAKING
mkBREAKING = oneOrTheOther breakingFP

mkDEPRECATED :: ChangeM DEPRECATED
mkDEPRECATED = fmap ($ []) <$> do
  fps  <- liftIO $ getFiles deprecatedFP
  rens <- forM fps $ \ fp -> do
    ls  <- liftIO $ nonEmptyLinesOf fp
    pqs <- forM ls $ \ l -> case words l of
      [p,q] -> pure (p,q)
      _     -> error $ unlines [ "ERROR: invalid line"
                               , "  " ++ l
                               , "in file " ++ fp
                               ]
    pure $ Map.singleton (takeFileName fp) (pqs ++)
  pure $ foldr (Map.unionWith (.)) Map.empty rens

mkMODULES :: ChangeM MODULES
mkMODULES = do
  fps <- liftIO $ getFiles modulesFP
  bfs <- forM fps $ \ fp -> do
    ls <- lines <$> (liftIO $ readFile fp)
    pure $ case takeFileName fp of
      "others" -> ([], ls)
      _ -> case break (all isSpace) ls of
        (hd, _:ps) -> case break (not . all isSpace) ps of
          (_, ps) -> ([(unlines (zipWith (++) ("* " : repeat "  ") hd)
                        , ps)
                       ], [])
        _ -> error $ unlines [ "ERROR: invalid file format " ++ fp ]
  let (rs, iss) = unzip bfs
  pure (concat rs, concat iss)


mkMINOR :: ChangeM MINOR
mkMINOR = fmap ($ []) <$> do
  fps  <- liftIO $ getFiles minorFP
  news <- forM fps $ \ fp -> do
    ls <- liftIO $ lines <$> readFile fp
    pure $ Map.singleton (takeFileName fp) (ls ++)
  pure $ foldr (Map.unionWith (.)) Map.empty news

mkCHANGELOG :: ChangeM CHANGELOG
mkCHANGELOG = CHANGELOG
          <$> mkHIGHLIGHTS
          <*> mkBUGFIXES
          <*> mkBREAKING
          <*> mkDEPRECATED
          <*> mkMODULES
          <*> mkMINOR

main :: IO ()
main = do
  ch <- evalChangeM mkCHANGELOG
  let txt = unlines $ pretty ch
  trace txt $ pure ()
  writeFile "CHANGELOG.md" txt
