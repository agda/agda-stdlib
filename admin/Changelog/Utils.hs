module Changelog.Utils where

import Control.Monad
import Data.Char
import System.Directory
import System.FilePath

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

  where check = all (\ c -> isAlphaNum c || c `elem` "./-")

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
