{-# LANGUAGE OverloadedStrings #-}
-- | This module extracts all the non-ASCII characters used by the
-- library code (along with how many times they are used).

module Main where

import qualified Data.List as L (sortBy, group, sort)
import Data.Char (isAscii, ord)
import Data.Function (on)
import Numeric (showHex)
import System.FilePath.Find (find, always, extension, (||?), (==?))
import System.IO (openFile, hSetEncoding, utf8, IOMode(ReadMode))
import qualified Data.Text as T (Text, pack, unpack, concat)
import qualified Data.Text.IO as T (putStrLn, hGetContents)

readUTF8File :: FilePath -> IO T.Text
readUTF8File f = do
  h <- openFile f ReadMode
  hSetEncoding h utf8
  T.hGetContents h

main :: IO ()
main = do
  agdaFiles <- find always
                    (extension ==? ".agda" ||? extension ==? ".lagda")
                    "src"
  nonAsciiChars <-
    filter (not . isAscii) . T.unpack . T.concat <$> mapM readUTF8File agdaFiles
  let table :: [(Char, Int)]
      table = L.sortBy (flip compare `on` snd) $
              map (\cs -> (head cs, length cs)) $
              L.group $ L.sort $ nonAsciiChars

  let codePoint :: Char -> T.Text
      codePoint c = T.pack $ showHex (ord c) ""

      uPlus :: Char -> T.Text
      uPlus c = T.concat ["(U+", codePoint c, ")"]

  mapM_ (\(c, count) -> T.putStrLn $ T.concat [T.pack [c], " ", uPlus c, ": ", T.pack $ show count])
        table
