module Changelog.Pretty where

import Data.List
import qualified Data.Map.Strict as Map

import Changelog.Types

preamble :: String -> [String]
preamble str =
  [ ""
  , str
  , replicate (length str) '-'
  ]

prAGDA :: [String] -> [String]
prAGDA ls = concat
  [ [ "  ```agda" ]
  , map ("  " ++) ls
  , [ "  ```" ]
  ]

prItems :: [[String]] -> [String]
prItems is = intercalate [""] $ do
  ls <- is
  pure $ zipWith (++) ("* " : repeat "  ") ls

prHIGHLIGHTS :: HIGHLIGHTS -> [String]
prHIGHLIGHTS h = preamble "Highlights" ++ prItems h where

prOneOrTheOther :: OneOrTheOther String -> [String]
prOneOrTheOther (OneOrTheOther raw others) = concat
  [ unlessNull ("":)          [] raw
  , unlessNull (("":) . rest) [] others
  ] where

  banner = [ "#### Other", "" ]
  rest o = unlessNull (const (banner ++)) id raw $ prItems o

prBUGFIXES :: BUGFIXES -> [String]
prBUGFIXES b = concat
  [ preamble "Bug fixes"
  , prOneOrTheOther b
  ]

prBREAKING :: BREAKING -> [String]
prBREAKING b = concat
  [ preamble "Non-backwards compatible changes"
  , prOneOrTheOther b
  ]

prMODULES :: MODULES -> [String]
prMODULES (is, others) = concat
  [ preamble "New modules"
  , unlessNull ("":)          [] (map highlighted is)
  , unlessNull (("":) . rest) [] others
  ] where

  banner = [ "#### Other", "" ]
  rest = unlessNull (const (banner ++)) id is . prAGDA
  highlighted (hd, ms) = unlines $ hd : "" : prAGDA ms

prMINOR :: MINOR -> [String]
prMINOR n = (preamble "Other minor additions" ++) . ("" :) $ intercalate [""] $ do
  (mod, defs) <- Map.toAscList n
  pure $ concat ["* New definitions in `", mod, "`:"]
       : prAGDA defs

prDEPRECATED :: DEPRECATED -> [String]
prDEPRECATED d = (preamble ++) $ intercalate [""] $ do
  (mod, pairs) <- Map.toAscList d
  pure $ concat [ "* In `", mod, "`:" ]
       : prAGDA (map renamings pairs)
  where
  renamings (p, q) = concat [ p, " ↦ ", q ]
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

unlessNull :: Foldable t => (t a -> b) -> b -> t a -> b
unlessNull f b t = if null t then b else f t

pretty :: CHANGELOG -> [String]
pretty c = concat
  [ unlessNull prHIGHLIGHTS [] (highlights c)
  , unlessNull prBUGFIXES   [] (bugfixes c)
  , unlessNull prBREAKING   [] (breaking c)
  , unlessNull prDEPRECATED [] (deprecated c)
  , unlessNull prMODULES    [] (modules c)
  , unlessNull prMINOR      [] (minor c)
  ]
