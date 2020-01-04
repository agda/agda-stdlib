module Changelog.Pretty where

import Data.List
import qualified Data.Map.Strict as Map

import Changelog.Types

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
