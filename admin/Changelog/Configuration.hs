module Changelog.Configuration where

import System.FilePath

changesFP :: FilePath
changesFP = "changes"

bugfixesFP :: FilePath
bugfixesFP = changesFP </> "bugfixes"

breakingFP :: FilePath
breakingFP = changesFP </> "breaking"

highlightsFP :: FilePath
highlightsFP = changesFP </> "highlights"

newFP :: FilePath
newFP = changesFP </> "new"

deprecatedFP :: FilePath
deprecatedFP = changesFP </> "deprecated"
