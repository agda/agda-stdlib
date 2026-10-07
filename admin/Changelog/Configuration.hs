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

modulesFP :: FilePath
modulesFP = changesFP </> "new_modules"

minorFP :: FilePath
minorFP = changesFP </> "minor_additions"

deprecatedFP :: FilePath
deprecatedFP = changesFP </> "deprecated"
