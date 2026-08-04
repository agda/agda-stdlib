{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFoldable             #-}

module Changelog.Types where

import Control.Monad.State
import Data.Map.Strict (Map)

import Changelog.Configuration
import Changelog.Utils

data OneOrTheOther a = OneOrTheOther
  { one      :: [a]
  , theOther :: [[a]]
  } deriving (Foldable)
-- ^ Foldable

type HIGHLIGHTS = [[String]]
type BUGFIXES   = OneOrTheOther String
  -- ^ Markdown for major ones + other items
type BREAKING   = OneOrTheOther String
  -- ^ Markdown for major ones + other items
type DEPRECATED = Map String [(String,String)]
  -- ^ map of module name * renamings
type MODULES = ([(String, [String])], [String])
  -- ^ Header + list of modules for major ones + other items
type MINOR = Map String [String]
  -- ^ map of module name * new definitions

data CHANGELOG = CHANGELOG
  { highlights :: HIGHLIGHTS
  , bugfixes   :: BUGFIXES
  , breaking   :: BREAKING
  , deprecated :: DEPRECATED
  , modules    :: MODULES
  , minor      :: MINOR
  }

newtype ChangeM a = ChangeM { runChangeM :: IO a }
  deriving (Functor, Applicative, Monad, MonadIO)

evalChangeM :: ChangeM a -> IO a
evalChangeM = runChangeM
