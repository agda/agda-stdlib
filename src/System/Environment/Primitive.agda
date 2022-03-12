------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive System.Environment: simple bindings to Haskell functions
--
-- Note that we currently leave out:
-- * filepath-related functions (until we have a good representation of
--   absolute vs. relative & directory vs. file)
-- * functions that may fail with an exception
--   e.g. we provide `lookupEnv` but not `getEnv`
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module System.Environment.Primitive where

open import IO.Primitive using (IO)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe)
open import Data.String.Base using (String)
open import Data.Unit using (⊤)

open import Foreign.Haskell.Pair using (Pair)

{-# FOREIGN GHC import qualified System.Environment as SE #-}
{-# FOREIGN GHC import qualified Data.Text          as T  #-}
{-# FOREIGN GHC import Data.Bifunctor (bimap)             #-}
{-# FOREIGN GHC import Data.Function (on)                 #-}

postulate
  getArgs        : IO (List String)
  getProgName    : IO String
  lookupEnv      : String → IO (Maybe String)
  setEnv         : String → String → IO ⊤
  unsetEnv       : String → IO ⊤
  withArgs       : ∀ {a} {A : Set a} → List String → IO A → IO A
  withProgName   : ∀ {a} {A : Set a} → String → IO A → IO A
  getEnvironment : IO (List (Pair String String))

{-# COMPILE GHC getArgs        = fmap (fmap T.pack) SE.getArgs #-}
{-# COMPILE GHC getProgName    = fmap T.pack SE.getProgName #-}
{-# COMPILE GHC lookupEnv      = fmap (fmap T.pack) . SE.lookupEnv . T.unpack #-}
{-# COMPILE GHC setEnv         = SE.setEnv `on` T.unpack #-}
{-# COMPILE GHC unsetEnv       = SE.unsetEnv . T.unpack #-}
{-# COMPILE GHC withArgs       = \ _ _ -> SE.withArgs . fmap T.unpack #-}
{-# COMPILE GHC withProgName   = \ _ _ -> SE.withProgName . T.unpack #-}
{-# COMPILE GHC getEnvironment = fmap (fmap (bimap T.pack T.pack)) SE.getEnvironment #-}
