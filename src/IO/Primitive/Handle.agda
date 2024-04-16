------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive IO handles: simple bindings to Haskell types and functions
------------------------------------------------------------------------

-- NOTE: the contents of this module should be accessed via `IO`.

{-# OPTIONS --cubical-compatible #-}

module IO.Primitive.Handle where

open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ)

data BufferMode : Set where
  noBuffering lineBuffering : BufferMode
  blockBuffering : Maybe ℕ → BufferMode
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# FOREIGN GHC
    data AgdaBufferMode
      = NoBuffering
      | LineBuffering
      | BlockBuffering (Maybe Integer)
    toBufferMode :: AgdaBufferMode -> SIO.BufferMode
    toBufferMode x = case x of
      NoBuffering       -> SIO.NoBuffering
      LineBuffering     -> SIO.LineBuffering
      BlockBuffering mi -> SIO.BlockBuffering (fromIntegral <$> mi)
    fromBufferMode :: SIO.BufferMode -> AgdaBufferMode
    fromBufferMode x = case x of
      SIO.NoBuffering       -> NoBuffering
      SIO.LineBuffering     -> LineBuffering
      SIO.BlockBuffering mi -> BlockBuffering (fromIntegral <$> mi)
#-}

{-# COMPILE GHC BufferMode = data AgdaBufferMode
                           ( NoBuffering
                           | LineBuffering
                           | BlockBuffering
                           )
#-}

open import Data.Unit.Base using (⊤)
open import IO.Primitive.Core using (IO)

postulate
  Handle : Set
  stdin stdout stderr : Handle
  hSetBuffering : Handle → BufferMode → IO ⊤
  hGetBuffering : Handle → IO BufferMode
  hFlush : Handle → IO ⊤

{-# FOREIGN GHC import System.IO #-}
{-# COMPILE GHC Handle = type Handle #-}
{-# COMPILE GHC stdin = stdin #-}
{-# COMPILE GHC stdout = stdout #-}
{-# COMPILE GHC stderr = stderr #-}
{-# COMPILE GHC hSetBuffering = \ h -> hSetBuffering h . toBufferMode #-}
{-# COMPILE GHC hGetBuffering = fmap fromBufferMode . hGetBuffering #-}
{-# COMPILE GHC hFlush = hFlush #-}
