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
{-# FOREIGN GHC import System.IO #-}
{-# FOREIGN GHC
    data AgdaBufferMode
      = AgdaNoBuffering
      | AgdaLineBuffering
      | AgdaBlockBuffering (Maybe Integer)
    toBufferMode :: AgdaBufferMode -> BufferMode
    toBufferMode x = case x of
      AgdaNoBuffering       -> NoBuffering
      AgdaLineBuffering     -> LineBuffering
      AgdaBlockBuffering mi -> BlockBuffering (fromIntegral <$> mi)
    fromBufferMode :: BufferMode -> AgdaBufferMode
    fromBufferMode x = case x of
      NoBuffering       -> AgdaNoBuffering
      LineBuffering     -> AgdaLineBuffering
      BlockBuffering mi -> AgdaBlockBuffering (fromIntegral <$> mi)
#-}

{-# COMPILE GHC BufferMode = data AgdaBufferMode
                           ( AgdaNoBuffering
                           | AgdaLineBuffering
                           | AgdaBlockBuffering
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
