------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive IO: simple bindings to Haskell types and functions
-- manipulating potentially infinite objects
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module IO.Primitive.Infinite where

-- NOTE: the contents of this module should be accessed via `IO` or
-- `IO.Infinite`.

open import Codata.Musical.Costring
open import Agda.Builtin.String
open import Agda.Builtin.Unit renaming (⊤ to Unit)

------------------------------------------------------------------------
-- The IO monad

open import Agda.Builtin.IO public using (IO)

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.


postulate
  getContents : IO Costring
  readFile    : String → IO Costring
  writeFile   : String → Costring → IO Unit
  appendFile  : String → Costring → IO Unit
  putStr      : Costring → IO Unit
  putStrLn    : Costring → IO Unit

{-# FOREIGN GHC import qualified Data.Text    #-}

{-# FOREIGN GHC

  fromColist :: MAlonzo.Code.Codata.Musical.Colist.Base.AgdaColist a -> [a]
  fromColist MAlonzo.Code.Codata.Musical.Colist.Base.Nil         = []
  fromColist (MAlonzo.Code.Codata.Musical.Colist.Base.Cons x xs) =
    x : fromColist (MAlonzo.RTE.flat xs)

  toColist :: [a] -> MAlonzo.Code.Codata.Musical.Colist.Base.AgdaColist a
  toColist []       = MAlonzo.Code.Codata.Musical.Colist.Base.Nil
  toColist (x : xs) =
    MAlonzo.Code.Codata.Musical.Colist.Base.Cons x (MAlonzo.RTE.Sharp (toColist xs))
#-}

{-# COMPILE GHC getContents    = fmap toColist getContents                          #-}
{-# COMPILE GHC readFile       = fmap toColist . readFile . Data.Text.unpack        #-}
{-# COMPILE GHC writeFile      = \x -> writeFile (Data.Text.unpack x) . fromColist  #-}
{-# COMPILE GHC appendFile     = \x -> appendFile (Data.Text.unpack x) . fromColist #-}
{-# COMPILE GHC putStr         = putStr . fromColist                                #-}
{-# COMPILE GHC putStrLn       = putStrLn . fromColist                              #-}
{-# COMPILE UHC getContents    = UHC.Agda.Builtins.primGetContents     #-}
{-# COMPILE UHC readFile       = UHC.Agda.Builtins.primReadFile        #-}
{-# COMPILE UHC writeFile      = UHC.Agda.Builtins.primWriteFile       #-}
{-# COMPILE UHC appendFile     = UHC.Agda.Builtins.primAppendFile      #-}
{-# COMPILE UHC putStr         = UHC.Agda.Builtins.primPutStr          #-}
{-# COMPILE UHC putStrLn       = UHC.Agda.Builtins.primPutStrLn        #-}
