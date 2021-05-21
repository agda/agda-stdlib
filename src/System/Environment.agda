------------------------------------------------------------------------
-- The Agda standard library
--
-- Miscellanous information about the system environment
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module System.Environment where

open import IO using (IO; lift; run; ignore)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (Maybe)
open import Data.Product using (_×_)
open import Data.String.Base using (String)
open import Data.Unit.Polymorphic using (⊤)
open import Foreign.Haskell.Coerce

import System.Environment.Primitive as Prim

getArgs : IO (List String)
getArgs = lift Prim.getArgs

getProgName : IO String
getProgName = lift Prim.getProgName

lookupEnv : String → IO (Maybe String)
lookupEnv var = lift (coerce (Prim.lookupEnv var))

setEnv : String → String → IO ⊤
setEnv var val = ignore (lift (Prim.setEnv var val))

unsetEnv : String → IO ⊤
unsetEnv var = ignore (lift (Prim.unsetEnv var))

withArgs : ∀ {a} {A : Set a} → List String → IO A → IO A
withArgs args io = lift (Prim.withArgs args (run io))

withProgName : ∀ {a} {A : Set a} → String → IO A → IO A
withProgName name io = lift (Prim.withProgName name (run io))

getEnvironment : IO (List (String × String))
getEnvironment = lift (coerce Prim.getEnvironment)
