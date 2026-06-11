{-# OPTIONS --guardedness #-}

module Main where

open import Level using (0ℓ)

open import Data.Bool.Base using (Bool)
open import Data.String.Base
open import Data.Unit.Polymorphic.Base using (⊤)
open import Data.Vec.Bounded using (Vec≤)
open import Function.Base using (_$_; _∘_)

import Data.Bool.Show as Bool
import Data.Vec.Bounded.Show as Vec≤

open import Effect.Monad
open import Effect.Monad.IO
open import Effect.Monad.Random

open import IO
open import IO.Instances

open import Effect.Monad.Random.Instances
open import Effect.Monad.IO.Instances

open RawMonadIO {{...}}
open RawMonadRandom {{...}}
open RawMonadRandomR {{...}} using (getRandomR)

asA : String → String → IO {0ℓ} ⊤
asA ty val = putStrLn (ty ++ ": " ++ val)

main : Main
main = run $ do
  asA "Bool" ∘ Bool.show =<< getRandom {A = Bool}
  asA "Vec≤ Bool 10" ∘ Vec≤.show Bool.show =<< getRandom {A = Vec≤ Bool 10}
  putStrLn "Success!"
