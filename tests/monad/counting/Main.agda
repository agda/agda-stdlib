{-# OPTIONS --guardedness #-}

module Main where

open import Data.Nat.Base
open import Data.Nat.Show using (show)
open import Data.Product using (_,_)
open import Data.String.Base using (String; _++_)
open import IO.Base as IO using (IO; Main; run)
open import IO.Finite using (putStrLn)
open import IO.Effectful as IO
open import Function.Base using (_∘′_; _$_; const)

open import Level using (Lift; 0ℓ; lift; lower)

open import Effect.Monad
open import Effect.Monad.Reader.Transformer as Reader
open import Effect.Monad.State.Transformer as State
open import Effect.Monad.IO

open import IO.Instances

open import Effect.Monad.IO.Instances
open import Effect.Monad.State.Instances
open import Effect.Monad.Reader.Instances

open RawMonad {{...}}
open RawMonadReader {{...}}
open RawMonadState {{...}}
open RawMonadIO {{...}}

step : ∀ {M : Set Level.zero → Set (Level.suc Level.zero)} →
  {{RawMonad M}} →
  {{RawMonadReader String M}} →
  {{RawMonadState ℕ M}} →
  {{RawMonadIO M}} →
  (ℕ → ℕ) →
  M _
step f = do
  modify f
  str ← ask
  n ← get
  let msg = str ++ show n
  liftIO (putStrLn msg)

script : ∀ {M} →
  {{RawMonad M}} →
  {{RawMonadReader String M}} →
  {{RawMonadState ℕ M}} →
  {{RawMonadIO M}} →
  M _
script = do
  step suc
  local (const "Second: ") $ step (3 *_)
  local (const "Third: ") $ step (2 ^_)

it : ∀ {a} {A : Set a} → {{A}} → A
it {{x}} = x

main : Main
main = run $ evalStateT it (runReaderT script "First: ") 0
