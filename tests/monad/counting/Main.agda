{-# OPTIONS --guardedness --sized-types #-}

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

open RawMonad {{...}}
open RawMonadReader {{...}}
open RawMonadState {{...}}
open RawMonadIO {{...}}

step : ∀ {M : Set Level.zero → Set (Level.suc Level.zero)} →
  {{RawMonad M}} →
  {{RawMonadReader String 0ℓ M}} →
  {{RawMonadState ℕ M}} →
  {{RawMonadIO M}} →
  (ℕ → ℕ) →
  M _
step f = do
  modify f
  lift str ← ask
  n ← get
  let msg = str ++ show 3 -- n
  liftIO (putStrLn msg)

script : ∀ {M} →
  {{RawMonad M}} →
  {{RawMonadReader String 0ℓ M}} →
  {{RawMonadState ℕ M}} →
  {{RawMonadIO M}} →
  M _
script = do
  step suc
  local (const "Second: ") $ step (3 *_)
  local (const "Third: ") $ step (2 ^_)

liftMonadState : RawMonadState ℕ (ReaderT String _ _ (StateT ℕ IO))
liftMonadState = record
  { get = mkReaderT (λ _ → M.get)
  ; put = λ s → mkReaderT (λ _ → M.put s)
  ; modify = λ f → mkReaderT (λ _ → M.modify f)
  } where module M = RawMonadState (monadState IO.monad)

liftMonadIO : RawMonadIO (ReaderT String _ _ (StateT ℕ IO))
liftMonadIO = record
  { liftIO = λ io → mkReaderT (λ r → mkStateT (λ s → (s ,_) IO.<$> io)) }

main : Main
main = run $
  let M = ReaderT String _ _ (StateT ℕ IO) in
  let u = script {M = M}
            {{Reader.monad _ _ (State.monad IO.monad)}}
            {{monadReader _ _ (State.monad IO.monad)}}
            {{liftMonadState}}
            {{liftMonadIO}} in
  let v = runReaderT u "First :" in
  let w = evalStateT IO.functor v 0 in
  w
