{-# OPTIONS --guardedness --rewriting #-}

module Main where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using (show)
open import Data.Product using (_,_)
open import Data.String.Base using (String; _++_)

open import Data.Default
open import Debug.Trace using (trace)

open import IO.Base using (Main; run)
open import IO.Finite using (putStrLn)
open import Function.Base using (_$_)

open import Effect.Monad
open import Effect.Monad.State
open import Effect.Monad.State.Instances
open import Effect.Monad.Identity.Instances
open import IO.Instances

open RawMonad {{...}}
open RawMonadState {{...}}

record Fib : Set where
  field tracing : Bool
        index   : ℕ
        current : ℕ
        next    : ℕ
open Fib

initFib : Bool → Fib
initFib b = record
  { tracing = b
  ; index = 0
  ; current = 0
  ; next = 1
  }

displayFib : ℕ → ℕ → String
displayFib idx fibn = "fib " ++ show idx ++ " = " ++ show fibn

fibM : ℕ → State Fib ℕ
fibM 0 = gets current
fibM (suc n) = do
  b ← gets tracing
  when b $ do
    idx ← gets index
    fibn ← gets current
    trace (displayFib idx fibn) (pure _)
  modify (λ r → record r { index = suc (index r) ; current = next r ; next = next r + current r })
  fibM n

fib : ℕ → Bool → ℕ
fib n b = evalState (fibM n) (initFib b)

fibStr : ℕ → {{WithDefault false}} → String
fibStr n {{b}} = displayFib n (fib n (value b))

main : Main
main = run $ do
  putStrLn $ fibStr 0
  putStrLn $ fibStr 1
  putStrLn $ fibStr 2
  putStrLn $ fibStr 3
  putStrLn $ fibStr 5
  putStrLn $ fibStr 6
  putStrLn $ fibStr 7
  putStrLn $ fibStr 8
  putStrLn $ fibStr 9
  putStrLn $ fibStr 10
