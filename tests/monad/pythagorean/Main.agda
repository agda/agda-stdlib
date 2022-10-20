{-# OPTIONS --guardedness #-}

module Main where

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using (List; []; _∷_; catMaybes)
open import Data.List.Effectful.Transformer
open import Data.List.Effectful
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Effectful.Transformer
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _^_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (_++_)
open import Function.Base using (_$_)

open import Effect.Applicative
open import Effect.Monad
open import Effect.Monad.Identity

open import IO.Base using (Main; run)
open import IO.Finite using (putStrLn)

open import Data.List.Instances
open import Data.Maybe.Instances
open import Effect.Monad.Identity.Instances
open import IO.Instances

open RawMonad {{...}}
open RawApplicativeZero {{...}} using (guard)
open TraversableA {{...}}

1⋯100 : List ℕ
1⋯100 = rangeFrom 1 100 where

  rangeFrom : (start steps : ℕ) → List ℕ
  rangeFrom start zero    = []
  rangeFrom start (suc n) = start ∷ rangeFrom (suc start) n

triples : MaybeT (ListT Identity) (ℕ × ℕ × ℕ)
triples = do
  let range = mkMaybeT (mkListT (pure (pure <$> 1⋯100)))
  p ← range
  q ← range
  r ← range
  mkMaybeT (mkListT (pure (pure (guard (p ^ 2 + q ^ 2 ≡ᵇ r ^ 2)))))
  pure (p , q , r)

main : Main
main = run
     $ ignore $ forA (catMaybes $ runIdentity $ runListT $ runMaybeT triples)
     $ λ (p , q , r) → do let sqStr = λ x → show x ++ "²"
                          putStrLn (sqStr p ++ " + " ++ sqStr q ++ " = " ++ sqStr r)
