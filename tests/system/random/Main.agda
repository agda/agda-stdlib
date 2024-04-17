{-# OPTIONS --guardedness #-}

module Main where

import Data.Fin.Base as Fin
import Data.Fin.Show as Fin
import Data.Float.Base as Float
open import Data.Integer.Base using (-[1+_]; +_; -≤+)
import Data.Integer.Show as ℤ
open import Data.List.Base using ([]; _∷_)
import Data.List.Show as List
import Data.Nat.Base
import Data.Nat.Properties as ℕ
import Data.Nat.Show as ℕ
open import Data.String.Base
import Data.Vec.Show as Vec
import Data.Word.Base as Word64
open import IO.Base
open import IO.Finite
open import Function.Base using (_$_; _∘_)
open import System.Random

open import Relation.Binary.Construct.Closure.Reflexive

main : Main
main = run $ do
  putStrLn ∘ fromChar =<< Char.randomIO
  putStrLn ∘ fromChar ∘ InBounds.value =<< Char.randomRIO 'a' 'f' [ ℕ.≤ᵇ⇒≤ _ _ _ ]
  putStrLn ∘ Float.show =<< Float.randomIO
  putStrLn ∘ Float.show ∘ InBounds.value =<< Float.randomRIO 0.0 1.0 _
  putStrLn ∘ ℤ.show =<< ℤ.randomIO
  putStrLn ∘ ℤ.show ∘ InBounds.value =<< ℤ.randomRIO -[1+ 2 ] (+ 5) -≤+
  putStrLn ∘ ℕ.show ∘ Word64.toℕ =<< Word64.randomIO
  putStrLn ∘ ℕ.show ∘ Word64.toℕ ∘ InBounds.value =<<
    Word64.randomRIO (Word64.fromℕ 10) (Word64.fromℕ 20) (ℕ.≤ᵇ⇒≤ _ _ _)
  putStrLn ∘ Fin.show =<< Fin.randomIO {n = 10}
  putStrLn ∘ Fin.show ∘ InBounds.value =<<
    Fin.randomRIO {n = 10}
      (Fin.fromℕ< {m = 3} (ℕ.≤ᵇ⇒≤ _ _ _))
      (Fin.fromℕ< {m = 8} (ℕ.≤ᵇ⇒≤ _ _ _))
      (ℕ.≤ᵇ⇒≤ _ _ _)
  putStrLn ∘ List.show ℤ.show =<< List.randomIO ℤ.randomIO
  putStrLn ∘ Vec.show (Float.show ∘ InBounds.value) =<< Vec.randomIO (Float.randomRIO -20.0 20.0 _) 10
  putStrLn =<< String.randomIO
