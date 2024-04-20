{-# OPTIONS --guardedness #-}

module Main where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic.Base using (⊤)
import Data.Char.Base as Char
import Data.Fin.Base as Fin
import Data.Fin.Show as Fin
import Data.Float.Base as Float
open import Data.Integer.Base using (-[1+_]; +_; -≤+)
import Data.Integer.Show as ℤ
open import Data.List.Base as List using ([]; _∷_)
import Data.List.Show as List
import Data.Nat.Base
import Data.Nat.Properties as ℕ
import Data.Nat.Show as ℕ
open import Data.String.Base as String
import Data.Vec.Show as Vec
import Data.Word.Base as Word64
open import IO.Base
open import IO.Finite
open import Function.Base using (_$_; _∘_)
open import System.Random
import Data.Vec.Bounded.Show as Vec≤

open import Relation.Binary.Construct.Closure.Reflexive

asA : String → String → IO {0ℓ} ⊤
asA ty str = putStrLn (ty ++ ": " ++ str)

main : Main
main = run $ do
  asA "Char" ∘ Char.show =<< Char.randomIO
  asA "Char" ∘ Char.show ∘ InBounds.value =<< Char.randomRIO ' ' '~' [ ℕ.≤ᵇ⇒≤ _ _ _ ]
  asA "Float" ∘ Float.show =<< Float.randomIO
  asA "Float" ∘ Float.show ∘ InBounds.value =<< Float.randomRIO 0.0 1.0 _
  asA "Integer" ∘ ℤ.show =<< ℤ.randomIO
  asA "Integer" ∘ ℤ.show ∘ InBounds.value =<< ℤ.randomRIO -[1+ 2 ] (+ 5) -≤+
  asA "Nat" ∘ ℕ.show =<< ℕ.randomIO
  asA "Nat" ∘ ℕ.show ∘ InBounds.value =<< ℕ.randomRIO 1 10 (ℕ.≤ᵇ⇒≤ _ _ _)
  asA "Word" ∘ ℕ.show ∘ Word64.toℕ =<< Word64.randomIO
  asA "Word" ∘ ℕ.show ∘ Word64.toℕ ∘ InBounds.value =<<
    Word64.randomRIO (Word64.fromℕ 10) (Word64.fromℕ 20) (ℕ.≤ᵇ⇒≤ _ _ _)
  asA "Fin 10" ∘ Fin.show =<< Fin.randomIO {n = 10}
  asA "Fin 10" ∘ Fin.show ∘ InBounds.value =<<
    Fin.randomRIO {n = 10}
      (Fin.fromℕ< {m = 3} (ℕ.≤ᵇ⇒≤ _ _ _))
      (Fin.fromℕ< {m = 8} (ℕ.≤ᵇ⇒≤ _ _ _))
      (ℕ.≤ᵇ⇒≤ _ _ _)
  asA "Vec≤ Integer 10" ∘ Vec≤.show (ℤ.show ∘ InBounds.value) =<< Vec≤.randomIO (ℤ.randomRIO -[1+ 10 ] (+ 11) -≤+) 10
  asA "Vec Float 5" ∘ Vec.show (Float.show ∘ InBounds.value) =<< Vec.randomIO (Float.randomRIO -20.0 20.0 _) 5
  asA "String≤ 20" ∘ String.show =<< RangedString≤.randomIO ' ' '~' [ ℕ.≤ᵇ⇒≤ _ _ _ ] 20
