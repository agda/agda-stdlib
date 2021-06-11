{-# OPTIONS --guardedness --sized-types #-}

module Main where

open import Level
open import Data.List as List using (List; _∷_; []; _++_; reverse)
open import Data.List.Zipper
import Data.List.Sort as Sort
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Show using (show)
import Data.Nat.Properties as ℕₚ
open import Data.String.Base as String using (String)
import Data.Vec.Base as Vec

open import Codata.Stream using (nats; take)

open Sort ℕₚ.≤-decTotalOrder

open import IO.Base
open import IO.Finite
open import Function.Base using (_$_)

private
  variable
    a : Level
    A : Set a

data Direction : Set where Left Right : Direction

follow : List Direction → List A → Zipper A
follow dirs init = go dirs (fromList init) where

  turn : Direction → Zipper A → Zipper A
  turn Left  zip = fromMaybe zip (left zip)
  turn Right zip = fromMaybe zip (right zip)

  go : List Direction → Zipper A → Zipper A
  go []         zip = zip
  go (d ∷ dirs) zip = go dirs (turn d zip)

updateFocus : (A → A) → Zipper A → Zipper A
updateFocus f (mkZipper ctx (a ∷ val)) = mkZipper ctx (f a ∷ val)
updateFocus f zip = zip

applyAt : List Direction → (A → A) → List A → List A
applyAt dirs f xs = toList
                  $ updateFocus f
                  $ follow dirs xs

someNats : List ℕ
someNats = Vec.toList $ take 20 $ nats

otherNats : List ℕ
otherNats = applyAt (Right ∷ Right ∷ [])                   (3 +_)
          $ applyAt (List.replicate 10 Right ++ Left ∷ []) (10 +_)
          $ applyAt (List.replicate 10 Left)               (_∸ 5)
          $ applyAt (Left ∷ Right ∷ Right ∷ Left ∷ [])     (2 *_)
          $ applyAt (List.replicate 5 Right)               (_^ 2)
          $ List.reverse someNats

showNats : List ℕ → String
showNats ns = String.concat
            $ "["
            ∷ String.intersperse ", " (List.map show ns)
            ∷ "]" ∷ []

main : Main
main = run $ do
  putStrLn $ showNats someNats
  putStrLn $ showNats otherNats
  putStrLn $ showNats $ sort otherNats
