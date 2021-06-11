-- This is taken from README.Text.Tabular

{-# OPTIONS --guardedness #-}

module Main where

open import Function.Base

open import Data.List.Base
open import Data.String.Base
open import Data.Vec.Base

open import IO.Base
open import IO.Finite

open import Text.Tabular.Base
import Text.Tabular.List as Tabularˡ
import Text.Tabular.Vec  as Tabularᵛ

main : Main
main = run $ do
  putStrLn $
    unlines (Tabularᵛ.display unicode
            (Right ∷ Left ∷ Center ∷ [])
          ( ("foo" ∷ "bar" ∷ "baz" ∷ [])
          ∷ ("1"   ∷ "2"   ∷ "3" ∷ [])
          ∷ ("6"   ∷ "5"   ∷ "4" ∷ [])
          ∷ []))

  let foobar = ("foo" ∷ "bar" ∷ [])
             ∷ ("1"   ∷ "2"   ∷ [])
             ∷ ("4"   ∷ "3"   ∷ [])
             ∷ []

  putStrLn $
    unlines (Tabularᵛ.display unicode
            (Right ∷ Left ∷ [])
            foobar)

  putStrLn $
    unlines (Tabularᵛ.display ascii
            (Right ∷ Left ∷ [])
            foobar)

  putStrLn $
    unlines (Tabularᵛ.display whitespace
            (Right ∷ Left ∷ [])
            foobar)

  putStrLn $
    unlines (Tabularᵛ.display (compact unicode)
            (Right ∷ Left ∷ [])
            foobar)

  putStrLn $
    unlines (Tabularᵛ.display (noBorder unicode)
            (Right ∷ Left ∷ [])
            foobar)

  putStrLn $
    unlines (Tabularᵛ.display (addSpace unicode)
            (Right ∷ Left ∷ [])
            foobar)

  putStrLn $
    unlines (Tabularᵛ.display (compact (addSpace unicode))
            (Right ∷ Left ∷ [])
            foobar)

  putStrLn $
    unlines (Tabularˡ.display unicode
            (Center ∷ Right ∷ [])
            ( ("foo" ∷ "bar" ∷ [])
            ∷ ("partial" ∷ "rows" ∷ "are" ∷ "ok" ∷ [])
            ∷ ("3" ∷ "2" ∷ "1" ∷ "..." ∷ "surprise!" ∷ [])
            ∷ []))

  putStrLn $
    unlines (unsafeDisplay (compact unicode)
          ( ("foo" ∷ "bar" ∷ [])
          ∷ ("  1" ∷ "  2" ∷ [])
          ∷ ("  4" ∷ "  3" ∷ [])
          ∷ []))
