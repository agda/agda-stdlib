{-# OPTIONS --guardedness #-}

module Main where

open import Agda.Builtin.FromNat

open import Data.Bytestring.Base as Bytestring
open import Data.Bytestring.Builder.Base
open import Data.List.Base using ([]; _∷_)
import Data.Nat.Literals; instance numberNat = Data.Nat.Literals.number
open import Data.Product.Base using (_×_; _,_)
open import Data.String using (String; _++_; fromVec)
open import Data.Unit.Base using (⊤; tt)
import Data.Vec.Base as Vec
open import Data.Word8.Base as Word8
import Data.Word8.Show as Word8
import Data.Word8.Literals; instance numberWord8 = Data.Word8.Literals.number
open import Data.Word64.Base as Word64 using (Word64)
import Data.Word64.Unsafe as Word64
import Data.Word64.Show as Word64
import Data.Word64.Literals; instance numberWord64 = Data.Word64.Literals.number

open import Function.Base using (_$_)

open import IO.Base
open import IO.Finite

1⋯3 : Bytestring
1⋯3 = toBytestring
    $ List.concat
    $ word8 1
    ∷ word64LE 2
    ∷ word64BE 3
    ∷ []

1,⋯,3 : Word8 × Word64 × Word64
1,⋯,3 = getWord8 1⋯3 0
      , getWord64LE 1⋯3 1
      , getWord64BE 1⋯3 9

main : Main
main = run $ do
  let separation = fromVec (Vec.replicate 72 '-')
  putStrLn (Bytestring.show 1⋯3)
  putStrLn separation
  let (one , two , three) = 1,⋯,3

  let word8test : Word8 → IO _
      word8test w = do
        putStrLn (Word8.show w ++ " = " ++ Word8.showBits w)
        putStrLn (Word8.show w ++ " = " ++ Word8.showHexa w)
        putStrLn (Word8.show w ++ " = " ++ Word8.show (Word8.fromBits (Word8.toBits w)))


  let word64test : Word64 → IO _
      word64test w = do
        putStrLn separation
        putStrLn (Word64.show w ++ " = " ++ Word64.showBits w)
        putStrLn (Word64.show w ++ " = " ++ Word64.showHexa w)
        putStrLn (Word64.show w ++ " = " ++ Word64.show (Word64.fromBits (Word64.toBits w)))

  word8test one
  word8test (Word8.fromℕ 144)
  word64test two
  word64test three
  word64test (Word64.fromℕ 2024)
