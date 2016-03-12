------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

module Data.String.Base where

open import Data.List.Base as List using (_∷_; []; List)
                           renaming (map to lmap)
open import Data.Bool.Base using (Bool)
open import Data.Char.Core using (Char)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

------------------------------------------------------------------------
-- From Agda.Builtin

open import Agda.Builtin.String public
  using ( String
        ; primStringAppend
        ; primStringToList
        ; primStringFromList
        ; primStringEquality
        ; primShowString )

------------------------------------------------------------------------
-- Operations

infixr 5 _++_

_++_ : String → String → String
_++_ = primStringAppend

toList : String → List Char
toList = primStringToList

fromList : List Char → String
fromList = primStringFromList

toList∘fromList : ∀ s → toList (fromList s) ≡ s
toList∘fromList s = trustMe

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = trustMe

unlines : List String → String
unlines []       = ""
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

show : String → String
show = primShowString

{-# IMPORT Data.Text #-}

postulate
  Int : Set
{-# COMPILED_TYPE Int Int #-}

data Pair (A B : Set) : Set where
  pair : A → B → Pair A B

{-# COMPILED_DATA Pair (,) (,) #-}

postulate
  cons         : Char → String → String 
  snoc         : String → Char → String 
  append       : String → String → String 
  head         : String → Char 
  last         : String → Char 
  tail         : String → String 
  init         : String → String 
  null         : String → Bool 
  length       : String → Int 
  map          : (Char → Char) → String → String 
  intercalate  : String → List String → String 
  intersperse  : Char → String → String 
  reverse      : String → String 
  replace      : String → String → String → String
  toCaseFold   : String → String 
  toLower      : String → String 
  toUpper      : String → String 
  toTitle      : String → String 
  justifyLeft  : Int → Char → String → String 
  justifyRight : Int → Char → String → String 
  center       : Int → Char → String → String 
  transpose    : List String → List String 
  foldl1       : (Char → Char → Char) → String → Char 
  foldr1       : (Char → Char → Char) → String → Char 
  concat       : List String → String 
  concatMap    : (Char → String) → String → String 
  any          : (Char → Bool) → String → Bool 
  all          : (Char → Bool) → String → Bool 
  maximum      : String → Char 
  minimum      : String → Char 
  scanl        : (Char → Char → Char) → Char → String → String 
  scanl1       : (Char → Char → Char) → String → String 
  scanr        : (Char → Char → Char) → Char → String → String 
  scanr1       : (Char → Char → Char) → String → String 
  replicate    : Int → String → String 
  take         : Int → String → String 
  takeEnd      : Int → String → String 
  drop         : Int → String → String 
  dropEnd      : Int → String → String 
  takeWhile    : (Char → Bool) → String → String 
  takeWhileEnd : (Char → Bool) → String → String 
  dropWhile    : (Char → Bool) → String → String 
  dropWhileEnd : (Char → Bool) → String → String 
  dropAround   : (Char → Bool) → String → String 
  stripStart   : String → String 
  stripEnd     : String → String 
  strip        : String → String 
  groupBy      : (Char → Char → Bool)→ String → List String 
  group        : String → List String 
  inits        : String → List String 
  tails        : String → List String 
  splitOn      : String → String → List String
  split        : (Char → Bool) → String → List String 
  chunksOf     : Int → String → List String 
  find         : (Char → Bool) → String → Maybe Char 
  filter       : (Char → Bool) → String → String 
  index        : String → Int → Char 
  findIndex    : (Char → Bool) → String → Maybe Int 
  count        : String → String → Int 
  zipWith      : (Char → Char → Char) → String → String → String 
  words        : String → List String 
  lines        : String → List String 
  unwords      : List String → String 
  isPrefixOf   : String → String → Bool 
  isSuffixOf   : String → String → Bool 
  isInfixOf    : String → String → Bool 
  stripPrefix  : String → String → Maybe String 
  stripSuffix  : String → String → Maybe String 

postulate
  splitAt₁     : Int → String → Pair String String 
  break₁       : (Char → Bool) → String → Pair String String 
  breakOn₁     : String → String → Pair String String 
  breakOnEnd₁  : String → String → Pair String String 
  breakOnAll₁  : String → String → List (Pair String String)
  partition₁   : (Char → Bool) → String → Pair String String 
  uncons₁      : String → Maybe (Pair String String)
  span₁        : (Char → Bool) → String → Pair String String 
  zip₁         : String → String → List (Pair String String)

splitAt : Int → String → (String × String)
splitAt i s with splitAt₁ i s
... | pair t t₁ = (t , t₁)

break : (Char → Bool) → String → (String × String)
break p s with break₁ p s
... | pair t t₁ = (t , t₁)

breakOn : String → String → (String × String)
breakOn s s₁ with breakOn₁ s s₁
... | pair t t₁ = (t , t₁)

breakOnEnd : String → String → (String × String)
breakOnEnd s s₁ with breakOnEnd₁ s s₁
... | pair t t₁ = (t , t₁)

mkProduct : Pair String String → (String × String)
mkProduct (pair a b) = (a , b)

breakOnAll : String → String → List (String × String)
breakOnAll s s₁ with breakOnAll₁ s s₁
... | l = lmap mkProduct l

partition : (Char → Bool) → String → (String × String)
partition p s with partition₁ p s
... | pair t t₁ = (t , t₁)

uncons : String → Maybe (String × String)
uncons s with uncons₁ s
... | (just (pair t t₁)) = just (t , t₁)
... | _ = nothing

span : (Char → Bool) → String → (String × String)
span p s with span₁ p s
... | pair t t₁ = (t , t₁)

zip : String → String → List (String × String)
zip s s₁ with zip₁ s s₁
... | l = lmap mkProduct l


{-# COMPILED splitAt₁ Data.Text.splitAt #-}
{-# COMPILED breakOn₁ Data.Text.breakOn #-}
{-# COMPILED breakOnEnd₁ Data.Text.breakOnEnd #-}
{-# COMPILED partition₁ Data.Text.partition #-}
{-# COMPILED uncons₁ Data.Text.uncons #-}
{-# COMPILED break₁ Data.Text.break #-}
{-# COMPILED breakOnAll₁ Data.Text.breakOnAll #-}
{-# COMPILED zip₁ Data.Text.zip #-}

{-# COMPILED cons Data.Text.cons #-}
{-# COMPILED snoc Data.Text.snoc #-}
{-# COMPILED append Data.Text.append #-}
{-# COMPILED head Data.Text.head #-}
{-# COMPILED last Data.Text.last #-}
{-# COMPILED tail Data.Text.tail #-}
{-# COMPILED init Data.Text.init #-}
{-# COMPILED null Data.Text.null #-}
{-# COMPILED length Data.Text.length #-}
{-# COMPILED map Data.Text.map #-}
{-# COMPILED intercalate Data.Text.intercalate #-}
{-# COMPILED intersperse Data.Text.intersperse #-}
{-# COMPILED reverse Data.Text.reverse #-}
{-# COMPILED replace Data.Text.replace #-}
{-# COMPILED toCaseFold Data.Text.toCaseFold #-}
{-# COMPILED toLower Data.Text.toLower #-}
{-# COMPILED toUpper Data.Text.toUpper #-}
{-# COMPILED toTitle Data.Text.toTitle #-}
{-# COMPILED justifyLeft Data.Text.justifyLeft #-}
{-# COMPILED justifyRight Data.Text.justifyRight #-}
{-# COMPILED center Data.Text.center #-}
{-# COMPILED transpose Data.Text.transpose #-}
{-# COMPILED foldl1 Data.Text.foldl1 #-}
{-# COMPILED foldr1 Data.Text.foldr1 #-}
{-# COMPILED concat Data.Text.concat #-}
{-# COMPILED concatMap Data.Text.concatMap #-}
{-# COMPILED any Data.Text.any #-}
{-# COMPILED all Data.Text.all #-}
{-# COMPILED maximum Data.Text.maximum #-}
{-# COMPILED minimum Data.Text.minimum #-}
{-# COMPILED scanl Data.Text.scanl #-}
{-# COMPILED scanl1 Data.Text.scanl1 #-}
{-# COMPILED scanr Data.Text.scanr #-}
{-# COMPILED scanr1 Data.Text.scanr1 #-}
{-# COMPILED replicate Data.Text.replicate #-}
{-# COMPILED take Data.Text.take #-}
{-# COMPILED takeEnd Data.Text.takeEnd #-}
{-# COMPILED drop Data.Text.drop #-}
{-# COMPILED dropEnd Data.Text.dropEnd #-}
{-# COMPILED takeWhile Data.Text.takeWhile #-}
{-# COMPILED takeWhileEnd Data.Text.takeWhileEnd #-}
{-# COMPILED dropWhile Data.Text.dropWhile #-}
{-# COMPILED dropWhileEnd Data.Text.dropWhileEnd #-}
{-# COMPILED dropAround Data.Text.dropAround #-}
{-# COMPILED stripStart Data.Text.stripStart #-}
{-# COMPILED stripEnd Data.Text.stripEnd #-}
{-# COMPILED strip Data.Text.strip #-}
{-# COMPILED groupBy Data.Text.groupBy #-}
{-# COMPILED group Data.Text.group #-}
{-# COMPILED inits Data.Text.inits #-}
{-# COMPILED tails Data.Text.tails #-}
{-# COMPILED splitOn Data.Text.splitOn #-}
{-# COMPILED split Data.Text.split #-}
{-# COMPILED chunksOf Data.Text.chunksOf #-}
{-# COMPILED find Data.Text.find #-}
{-# COMPILED filter Data.Text.filter #-}
{-# COMPILED index Data.Text.index #-}
{-# COMPILED findIndex Data.Text.findIndex #-}
{-# COMPILED count Data.Text.count #-}
{-# COMPILED zipWith Data.Text.zipWith #-}
{-# COMPILED words Data.Text.words #-}
{-# COMPILED lines Data.Text.lines #-}
{-# COMPILED unwords Data.Text.unwords #-}
{-# COMPILED isPrefixOf Data.Text.isPrefixOf #-}
{-# COMPILED isSuffixOf Data.Text.isSuffixOf #-}
{-# COMPILED isInfixOf Data.Text.isInfixOf #-}
{-# COMPILED stripPrefix Data.Text.stripPrefix #-}
{-# COMPILED stripSuffix Data.Text.stripSuffix #-}
