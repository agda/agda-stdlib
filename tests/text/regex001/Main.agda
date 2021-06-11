{-# OPTIONS --guardedness #-}

module Main where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (_∷_; [])
open import Data.List.Relation.Binary.Infix.Heterogeneous using (toView; MkView)
open import Data.String using (String; toList; fromList; lines; concat)
open import IO
open import Function.Base using (_$_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary
open import Text.Regex.String

show : ∀ e {xs} → Dec (Match (Span e _≡_) xs (Regex.expression e)) → String
show _ (no _) = "No match found"
show e (yes match) = case toView (toInfix e (match .Match.related)) of λ where
  (MkView pref x suff) → concat
    $ "Match found: "
    ∷ fromList pref
    ∷ "["
    ∷ fromList (match .Match.list)
    ∷ "]"
    ∷ fromList suff
    ∷ []

agdaFile : Regex
agdaFile .Regex.fromStart  = false
agdaFile .Regex.tillEnd    = false
agdaFile .Regex.expression
  = [ 'a' ─ 'z' ∷ 'A' ─ 'Z' ∷ [] ] +
  ∙ singleton '.'
  ∙ singleton 'a'
  ∙ singleton 'g'
  ∙ singleton 'd'
  ∙ singleton 'a'

main : Main
main = run $ do
  text ← readFiniteFile "run"
  List.forM′ (lines text) $ λ l →
    putStrLn (show agdaFile $ search (toList l) agdaFile)
