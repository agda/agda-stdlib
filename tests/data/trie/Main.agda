-- Taken from README.Data.Trie.NonDependent

{-# OPTIONS --guardedness --sized-types #-}

module Main where

open import Level
open import Data.Unit
open import Data.Bool
open import Data.Char         as Char hiding (show)
import Data.Char.Properties   as Char
open import Data.List.Base    as List using (List; []; _∷_)
open import Data.List.Fresh   as List# using (List#; []; _∷#_)
open import Data.Maybe        as Maybe
open import Data.Product      as Prod
open import Data.String       as String using (String; unlines; _++_)
open import Data.These        as These

open import Function.Base using (case_of_; _$_; _∘′_; id; _on_)
open import Relation.Nary
open import Relation.Binary using (Rel)
open import Relation.Nullary.Decidable using (¬?)

open import Data.Trie Char.<-strictTotalOrder
open import Data.Tree.AVL.Value

open import IO.Base
open import IO.Finite

record Lexer t : Set (suc t) where
  field
    Tok : Set t

  Keyword : Set t
  Keyword = String × Tok

  Distinct : Rel Keyword 0ℓ
  Distinct a b = ⌊ ¬? ((proj₁ a) String.≟ (proj₁ b)) ⌋

  field
    keywords : List# Keyword Distinct
    breaking : Char → ∃ λ b → if b then Maybe Tok else Lift _ ⊤
    default  : String → Tok


module _ {t} (L : Lexer t) where
  open Lexer L

  tokenize : String → List Tok
  tokenize = start ∘′ String.toList where

   mutual

    Keywords : Set _
    Keywords = Trie (const _ Tok) _

    init : Keywords
    init = fromList $ List.map (Prod.map₁ String.toList) $ proj₁ $ List#.toList keywords

    start : List Char → List Tok
    start = loop [] init

    loop : (acc  : List Char)  → -- chars read so far in this token
           (toks : Keywords)   → -- keyword candidates left at this point
           (input : List Char) → -- list of chars to tokenize
           List Tok
    loop acc toks []         = push acc []
    loop acc toks (c ∷ cs)   = case breaking c of λ where
      (true , m)  → push acc $ maybe′ _∷_ id m $ start cs
      (false , _) → case lookupValue toks (c ∷ []) of λ where
        (just tok) → tok ∷ start cs
        nothing    → loop (c ∷ acc) (lookupTrie toks c) cs

    push : List Char → List Tok → List Tok
    push [] ts = ts
    push cs ts = default (String.fromList (List.reverse cs)) ∷ ts

module LetIn where

  data TOK : Set where
    LET EQ IN : TOK
    LPAR RPAR : TOK
    ID : String → TOK

  show : TOK → String
  show LET    = "LET"
  show EQ     = "EQ"
  show IN     = "IN"
  show LPAR   = "LPAR"
  show RPAR   = "RPAR"
  show (ID x) = "ID \"" ++ x ++ "\""

  keywords : List# (String × TOK) (λ a b → ⌊ ¬? ((proj₁ a) String.≟ (proj₁ b)) ⌋)
  keywords =  ("let" , LET)
           ∷# ("="   , EQ)
           ∷# ("in"  , IN)
           ∷# []

  breaking : Char → ∃ (λ b → if b then Maybe TOK else Lift 0ℓ ⊤)
  breaking c = if isSpace c then true , nothing else parens c where

    parens : Char → _
    parens '(' = true , just LPAR
    parens ')' = true , just RPAR
    parens _   = false , _

  default : String → TOK
  default = ID

letIn : Lexer 0ℓ
letIn = record { LetIn }

main : Main
main = run $ do
  let open LetIn
  putStrLn $ unlines $ List.map show $
    tokenize letIn "fix f x = let b = fix f in (f b) x"
