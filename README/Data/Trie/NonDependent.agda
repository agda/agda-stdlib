------------------------------------------------------------------------
-- The Agda standard library
--
-- Example use case for a trie: a wee generic lexer
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module README.Data.Trie.NonDependent where

------------------------------------------------------------------------
-- Introduction

-- A Trie is a tree of values indexed by words in a finite language. It
-- allows users to quickly compute the Brzozowski derivative of that
-- little mapping from words to values.

-- In the most general case, values can depend upon the list of characters
-- that constitutes the path leading to them. Here however we consider a
-- non-dependent case (cf. README.Trie.Dependent for a dependent use case).

-- We can recognize keywords by storing the list of characters they
-- correspond to as paths in a Trie and the constructor they are decoded
-- to as the tree's values.

-- E.g.
-- [     .      ] is a root
-- [  -- m -->  ] is an m-labeled edge and is followed when reading 'm'
-- [    (X)     ] is a value leaf storing constructor X

--                     --> -- m --> -- m --> -- a --> (LEMMA)
--                    /
--       -- l --> -- e --> -- t --> (LET)
--      /
--     /    -- u --> -- t --> -- u --> -- a --> -- l --> (MUTUAL)
--    /    /
--  .< -- m --> -- o --> -- d --> -- u --> -- l --> -- e --> (MODULE)
--    \
--     -- w --> -- h --> -- e --> -- r --> -- e --> (WHERE)
--                           \
--                            --> -- n --> (WHEN)


-- after reading 'w', we get the derivative:

--  . -- h --> -- e --> -- r --> -- e --> (WHERE)
--                 \
--                  --> -- n --> (WHEN)


open import Level
open import Data.Unit
open import Data.Bool
open import Data.Char          as Char
import Data.Char.Properties    as Char
open import Data.List          as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Maybe         as Maybe
open import Data.Product       as Prod
open import Data.String.Base   as String using (String)
open import Data.These         as These

open import Function using (case_of_; _$_; _∘′_; id)

open import Data.Trie Char.strictTotalOrder
open import Data.AVL.Value

------------------------------------------------------------------------
-- Generic lexer

module Lexer
  -- Our lexer is parametrised over the type of tokens
  {t} {Tok : Set t}
  -- We start with an association list between
  -- * keywords (as Strings)
  -- * keywords (as token values)
  (lex : List⁺ (String × Tok))
  -- Some characters are special: they are separators, breaking a string
  -- into a list of tokens. Some are associated to a token value
  -- (e.g. parentheses) others are not (e.g. space)
  (breaking : Char → ∃ λ b → if b then Maybe Tok else Lift _ ⊤)
  -- Finally, strings which are not decoded as keywords are coerced
  -- using a function to token values.
  (default  : String → Tok)
  where

  tokenize : String → List Tok
  tokenize = start ∘′ String.toList where

   mutual

    -- A Trie is defined for an alphabet of strictly ordered letters (here
    -- we have picked Char for letters and decided to use the strict total
    -- order induced by their injection into ℕ as witnessed by the statement
    -- open import Data.Trie Char.strictTotalOrder earlier in this file).

    -- It is parametrised by a set of Values indexed over list of letters.
    -- Because we focus on the non-dependent case, we pick the constant
    -- family of Value uniformly equal to Tok. It is trivially compatible
    -- with the notion of equality underlying the strict total order on Chars.

    Keywords : Set _
    Keywords = Trie (const _ Tok) _

    -- We build a trie from the association list so that we may easily
    -- compute the successive derivatives obtained by eating the
    -- characters one by one

    init : Keywords
    init = fromList $ List⁺.toList $ List⁺.map (Prod.map₁ String.toList) lex

    -- Kickstart the tokeniser with an empty accumulator and the initial
    -- trie.
    start : List Char → List Tok
    start = loop [] init

    -- The main loop
    loop : (acc  : List Char)  → -- chars read so far in this token
           (toks : Keywords)   → -- keyword candidates left at this point
           (input : List Char) → -- list of chars to tokenize
           List Tok
    -- Empty input: finish up, check whether we have a non-empty accumulator
    loop acc toks []         = push acc []
    -- At least one character
    loop acc toks (c ∷ cs)   = case breaking c of λ where
      -- if we are supposed to break on this character, we do
      (true , m)  → push acc $ maybe′ _∷_ id m $ start cs
      -- otherwise we see whether it leads to a recognized keyword
      (false , _) → case lookupValue (c ∷ []) toks of λ where
        -- if so we can forget about the current accumulator and
        -- restart the tokenizer on the rest of the input
        (just tok) → tok ∷ start cs
        -- otherwise we record the character we read in the accumulator,
        -- compute the derivative of the map of keyword candidates and
        -- keep going with the rest of the input
        nothing    → loop (c ∷ acc) (lookupTrie c toks) cs

    -- Grab the accumulator and, unless it is empty, push it on top of
    -- the decoded list of tokens
    push : List Char → List Tok → List Tok
    push [] ts = ts
    push cs ts = default (String.fromList (List.reverse cs)) ∷ ts


------------------------------------------------------------------------
-- Concrete instance

-- A small set of keywords for a language with expressions of the form
-- `let x = e in b`.

data TOK : Set where
  LET EQ IN : TOK
  LPAR RPAR : TOK
  ID : String → TOK

toks : List⁺ (String × TOK)
toks = ("let" , LET)
     ∷ ("="   , EQ)
     ∷ ("in"  , IN)
     ∷ []

-- Breaking characters: spaces (thrown away) and parentheses (kept)

breaking : Char → ∃ λ b → if b then Maybe TOK else Lift _ ⊤
breaking c = if isSpace c then true , nothing else parens c where

  parens : Char → _
  parens '(' = true , just LPAR
  parens ')' = true , just RPAR
  parens _   = false , _

open import Agda.Builtin.Equality
open Lexer toks breaking ID

-- A test case:

_ : tokenize "fix f x = let b = fix f in (f b) x"
  ≡ ID "fix"
  ∷ ID "f"
  ∷ ID "x"
  ∷ EQ
  ∷ LET
  ∷ ID "b"
  ∷ EQ
  ∷ ID "fix"
  ∷ ID "f"
  ∷ IN
  ∷ LPAR
  ∷ ID "f"
  ∷ ID "b"
  ∷ RPAR
  ∷ ID "x"
  ∷ []
_ = refl
