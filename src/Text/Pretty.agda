------------------------------------------------------------------------
-- The Agda standard library
--
-- Pretty Printing
-- This module is based on Jean-Philippe Bernardy's functional pearl
-- "A Pretty But Not Greedy Printer"
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

open import Data.Nat.Base using (ℕ)

module Text.Pretty (width : ℕ) where

import Level
open import Data.Char.Base using (Char)
open import Data.List.Base
  using (List; _∷_; []; [_]; uncons; _++_; map; filter)
open import Data.List.NonEmpty as List⁺ using (foldr₁)
open import Data.Maybe.Base using (maybe′)
open import Data.Product.Base using (uncurry)
open import Data.String.Base using (String; fromList; replicate)
open import Function.Base using (_∘_; _∘′_; _$_)

open import Effect.Monad using (RawMonad)
import Data.List.Effectful as Cat
open RawMonad (Cat.monad {Level.zero})

import Data.Nat.Properties as ℕₚ
open import Data.List.Extrema.Core ℕₚ.≤-totalOrder using (⊓ᴸ)

------------------------------------------------------------------------
-- Internal representation of documents and rendering function

import Text.Pretty.Core as Core

record Doc : Set where
  constructor mkDoc
  field runDoc : List Core.Block
open Doc public

render : Doc → String
render = Core.render
       ∘ maybe′ (foldr₁ (⊓ᴸ Core.Block.height) ∘′ uncurry List⁺._∷_) Core.empty
       ∘ uncons
       ∘′ runDoc

------------------------------------------------------------------------
-- Basic building blocks

fail : Doc
fail = mkDoc []

text : String → Doc
text = mkDoc ∘′ filter (Core.valid width) ∘ pure ∘ Core.text

empty : Doc
empty = text ""

char : Char → Doc
char c = text (fromList (c ∷ []))

spaces : ℕ → Doc
spaces n = text (replicate n ' ')

semi colon comma space dot : Doc
semi = char ';'; colon = char ':'
comma = char ','; space = char ' '; dot = char '.'

backslash forwardslash equal : Doc
backslash = char '\\'; forwardslash = char '/'; equal = char '='

squote dquote : Doc
squote = char '\''; dquote = char '"'

lparen rparen langle rangle : Doc
lparen = char '('; rparen = char ')'
langle = char '<'; rangle = char '>'

lbrace rbrace llbrace rrbrace : Doc
lbrace = char '{'; rbrace = char '}'
llbrace = char '⦃'; rrbrace = char '⦄'

lbracket rbracket llbracket rrbracket : Doc
lbracket = char '['; rbracket = char ']'
llbracket = char '⟦'; rrbracket = char '⟧'

------------------------------------------------------------------------
-- Combining two documents

infixr 5 _<>_
_<>_ : Doc → Doc → Doc
xs <> ys = mkDoc $
  let candidates = Core._<>_ <$> runDoc xs ⊛ runDoc ys in
  filter (Core.valid width) candidates


flush : Doc → Doc
flush = mkDoc ∘′ map Core.flush ∘′ runDoc

infixr 5 _<+>_
_<+>_ : Doc → Doc → Doc
x <+> y = x <> space <> y

infixr 5 _$$_
_$$_ : Doc → Doc → Doc
x $$ y = flush x <> y

infixr 4 _<|>_
_<|>_ : Doc → Doc → Doc
x <|> y = mkDoc (runDoc x ++ runDoc y)

------------------------------------------------------------------------
-- Combining lists of documents

foldDoc : (Doc → Doc → Doc) → List Doc → Doc
foldDoc _ []       = empty
foldDoc _ (x ∷ []) = x
foldDoc f (x ∷ xs) = f x (foldDoc f xs)

hsep vcat : List Doc → Doc
hsep = foldDoc _<+>_
vcat = foldDoc _$$_

sep : List Doc → Doc
sep [] = empty
sep xs = hsep xs <|> vcat xs

------------------------------------------------------------------------
-- Defined combinators

parens : Doc → Doc
parens d = lparen <> d <> rparen

commaSep : List Doc → Doc
commaSep = foldDoc (λ d e → d <> comma <+> e)

newline : Doc
newline = flush empty
