{-# OPTIONS --guardedness #-}

module Main where

open import Data.List.Base
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String)
open import Data.Tree.Rose using (Rose; node)

open import IO.Base
open import IO.Finite

open import Function.Base using (_$_)

open import Text.Pretty using (Doc; render)
open module Pretty {w} = Text.Pretty w hiding (Doc; render)

private
  variable
    w : ℕ

pretty : Rose (Maybe String) → Doc w
pretty = foldr $
 maybe′ (λ where
             s [] → text s
             s ds@(_ ∷ _) → parens $ text s <+> sep ds
        )
        vcat
{-
pretty (node nothing  ts) = vcat (map pretty ts)
pretty (node (just a) []) = text a
pretty (node (just a) ts) = parens $ text a <+> sep (map pretty ts)
-}
SEXP = Rose (Maybe String)

atom : String → SEXP
atom a = node (just a) []

list : List SEXP → SEXP
list = node nothing

colMode : SEXP
colMode = node (just "setq") (atom "column-number-mode" ∷ atom "t" ∷ [])

showTrailing : SEXP
showTrailing = node (just "setq-default")
             $ atom "show-trailing-whitespace" ∷ atom "t" ∷ []

deleteTrailing : SEXP
deleteTrailing =  node (just "add-hook")
               $ atom "'write-file-hooks"
               ∷ atom "'delete-trailing-whitespace"
               ∷ []

dotEmacs : SEXP
dotEmacs = node nothing
         $ colMode ∷ showTrailing ∷ deleteTrailing ∷ []

main : Main
main = run $ do
  let doc : Doc w; doc = pretty dotEmacs
  putStrLn $ render 40 doc
  putStrLn $ render 80 doc
