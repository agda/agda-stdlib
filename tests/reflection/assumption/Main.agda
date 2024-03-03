{-# OPTIONS --guardedness #-}

module Main where

open import Data.String.Base using (String)
open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base using (List; []; _∷_; concatMap; map)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_)
open import Level using (Level)
open import Data.Unit.Base using (⊤)
open import Function.Base using (case_of_; _$_)
open import Reflection.TCM hiding (pure)
open import Reflection.AST.Term
open import Reflection.AST.Literal hiding (_≟_)
open import Reflection.AST.Argument using (Arg; unArg; arg)
open import Reflection.AST.DeBruijn
open import Reflection.AST.Show
open import Relation.Nullary.Decidable using (does)

open import Effect.Monad
open RawMonad {{...}}

open import Data.Maybe.Instances
open import Reflection.TCM.Instances

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- As the doc states (cf. https://agda.readthedocs.io/en/latest/language/reflection.html#type-checking-computations)
-- Note that the types in the context are valid in the rest of the context.
-- To use in the current context they need to be weakened by 1 + their position
-- in the list.

-- That is to say that the type of the current goal needs to be strengthened
-- before being compared to the type of the most local variable. The goal
-- indeed lives below that variable's binding site!

searchEntry : ℕ → Type → List (String × Arg Type) → Maybe ℕ
searchEntry n ty [] = nothing
searchEntry n ty ((_ , e) ∷ es) = do
  ty ← strengthen ty
  if does (ty ≟ unArg e)
    then just n
    else searchEntry (suc n) ty es

macro
  assumption : Term → TC ⊤
  assumption hole = do
    asss ← getContext
    goal ← inferType hole
    debugPrint "" 10
      (strErr "Context : "
       ∷ concatMap (λ where (_ , arg info ty) → strErr "\n  " ∷ termErr ty ∷ []) asss)
    let res = searchEntry 0 goal asss
    case res of λ where
      nothing → typeError (strErr "Couldn't find an assumption of type: " ∷ termErr goal ∷ [])
      (just idx) → unify hole (var idx [])

test₀ : A → B → B
test₀ x y = assumption

test₁ : A → B → A
test₁ x y = assumption

test₂ : A → B → B → A
test₂ x y z = assumption

test₃ : List (A → B) → A → B → B → List (A → B)
test₃ x y z a = assumption

test₄ : (A → List B) → A → B → List B → A → List B
test₄ x y z a = assumption

open import IO.Base using (Main; run)
open import IO.Finite
open import IO.Instances

macro
  runTC : TC String → Term → TC ⊤
  runTC tc t = do
    u ← tc
    unify t (lit (string u))

main : Main
main = run $ do
  putStrLn $ runTC (showDefinition <$> getDefinition (quote test₀))
  putStrLn $ runTC (showDefinition <$> getDefinition (quote test₁))
  putStrLn $ runTC (showDefinition <$> getDefinition (quote test₂))
  putStrLn $ runTC (showDefinition <$> getDefinition (quote test₃))
  putStrLn $ runTC (showDefinition <$> getDefinition (quote test₄))
