------------------------------------------------------------------------
-- The Agda standard library
--
-- Macros for making working with cong more convenient
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

import Category.Monad.State
open import Data.Nat renaming (_≟_ to _≟ℕ_) hiding (_⊔_)
open import Level renaming (suc to lsuc)
open import Level.Literals
open import Relation.Binary.Definitions
open import Tactic.Cong.Id
open import Data.Product

module Tactic.Cong
  (recursion-limit : ℕ)
  (_≈_ : ∀ {a} {A : Set a} → A → A → Set a)
  (cong : ∀ {a b}
          {A : Set a}
          {B : Set b}
          (f : A → B)
          {x y : A}
          (p : x ≈ y)
          → f x ≈ f y)
  (trans : ∀{a} {A : Set a} → Transitive {A = A} _≈_)
  where

open import Data.Bool
open import Data.List
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Data.Unit
open import Function.Base
import Reflection
open import Reflection.Abstraction
open import Reflection.Apply recursion-limit
open import Reflection.Argument renaming (map to arg-map)
open import Reflection.Name using () renaming (_≟_ to _≟ⁿ_)
open import Reflection.Pattern hiding (_≟_)
open import Reflection.Term hiding (_≟_)
open import Relation.Nullary

private
  {- This function turns a term containing ⌊_⌋ into a lambda term with all
     instances of ⌊_⌋ replaced with the argument variable of the lambda.

     Returns the transformed term plus a Bool indicating whether any ⌊_⌋ were
     found. Not finding any ⌊_⌋ generally indicates that the macro has been used
     incorrectly.
  -}
  extract-f : Term → Term × Bool
  extract-f term = let (term , state) = ex 0 term false in (vLam "hole" term , state )
    where
    -- State Monad is used to track whether any ⌊_⌋ have been found
    open Category.Monad.State
    open RawMonadState (StateMonadState Bool)

    ex : ℕ → Term → State Bool Term
    ex-args : ℕ → List (Arg Term) → State Bool (List (Arg Term))
    ex-clauses : ℕ → List Clause → State Bool (List Clause)

    ex hole-i (var var-i args) with does (var-i ≥? hole-i)
    ...                           | true  = do
                                    args ← ex-args hole-i args
                                    return $ var (suc var-i) args
    ...                           | false = do
                                    args ← ex-args hole-i args
                                    return $ var var-i args
    ex hole-i (def f _   )                  with does (f ≟ⁿ quote ⌊_⌋)
    ex hole-i (def _ (_ ⟅∷⟆ _ ⟅∷⟆ _ ⟨∷⟩ args)) | true  = do
                                                 put true -- ⌊_⌋ has been found
                                                 args ← ex-args hole-i args
                                                 return $ var hole-i args
    ex hole-i (def f args)                     | _  = do
                                                 args ← ex-args hole-i args
                                                 return $ def f args
    ex hole-i (con c args) = do
      args ← ex-args hole-i args
      return $ con c args
    ex hole-i (lam v (abs s t)) = do
      t ← ex (suc hole-i) t
      return $ lam v $ abs s t
    ex hole-i (pat-lam cs args) = do
      cs ← ex-clauses hole-i cs
      args ← ex-args hole-i args
      return $ pat-lam cs args
    ex hole-i (meta x args) = do
      args ← ex-args hole-i args
      return $ meta x args
    ex hole-i (Π[ s ∶ arg v A ] t) = do
      A ← ex hole-i A
      t ← ex (suc hole-i) t
      return $ Π[ s ∶ arg v A ] t
    ex hole-i (sort s) = return $ sort s
    ex hole-i (lit l)  = return $ lit l
    ex hole-i unknown  = return unknown

    ex-args hole-i [] = return []
    ex-args hole-i (arg v t ∷ as) = do
      t ← ex hole-i t
      as ← ex-args hole-i as
      return $ arg v t ∷ as

    ex-clauses hole-i [] = return []
    ex-clauses hole-i (clause ps t ∷ cs) = do
      t ← ex (hole-i + pattern-args-size ps) t
      cs ← ex-clauses hole-i cs
      return $ clause ps t ∷ cs
    ex-clauses hole-i (absurd-clause ps ∷ cs) = do
      cs ← ex-clauses hole-i cs
      return $ absurd-clause ps ∷ cs

open Reflection hiding (map-Args ; _≟_)

data RelSide : Set 0ℓ where
  lhs : RelSide
  rhs : RelSide

private
  Sort→Level : Sort → TC Level
  Sort→Level unknown = typeError (strErr "Tactic.Cong: Could not determine sort of return type" ∷ [])
  Sort→Level (set a) = unquoteTC a
  Sort→Level (lit n) = return (# n)

  -- for idiom brackets
  pure : Term → TC Term
  pure t = return t

  -- for idiom brackets
  _<*>_ : TC Term → Arg Term → TC Term
  f <*> x = do
    f ← f
    case f ⟨ apply ⟩ x of λ {
        (err e) → typeError $ strErr "Tactic.Cong:" ∷ e ;
        (ok t) → return t
      }

  ⌊⌋' : ∀ {a} {A : Set a} {x y : A} → RelSide → x ≈ y → Term → TC ⊤
  ⌊⌋' {a = a} {A = A} {x = x} {y = y} rel-side x≈y hole = do
    hole-T ← inferType hole
    agda-sort hole-sort ← withNormalisation true $ inferType hole-T
      where other → typeError $ strErr "Tactic.Cong: expected a sort, got" ∷ termErr other ∷ []
    b ← Sort→Level hole-sort
    -- TODO: Take tail arguments of hole-T, not head
    just (fx ∷ fy ∷ _) ← return $ term-vis-args hole-T
      where _ → typeError $ strErr "Tactic.Cong: unexpected form for relation in" ∷ termErr hole-T ∷ []
    cong ← quoteTC {A = congT a b} cong
    Set-b ← quoteTC (Set b)
    A→ ← quoteTC (λ (B : Set b) → (A → B))
    A ← quoteTC A
    B ← checkType unknown Set-b
    A→B ← ⦇ A→ (vArg B) ⦈
    let chosen-side = case rel-side of λ { lhs → fx ; rhs → fy }
    f , true ← return $ extract-f $ chosen-side
      where _ , false → typeError $ strErr "Tactic.Cong: could not find ⌊_⌋ in" ∷ termErr chosen-side ∷ []
    f ← checkType f A→B
    x ← quoteTC x
    y ← quoteTC y
    x≈y ← quoteTC x≈y
    out ← ⦇ cong (hArg A) (hArg B) (vArg f) (hArg x) (hArg y) (vArg x≈y) ⦈
    unify hole out
    where
    congT : ∀ a b → Set (lsuc (a ⊔ b))
    congT a b =
      {A : Set a}
      {B : Set b}
      (f : A → B)
      {x y : A}
      (p : x ≈ y)
      → f x ≈ f y

infixr 2 _≈⌊_⌋_

macro
  {- call cong, inferring the function argument from the use of ⌊_⌋. The side of
     the relation inspected is determined by the RelSide parameter
  -}
  ⌊⌋ : ∀ {a} {A : Set a} {x y : A} → RelSide → x ≈ y → Term → TC ⊤
  ⌊⌋ side = ⌊⌋' side

  {- Convenience macro equivalent to using ⌊⌋ within _≈⟨_⟩_ -}
  _≈⌊_⌋_ : ∀ {a} {A : Set a} → Term → {x y : A} → x ≈ y → Term → Term → TC ⊤
  _≈⌊_⌋_ start x≈y end hole = do
    start-T ← inferType start
    agda-sort start-sort ← withNormalisation true $ inferType start-T
      where other → typeError (strErr "Tactic.Cong: expected a sort, got " ∷ termErr other ∷ [])
    b ← Sort→Level start-sort
    trans ← quoteTC {A = {B : Set b} → Transitive {A = B} _≈_} trans
    subhole ← checkType unknown unknown
    out ← ⦇ trans (hArg unknown) (hArg start) (hArg unknown) (hArg unknown) (vArg subhole) (vArg end) ⦈
    unify hole out
    ⌊⌋' lhs x≈y subhole
