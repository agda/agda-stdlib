------------------------------------------------------------------------
-- The Agda standard library
--
-- Macros for making working with cong more convenient
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level renaming (suc to lsuc; _⊔_ to lmax)
open import Relation.Binary.Definitions
open import Tactic.Cong.Id
open import Data.Nat renaming (_≟_ to _≟ℕ_)

module Tactic.Cong
  (recursion-limit : ℕ)
  (_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ)
  (cong : {aℓ bℓ : Level}
          {A : Set aℓ}
          {B : Set bℓ}
          (f : A → B)
          {x y : A}
          (p : x ≡ y)
          → f x ≡ f y)
  (trans : ∀ {ℓ} {A : Set ℓ} → Transitive {A = A} _≡_)
  where

open import Reflection.Term hiding (_≟_)
open import Reflection.Abstraction
open import Reflection.Argument renaming (map to arg-map)
open import Reflection.Apply recursion-limit
open import Reflection.Name using () renaming (_≟_ to _≟ⁿ_)
open import Reflection.Pattern hiding (_≟_)
open import Data.Unit
open import Data.List
open import Function.Base
open import Relation.Nullary
open import Data.Bool
open import Data.Product
open import Data.Maybe hiding (_>>=_)

infixr 2 _≡⌊_⌋_

private
  extract-f : Term → Term × Bool
  extract-f term = let (term , state) = ex 0 term false in (vLam "hole" term , state )
    where
      open import Category.Monad.State
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
                                                   put true
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

open import Reflection hiding (map-Args ; _≟_)

data RelSide : Set 0ℓ where
  lhs : RelSide
  rhs : RelSide

private
  Sort→Level : Sort → TC Level
  Sort→Level unknown = typeError (strErr "Tactic.Cong: Could not determine sort of return type" ∷ [])
  Sort→Level (set ℓ) = unquoteTC ℓ
  Sort→Level (lit n) = return (for-n n)
    where
      for-n : ℕ → Level
      for-n ℕ.zero = 0ℓ
      for-n (suc n) = lsuc (for-n n)

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

  ⌊⌋' : ∀ {ℓ} {A : Set ℓ} {x y : A} → RelSide → x ≡ y → Term → TC ⊤
  ⌊⌋' {ℓ = aℓ} {A = A} {x = x} {y = y} rel-side x≡y hole = do
    hole-T ← inferType hole
    agda-sort hole-sort ← withNormalisation true $ inferType hole-T
      where other → typeError $ strErr "Tactic.Cong: expected a sort, got" ∷ termErr other ∷ []
    bℓ ← Sort→Level hole-sort
    just (fx ∷ fy ∷ _) ← return $ term-vis-args hole-T
      where _ → typeError $ strErr "Tactic.Cong: unexpected form for relation in" ∷ termErr hole-T ∷ []
    cong ← quoteTC {A = congT aℓ bℓ} cong
    Set-bℓ ← quoteTC (Set bℓ)
    A→ ← quoteTC (λ (B : Set bℓ) → (A → B))
    A ← quoteTC A
    B ← checkType unknown Set-bℓ
    A→B ← ⦇ A→ (vArg B) ⦈
    let chosen-side = case rel-side of λ { lhs → fx ; rhs → fy }
    f , true ← return $ extract-f $ chosen-side
      where _ , false → typeError $ strErr "Tactic.Cong: could not find ⌊_⌋ in" ∷ termErr chosen-side ∷ []
    f ← checkType f A→B
    x ← quoteTC x
    y ← quoteTC y
    x≡y ← quoteTC x≡y
    out ← ⦇ cong (hArg A) (hArg B) (vArg f) (hArg x) (hArg y) (vArg x≡y) ⦈
    unify hole out
    where
      congT : ∀ aℓ bℓ → Set (lsuc (lmax aℓ bℓ))
      congT aℓ bℓ =
        {A : Set aℓ}
        {B : Set bℓ}
        (f : A → B)
        {x y : A}
        (p : x ≡ y)
        → f x ≡ f y

macro
  {- call cong, inferring the function argument from the use of ⌊_⌋. The side of
     the relation inspected is determined by the RelSide parameter
  -}
  ⌊⌋ : ∀ {ℓ} {A : Set ℓ} {x y : A} → RelSide → x ≡ y → Term → TC ⊤
  ⌊⌋ side = ⌊⌋' side

  {- Convenience macro equivalent to using ⌊⌋ within _≡⟨_⟩_ -}
  _≡⌊_⌋_ : ∀ {ℓ} {A : Set ℓ} → Term → {x y : A} → x ≡ y → Term → Term → TC ⊤
  _≡⌊_⌋_ start x≡y end hole = do
    start-T ← inferType start
    agda-sort start-sort ← withNormalisation true $ inferType start-T
      where other → typeError (strErr "Tactic.Cong: expected a sort, got " ∷ termErr other ∷ [])
    bℓ ← Sort→Level start-sort
    trans ← quoteTC {A = {B : Set bℓ} → Transitive {A = B} _≡_} trans
    subhole ← checkType unknown unknown
    out ← ⦇ trans (hArg unknown) (hArg start) (hArg unknown) (hArg unknown) (vArg subhole) (vArg end) ⦈
    unify hole out
    ⌊⌋' lhs x≡y subhole
