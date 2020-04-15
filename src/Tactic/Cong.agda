------------------------------------------------------------------------
-- The Agda standard library
--
-- Macros for making working with cong more convenient
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

import Category.Monad.State
open import Data.Nat renaming (_≟_ to _≟ℕ_) hiding (_⊔_)
open import Data.Product
open import Level renaming (suc to lsuc)
open import Level.Literals
open import Relation.Binary.Definitions
open import Tactic.Cong.Common

module Tactic.Cong
  (recursion-limit : ℕ)
  (_≈_ : ∀ {a} {A : Set a} → A → A → Set a)
  (cong : {a b : Level}
          {A : Set a}
          {B : Set b}
          (f : A → B)
          {x y : A}
          (p : x ≈ y)
          → (f x) ≈ (f y))
  (Param : Setω)
  (Fℓ : Param → Level)
  (F : (A : Param) → Set (Fℓ A))
  (_<_ : ∀ {A : Param} → F A → F A → Set (Fℓ A))
  (≈-<-trans : ∀ {A : Param} → Trans {A = F A} {B = F A} {C = F A} _≈_ _<_ _<_)
  where

open import Data.Bool hiding (_<_)
open import Data.List
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Data.Unit
open import Function.Base
open import Reflection hiding (map-Args ; _≟_)
open import Reflection.Abstraction
open import Reflection.Apply recursion-limit
open import Reflection.Argument renaming (map to arg-map)
open import Reflection.Name using () renaming (_≟_ to _≟ⁿ_)
open import Reflection.Pattern hiding (_≟_)
open import Reflection.Term hiding (_≟_)
open import Reflection.Show
open import Relation.Nullary
open import Tactic.Cong.Impl

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

  -- These functions are for calling blockOnMeta on any metavariables found
  -- inside a term
  -- This is useful to ensure that the term that will be searched
  -- for ⌊_⌋ is fully solved beforehand.
  block-on-metas : Term → TC ⊤
  block-on-metas-args : Args Term → TC ⊤
  block-on-metas-clauses : List Clause → TC ⊤

  block-on-metas (var _ args) = block-on-metas-args args
  block-on-metas (con _ args) = block-on-metas-args args
  block-on-metas (def _ args) = block-on-metas-args args
  block-on-metas (lam _ (abs _ t)) = block-on-metas t
  block-on-metas (pat-lam cs args) = block-on-metas-clauses cs >> block-on-metas-args args
  block-on-metas (Π[ _ ∶ arg _ A ] t) = block-on-metas A >> block-on-metas t
  block-on-metas (sort _) = return tt
  block-on-metas (lit _) = return tt
  block-on-metas (meta m args) = blockOnMeta m
  block-on-metas unknown = return tt

  block-on-metas-args [] = return tt
  block-on-metas-args (arg _ t ∷ args) = block-on-metas t >> block-on-metas-args args

  block-on-metas-clauses [] = return tt
  block-on-metas-clauses (clause _ t ∷ cs) = block-on-metas t >> block-on-metas-clauses cs 
  block-on-metas-clauses (absurd-clause _ ∷ cs) = block-on-metas-clauses cs

  {- Code common to both ⌊⌋ and _≈⌊_⌋_.
     Its main job is to call extract-f and cong and constrain the types of their results.
  -}
  common : ∀ {a} {A : Set a} {x y : A} → RelSide → x ≈ y → Term → Term → Term → TC ⊤
  common {a = a} {A = A} {x = x} {y = y} rel-side x≈y hole fx fy = do
    let chosen-side = case rel-side of λ { lhs → fx ; rhs → fy }
    f , true ← return $ extract-f $ chosen-side
      where _ , false → typeError $ strErr "Tactic.Cong: could not find ⌊_⌋ in" ∷ termErr chosen-side ∷ []
    a ← quoteTC a
    A ← quoteTC A
    x ← quoteTC x
    y ← quoteTC y
    x≈y ← quoteTC x≈y
    b ← checkType unknown unknown
    B ← checkType unknown unknown
    *→* ← quoteωTC {A = {a b : Level} (A : Set a) (B : Set b) → Set (a ⊔ b)} (λ A B → (A → B))
    A→B ← ⦇ *→* (hArg a) (hArg b) (vArg A) (vArg B) ⦈
    f ← checkType f A→B
    cong ← quoteωTC {A = congT} cong
    out ← ⦇ cong (hArg a) (hArg b) (hArg A) (hArg B) (vArg f) (hArg x) (hArg y) (vArg x≈y) ⦈
    _≈_ ← quoteωTC {A = ∀ {a} {A : Set a} → A → A → Set a} _≈_
    _≈B_ ← ⦇ _≈_ (hArg b) (hArg B) ⦈
    fx≈fy-T ← ⦇ (vArg fx) ≈B (vArg fy) ⦈
    out ← checkType out fx≈fy-T
    unify hole out
    where
    congT : Setω
    congT =
      {a b : Level}
      {A : Set a}
      {B : Set b}
      (f : A → B)
      {x y : A}
      (p : x ≈ y)
      → (f x) ≈ (f y)

infixr 2 _≈⌊_⌋_

macro
  {- call cong, inferring the function argument from the use of ⌊_⌋. The side of
     the relation inspected is determined by the RelSide parameter
  -}
  ⌊⌋ : ∀ {a} {A : Set a} {x y : A} → RelSide → x ≈ y → Term → TC ⊤
  ⌊⌋ rel-side x≈y hole = do
    hole-T ← inferType hole
    just (fy ∷ fx ∷ _) ← return $ Data.Maybe.map reverse $ term-vis-args hole-T
      where _ → typeError $ strErr "Tactic.Cong: unexpected form for relation in" ∷ termErr hole-T ∷ []
    block-on-metas $ case rel-side of λ {lhs → fx ; rhs → fy}
    common rel-side x≈y hole fx fy

  {- Equivalent to using ⌊⌋ within _≈⟨_⟩_ -}
  _≈⌊_⌋_ : ∀ {a} {A : Set a} {B : Param} {x y : A} {fy end : F B}
    → F B → x ≈ y → fy < end → Term → TC ⊤
  _≈⌊_⌋_ {B = B} {fy = fy} {end = end} fx x≈y fy<end hole = do
    B ← quoteωTC B
    fx ← quoteTC fx
    block-on-metas fx
    fy ← quoteTC fy
    end ← quoteTC end
    fy<end ← quoteTC fy<end
    F ← quoteωTC {A = (A : Param) → Set (Fℓ A)} F
    _≈_ ← quoteωTC {A = ∀ {a} {A : Set a} → A → A → Set a} _≈_
    FB ← ⦇ F (vArg B) ⦈
    _≈B_ ← ⦇ _≈_ (hArg unknown) (hArg FB) ⦈
    fx≈fy-T ← ⦇ (vArg fx) ≈B (vArg fy) ⦈
    fx≈fy ← checkType unknown fx≈fy-T
    trans ← quoteωTC {A = TransT} ≈-<-trans
    out ← ⦇ trans (hArg B) (hArg fx) (hArg fy) (hArg end) (vArg fx≈fy) (vArg fy<end) ⦈
    unify hole out
    common lhs x≈y fx≈fy fx fy
    where
    TransT : Setω
    TransT = {B : Param} → Trans {A = F B} {B = F B} {C = F B} _≈_ _<_ _<_
