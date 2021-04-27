------------------------------------------------------------------------
-- The Agda standard library
--
-- de Bruijn-aware generic traversal of reflected terms.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Category.Applicative using (RawApplicative)

module Reflection.Traversal {F : Set → Set} (AppF : RawApplicative F) where

open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.List    using (List; []; _∷_; _++_; reverse; length)
open import Data.Product using (_×_; _,_)
open import Data.String  using (String)
open import Function     using (_∘_)
open import Reflection

open RawApplicative AppF

------------------------------------------------------------------------
-- Context representation

-- Track both number of variables and actual context, to avoid having to
-- compute the length of the context everytime it's needed.
record Cxt : Set where
  constructor _,_
  pattern
  field
    len     : ℕ
    context : List (String × Arg Term)

private
  _∷cxt_ : String × Arg Term → Cxt → Cxt
  e ∷cxt (n , Γ) = (suc n , e ∷ Γ)

  _++cxt_ : List (String × Arg Term) → Cxt → Cxt
  es ++cxt (n , Γ) = (length es + n , es ++ Γ)

------------------------------------------------------------------------
-- Actions

Action : Set → Set
Action A = Cxt → A → F A

-- A traversal gets to operate on variables, metas, and names.
record Actions : Set where
  field
    onVar  : Action ℕ
    onMeta : Action Meta
    onCon  : Action Name
    onDef  : Action Name

-- Default action: do nothing.
defaultActions : Actions
defaultActions .Actions.onVar  _ = pure
defaultActions .Actions.onMeta _ = pure
defaultActions .Actions.onCon  _ = pure
defaultActions .Actions.onDef  _ = pure

------------------------------------------------------------------------
-- Traversal functions

module _ (actions : Actions) where

  open Actions actions

  traverseTerm    : Action Term
  traverseSort    : Action Sort
  traversePattern : Action Pattern
  traverseArgs    : Action (List (Arg Term))
  traverseArg     : Action (Arg Term)
  traversePats    : Action (List (Arg Pattern))
  traverseAbs     : Arg Term → Action (Abs Term)
  traverseClauses : Action Clauses
  traverseClause  : Action Clause
  traverseTel     : Action (List (String × Arg Term))

  traverseTerm Γ (var x args)      = var       <$> onVar Γ x ⊛ traverseArgs Γ args
  traverseTerm Γ (con c args)      = con       <$> onCon Γ c ⊛ traverseArgs Γ args
  traverseTerm Γ (def f args)      = def       <$> onDef Γ f ⊛ traverseArgs Γ args
  traverseTerm Γ (pat-lam cs args) = pat-lam   <$> traverseClauses Γ cs ⊛ traverseArgs Γ args
  traverseTerm Γ (pi a b)          = pi        <$> traverseArg Γ a ⊛ traverseAbs a Γ b
  traverseTerm Γ (agda-sort s)     = agda-sort <$> traverseSort Γ s
  traverseTerm Γ (meta x args)     = meta      <$> onMeta Γ x ⊛ traverseArgs Γ args
  traverseTerm Γ t@(lit _)         = pure t
  traverseTerm Γ t@unknown         = pure t
  traverseTerm Γ (lam v t)         = lam v     <$> traverseAbs (arg (arg-info v m) unknown) Γ t
    where
    m = defaultModality

  traverseArg Γ (arg i t) = arg i <$> traverseTerm Γ t
  traverseArgs Γ []       = pure []
  traverseArgs Γ (a ∷ as) = _∷_ <$> traverseArg Γ a ⊛ traverseArgs Γ as

  traverseAbs ty Γ (abs x t) = abs x <$> traverseTerm ((x , ty) ∷cxt Γ) t

  traverseClauses Γ []       = pure []
  traverseClauses Γ (c ∷ cs) = _∷_ <$> traverseClause Γ c ⊛ traverseClauses Γ cs

  traverseClause Γ (Clause.clause tel ps t) =
      Clause.clause <$> traverseTel Γ tel
                     ⊛  traversePats Γ′ ps
                     ⊛ traverseTerm Γ′ t
    where Γ′ = reverse tel ++cxt Γ
  traverseClause Γ (Clause.absurd-clause tel ps) =
      Clause.absurd-clause <$> traverseTel Γ tel
                            ⊛  traversePats Γ′ ps
    where Γ′ = reverse tel ++cxt Γ

  traverseTel Γ [] = pure []
  traverseTel Γ ((x , ty) ∷ tel) =
    _∷_ ∘ (x ,_) <$> traverseArg Γ ty ⊛ traverseTel ((x , ty) ∷cxt Γ) tel

  traverseSort Γ (Sort.set t)       = Sort.set <$> traverseTerm Γ t
  traverseSort Γ t@(Sort.lit _)     = pure t
  traverseSort Γ (Sort.prop t)      = Sort.prop <$> traverseTerm Γ t
  traverseSort Γ t@(Sort.propLit _) = pure t
  traverseSort Γ t@(Sort.inf _)     = pure t
  traverseSort Γ t@Sort.unknown     = pure t

  traversePattern Γ (Pattern.con c ps) = Pattern.con <$> onCon Γ c ⊛ traversePats Γ ps
  traversePattern Γ (Pattern.dot t)    = Pattern.dot <$> traverseTerm Γ t
  traversePattern Γ (Pattern.var x)    = Pattern.var <$> onVar Γ x
  traversePattern Γ p@(Pattern.lit _)  = pure p
  traversePattern Γ p@(Pattern.proj _) = pure p
  traversePattern Γ (Pattern.absurd x) = Pattern.absurd <$> onVar Γ x

  traversePats Γ [] = pure []
  traversePats Γ (arg i p ∷ ps) = _∷_ ∘ arg i <$> traversePattern Γ p ⊛ traversePats Γ ps
