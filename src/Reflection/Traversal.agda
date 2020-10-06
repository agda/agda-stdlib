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

  private
    patternTelescope : Args Pattern → List (String × Arg Term)
    patternTelescope []       = []
    patternTelescope (arg i (Pattern.var s)     ∷ ps) = (s , arg i unknown) ∷ patternTelescope ps
    patternTelescope (arg _ (Pattern.con c ps₁) ∷ ps) = patternTelescope ps₁ ++ patternTelescope ps
    patternTelescope (arg i Pattern.dot         ∷ ps) = patternTelescope ps
    patternTelescope (arg i (Pattern.lit l)     ∷ ps) = patternTelescope ps
    patternTelescope (arg i (Pattern.proj f)    ∷ ps) = patternTelescope ps
    patternTelescope (arg i Pattern.absurd      ∷ ps) = patternTelescope ps

  traverseTerm    : Action Term
  traverseSort    : Action Sort
  traverseArgs    : Action (List (Arg Term))
  traverseArg     : Action (Arg Term)
  traverseAbs     : Arg Term → Action (Abs Term)
  traverseClauses : Action Clauses
  traverseClause  : Action Clause

  traverseTerm Γ (var x args)      = var       <$> onVar Γ x ⊛ traverseArgs Γ args
  traverseTerm Γ (con c args)      = con       <$> onCon Γ c ⊛ traverseArgs Γ args
  traverseTerm Γ (def f args)      = def       <$> onDef Γ f ⊛ traverseArgs Γ args
  traverseTerm Γ (lam v t)         = lam v     <$> traverseAbs (arg (arg-info v relevant) unknown) Γ t
  traverseTerm Γ (pat-lam cs args) = pat-lam   <$> traverseClauses Γ cs ⊛ traverseArgs Γ args
  traverseTerm Γ (pi a b)          = pi        <$> traverseArg Γ a ⊛ traverseAbs a Γ b
  traverseTerm Γ (agda-sort s)     = agda-sort <$> traverseSort Γ s
  traverseTerm Γ (meta x args)     = meta      <$> onMeta Γ x ⊛ traverseArgs Γ args
  traverseTerm Γ t@(lit _)         = pure t
  traverseTerm Γ t@unknown         = pure t

  traverseArg Γ (arg i t) = arg i <$> traverseTerm Γ t
  traverseArgs Γ []       = pure []
  traverseArgs Γ (a ∷ as) = _∷_ <$> traverseArg Γ a ⊛ traverseArgs Γ as

  traverseAbs ty Γ (abs x t) = abs x <$> traverseTerm ((x , ty) ∷cxt Γ) t

  traverseClauses Γ []       = pure []
  traverseClauses Γ (c ∷ cs) = _∷_ <$> traverseClause Γ c ⊛ traverseClauses Γ cs

  traverseClause Γ (Clause.clause ps t) =
    Clause.clause ps <$> traverseTerm (patternTelescope ps ++cxt Γ) t
  traverseClause Γ c@(Clause.absurd-clause ps) = pure c

  traverseSort Γ (Sort.set t)   = Sort.set <$> traverseTerm Γ t
  traverseSort Γ t@(Sort.lit _) = pure t
  traverseSort Γ t@Sort.unknown = pure t
