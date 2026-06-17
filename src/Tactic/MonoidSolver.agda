------------------------------------------------------------------------
-- The Agda standard library
--
-- Reflection-based solver for monoid equalities
------------------------------------------------------------------------
--
-- This solver automates the construction of proofs of equivalences
-- between monoid expressions.
-- When called like so:
--
--   proof : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z) ∙ ε
--   proof x y z = solve mon
--
-- The following diagram describes what happens under the hood:
--
--            ┌▸x ∙ (y ∙ (z ∙ ε)) ════ x ∙ (y ∙ (z ∙ ε))◂┐
--            │         ║                      ║         │
--            │         ║                      ║         │
--          [_⇓]        ║                      ║        [_⇓]
--          ╱           ║                      ║          ╲
--         ╱            ║                      ║           ╲
-- (x ∙′ y) ∙′ z      homo                   homo    x ∙′ (y ∙′ z) ∙′ ε′
--   ▴     ╲            ║                      ║           ╱       ▴
--   │      ╲           ║                      ║          ╱        │
--   │       [_↓]       ║                      ║        [_↓]       │
--   │        │         ║                      ║         │         │
--   │        │         ║                      ║         │         │
--   │        └───▸(x ∙ y) ∙ z          x ∙ (y ∙ z) ∙ ε◂─┘         │
--   │                  │                      │                   │
--   │                  │                      │                   │
--   └────reflection────┘                      └───reflection──────┘
--
-- The actual output—the proof constructed by the solver—is represented
-- by the double-lined path (══).
--
-- We start at the bottom, with our two expressions.
-- Through reflection, we convert these two expressions to their AST
-- representations, in the Expr type.
-- We then can evaluate the AST in two ways: one simply gives us back
-- the two expressions we put in ([_↓]), and the other normalises
-- ([_⇓]).
-- We use the homo function to prove equivalence between these two
-- forms: joining up these two proofs gives us the desired overall
-- proof.

-- Note: What's going on with the Monoid parameter?
--
-- This module is not parameterised over a monoid, which is contrary
-- to what you might expect. Instead, we take the monoid record as an
-- argument to the solve macro, and then pass it around as an
-- argument wherever we need it.
--
-- We need to get the monoid record at the call site, not the import
-- site, to ensure that it's consistent with the rest of the context.
-- For instance, if we wanted to produce `x ∙ y` using the monoid record
-- as imported, we would run into problems:
-- * If we tried to just reflect on the expression itself
--   (quoteTerm (x ∙ y)) we would likely get some de Bruijn indices
--   wrong (in x and y), and ∙ might not even be in scope where the
--   user wants us to solve! If they're solving an expression like
--   x + (y + z), they can pass in the +-0-monoid, but don't have to
--   open it themselves.
-- * If instead we tried to construct a term which accesses the _∙_
--   field on the reflection of the record, we'd run into similar
--   problems again. While the record is a parameter for us, it might
--   not be for the user.
-- Basically, we need the Monoid we're looking at to be exactly the
-- same as the one the user is looking at, and in order to do that we
-- quote it at the call site.

{-# OPTIONS --without-K --safe #-}

module Tactic.MonoidSolver where

open import Algebra
open import Function.Base using (_⟨_⟩_)

open import Data.Bool.Base    as Bool    using (Bool; _∨_; if_then_else_)
open import Data.Maybe.Base   as Maybe   using (Maybe; just; nothing; maybe)
open import Data.List.Base    as List    using (List; _∷_; [])
open import Data.Nat.Base     as ℕ       using (ℕ; suc; zero)
open import Data.Product.Base as Product using (_×_; _,_)

open import Reflection.AST
open import Reflection.AST.Term
open import Reflection.AST.Argument
import Reflection.AST.Name as Name
open import Reflection.TCM
open import Reflection.TCM.Syntax

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

------------------------------------------------------------------------
-- The Expr type with homomorphism proofs
------------------------------------------------------------------------

infixl 7 _∙′_
data Expr {a} (A : Set a) : Set a where
  _∙′_  : Expr A → Expr A → Expr A
  ε′    : Expr A
  [_↑]  : A → Expr A

module _ {m₁ m₂} (monoid : Monoid m₁ m₂) where

  open Monoid monoid
  open ≈-Reasoning setoid

  -- Convert the AST to an expression (i.e. evaluate it) without
  -- normalising.
  [_↓] : Expr Carrier → Carrier
  [ x ∙′ y  ↓] = [ x ↓] ∙ [ y ↓]
  [ ε′      ↓] = ε
  [ [ x ↑]  ↓] = x

  -- Convert an AST to an expression (i.e. evaluate it) while
  -- normalising.
  --
  -- This first function actually converts an AST to the Cayley
  -- representation of the underlying monoid.
  -- This obeys the monoid laws up to beta-eta equality, which is the
  -- property which gives us the "normalising" behaviour we want.
  [_⇓]′ : Expr Carrier → Carrier → Carrier
  [ x ∙′ y  ⇓]′ z = [ x ⇓]′ ([ y ⇓]′ z)
  [ ε′      ⇓]′ y = y
  [ [ x ↑]  ⇓]′ y = x ∙ y

  [_⇓] : Expr Carrier → Carrier
  [ x ⇓] = [ x ⇓]′ ε

  homo′ : ∀ x y → [ x ⇓] ∙ y ≈ [ x ⇓]′ y
  homo′ ε′ y       = identityˡ y
  homo′ [ x ↑] y   = ∙-congʳ (identityʳ x)
  homo′ (x ∙′ y) z = begin
    [ x ∙′ y ⇓] ∙ z       ≡⟨⟩
    [ x ⇓]′ [ y ⇓] ∙ z    ≈⟨ ∙-congʳ (homo′ x [ y ⇓]) ⟨
    ([ x ⇓] ∙ [ y ⇓]) ∙ z ≈⟨ assoc [ x ⇓] [ y ⇓] z ⟩
    [ x ⇓] ∙ ([ y ⇓] ∙ z) ≈⟨ ∙-congˡ (homo′ y z) ⟩
    [ x ⇓] ∙ ([ y ⇓]′ z)  ≈⟨ homo′ x ([ y ⇓]′ z) ⟩
    [ x ⇓]′ ([ y ⇓]′ z)   ∎

  homo : ∀ x → [ x ⇓] ≈ [ x ↓]
  homo ε′       = refl
  homo [ x ↑]   = identityʳ x
  homo (x ∙′ y) = begin
    [ x ∙′ y ⇓]     ≡⟨⟩
    [ x ⇓]′ [ y ⇓]  ≈⟨ homo′ x [ y ⇓] ⟨
    [ x ⇓] ∙ [ y ⇓] ≈⟨ ∙-cong (homo x) (homo y) ⟩
    [ x ↓] ∙ [ y ↓] ∎

------------------------------------------------------------------------
-- Helpers for reflection
------------------------------------------------------------------------

getArgs : Term → Maybe (Term × Term)
getArgs (def _ xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (vArg x ∷ vArg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
getArgs _ = nothing

------------------------------------------------------------------------
-- Getting monoid names
------------------------------------------------------------------------

-- We try to be flexible here, by matching two kinds of names.
-- The first is the field accessor for the monoid record itself.
-- However, users will likely want to use the solver with
-- expressions like:
--
--   xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
--
-- So we also evaluate the field accessor to find functions like ++.

record MonoidNames : Set where
  field
    is-∙ : Name → Bool
    is-ε : Name → Bool

buildMatcher : Name → Maybe Name → Name → Bool
buildMatcher n nothing  x = n Name.≡ᵇ x
buildMatcher n (just m) x = n Name.≡ᵇ x ∨ m Name.≡ᵇ x

findMonoidNames : Term → TC MonoidNames
findMonoidNames mon = do
  ∙-altName ← normalise (def (quote Monoid._∙_) (2 ⋯⟅∷⟆ mon ⟨∷⟩ []))
  ε-altName ← normalise (def (quote Monoid.ε)   (2 ⋯⟅∷⟆ mon ⟨∷⟩ []))
  pure record
    { is-∙ = buildMatcher (quote Monoid._∙_) (getName ∙-altName)
    ; is-ε = buildMatcher (quote Monoid.ε)   (getName ε-altName)
    }

------------------------------------------------------------------------
-- Building Expr
------------------------------------------------------------------------

-- We now define a function that takes an AST representing the LHS
-- or RHS of the equation to solve and converts it into an AST
-- respresenting the corresponding Expr.

″ε″ : Term
″ε″ = quote ε′ ⟨ con ⟩ []

[_↑]′ : Term → Term
[ t ↑]′ = quote [_↑] ⟨ con ⟩ (t ⟨∷⟩ [])

module _ (names : MonoidNames) where

 open MonoidNames names

 mutual
  ″∙″ : List (Arg Term) → Term
  ″∙″ (x ⟨∷⟩ y ⟨∷⟩ []) = quote _∙′_ ⟨ con ⟩ buildExpr x ⟨∷⟩ buildExpr y ⟨∷⟩ []
  ″∙″ (x ∷ xs)         = ″∙″ xs
  ″∙″ _                = unknown

  buildExpr : Term → Term
  buildExpr t@(def n xs) =
    if is-∙ n
      then ″∙″ xs
    else if is-ε n
      then ″ε″
    else
      [ t ↑]′
  buildExpr t@(con n xs) =
    if is-∙ n
      then ″∙″ xs
    else if is-ε n
      then ″ε″
    else [ t ↑]′
  buildExpr t = quote [_↑] ⟨ con ⟩ (t ⟨∷⟩ [])

------------------------------------------------------------------------
-- Constructing the solution
------------------------------------------------------------------------

-- This function joins up the two homomorphism proofs. It constructs
-- a proof of the following form:
--
--   trans (sym (homo x)) (homo y)
--
-- where x and y are the Expr representations of each side of the
-- goal equation.

constructSoln : Term → MonoidNames → Term → Term → Term
constructSoln mon names lhs rhs =
  quote Monoid.trans ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩
    (quote Monoid.sym ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩
       (quote homo ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩ buildExpr names lhs ⟨∷⟩ []) ⟨∷⟩ [])
    ⟨∷⟩
    (quote homo ⟨ def ⟩ 2 ⋯⟅∷⟆ mon ⟨∷⟩ buildExpr names rhs ⟨∷⟩ []) ⟨∷⟩
    []

------------------------------------------------------------------------
-- Macro
------------------------------------------------------------------------

solve-macro : Term → Term → TC _
solve-macro mon hole = do
  hole′ ← inferType hole >>= normalise
  names ← findMonoidNames mon
  just (lhs , rhs) ← pure (getArgs hole′)
    where nothing → typeError (termErr hole′ ∷ [])
  let soln = constructSoln mon names lhs rhs
  unify hole soln

macro
  solve : Term → Term → TC _
  solve = solve-macro
