------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver that uses reflection to automatically obtain and solve
-- equations over rings.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.RingSolver where

open import Algebra
open import Data.Fin.Base   as Fin   using (Fin)
open import Data.Vec.Base   as Vec   using (Vec; _∷_; [])
open import Data.List.Base  as List  using (List; _∷_; [])
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat.Base            using (ℕ; suc; zero; _<ᵇ_)
open import Data.Bool.Base           using (Bool; if_then_else_; true; false)
open import Data.Unit.Base           using (⊤)
open import Data.String.Base         using (String)
open import Data.Product             using (_,_; proj₁)
open import Function
open import Relation.Nullary.Decidable

open import Reflection
open import Reflection.Argument
open import Reflection.Term
open import Reflection.Name as Name
open import Reflection.TypeChecking.Monad.Syntax
open import Data.Nat.Reflection
open import Data.List.Reflection
import Data.Vec.Reflection as Vec

open import Tactic.RingSolver.NonReflective renaming (solve to solver)
open import Tactic.RingSolver.Core.AlmostCommutativeRing
open import Tactic.RingSolver.Core.NatSet as NatSet

open AlmostCommutativeRing

------------------------------------------------------------------------
-- Utilities

private
  infix 4 _⇓≟_
  _⇓≟_ : Maybe Name → Name → Bool
  nothing ⇓≟ _ = false
  just x  ⇓≟ y = ⌊ x Name.≟ y ⌋
  {-# INLINE _⇓≟_ #-}

  VarMap : Set
  VarMap = ℕ → Maybe Term

  getVisible : Arg Term → Maybe Term
  getVisible (arg (arg-info visible _) x) = just x
  getVisible _                            = nothing

  getVisibleArgs : ∀ n → Term → Maybe (Vec Term n)
  getVisibleArgs n (def _ xs) = Maybe.map Vec.reverse (List.foldl f c (List.mapMaybe getVisible xs) n)
    where
    f : (∀ n → Maybe (Vec Term n)) → Term → ∀ n → Maybe (Vec Term n)
    f xs x zero    = just []
    f xs x (suc n) = Maybe.map (x ∷_) (xs n)

    c : ∀ n → Maybe (Vec Term n)
    c zero     = just []
    c (suc _ ) = nothing
  getVisibleArgs _ _ = nothing

  curriedTerm : NatSet → Term
  curriedTerm = List.foldr go Vec.`[] ∘ NatSet.toList
    where
    go : ℕ → Term → Term
    go x xs = var x [] Vec.`∷ xs

------------------------------------------------------------------------
-- Reflection utilities for rings

`AlmostCommutativeRing : Term
`AlmostCommutativeRing = def (quote AlmostCommutativeRing) (2 ⋯⟨∷⟩ [])

record RingOperatorNames : Set where
  constructor +⇒_*⇒_^⇒_-⇒_
  field
    +′ *′ ^′ -′ : Maybe Name

checkIsRing : Term → TC Term
checkIsRing ring = checkType ring `AlmostCommutativeRing

module RingReflection (ring : Term) where

  -- Takes the name of a function that takes the ring as it's first
  -- explicit argument and the terms of it's arguments and inserts
  -- the required ring arguments
  --   e.g. "_+_" $ʳ xs = "_+_ {_} {_} ring xs"
  infixr 6 _$ʳ_
  _$ʳ_ : Name → Args Term → Term
  nm $ʳ args = def nm (2 ⋯⟅∷⟆ ring ⟨∷⟩ args)

  `Carrier : Term
  `Carrier = quote Carrier $ʳ []

  `refl : Term
  `refl = quote refl $ʳ (1 ⋯⟅∷⟆ [])

  `sym : Term → Term
  `sym x≈y = quote sym $ʳ (2 ⋯⟅∷⟆ x≈y ⟨∷⟩ [])

  `trans : Term → Term → Term
  `trans x≈y y≈z = quote trans $ʳ (3 ⋯⟅∷⟆ x≈y ⟨∷⟩ y≈z ⟨∷⟩ [])

  getFieldName : Name → TC (Maybe Name)
  getFieldName nm = normalise (nm $ʳ []) <&> λ where
    (def f args) → just f
    _            → nothing

  getRingOperatorNames : TC RingOperatorNames
  getRingOperatorNames = ⦇
    +⇒ getFieldName (quote _+_)
    *⇒ getFieldName (quote _*_)
    ^⇒ getFieldName (quote _^_)
    -⇒ getFieldName (quote -_)
    ⦈

------------------------------------------------------------------------
-- Reflection utilities for ring solver

module RingSolverReflection (ring : Term) (numberOfVariables : ℕ) where
  open RingReflection ring

  `numberOfVariables : Term
  `numberOfVariables = toTerm numberOfVariables

  -- This function applies the hidden arguments that the constructors
  -- that Expr needs. The first is the universe level, the second is the
  -- type it contains, and the third is the number of variables it's
  -- indexed by. All three of these could likely be inferred, but to
  -- make things easier we supply the third because we know it.
  infix -1 _$ᵉ_
  _$ᵉ_ : Name → List (Arg Term) → Term
  e $ᵉ xs = con e (1 ⋯⟅∷⟆ `Carrier ⟅∷⟆ `numberOfVariables ⟅∷⟆ xs)

  -- A constant expression.
  `Κ : Term → Term
  `Κ x = quote Κ $ᵉ (x ⟨∷⟩ [])

  `I : Term → Term
  `I x = quote Ι $ᵉ (x ⟨∷⟩ [])

  _`⊜_ : Term → Term → Term
  x `⊜ y = quote _⊜_  $ʳ (`numberOfVariables ⟅∷⟆ x ⟨∷⟩ y ⟨∷⟩ [])

  `correct : Term → Term → Term
  `correct x ρ = quote Ops.correct $ʳ (1 ⋯⟅∷⟆ x ⟨∷⟩ ρ ⟨∷⟩ [])

  `solver : Term → Term → Term
  `solver `f `eq = quote solver $ʳ (`numberOfVariables ⟨∷⟩ `f ⟨∷⟩ `eq ⟨∷⟩ [])

  -- Converts the raw terms provided by the macro into the `Expr`s
  -- used internally by the solver.
  --
  -- When trying to figure out the shape of an expression, one of
  -- the difficult tasks is recognizing where constants in the
  -- underlying ring are used. If we were only dealing with ℕ, we
  -- might look for its constructors: however, we want to deal with
  -- arbitrary types which implement AlmostCommutativeRing. If the
  -- Term type contained type information we might be able to
  -- recognize it there, but it doesn't.
  --
  -- We're in luck, though, because all other cases in the following
  -- function *are* recognizable. As a result, the "catch-all" case
  -- will just assume that it has a constant expression.
  convertTerm : RingOperatorNames → VarMap → Term → Term
  convertTerm operatorNames varMap = convert
    where
    open RingOperatorNames operatorNames

    mutual
      convert : Term → Term
      -- Recognise the ring's fields
      convert (def (quote _+_) xs) = convertOp₂ (quote _⊕_) xs
      convert (def (quote _*_) xs) = convertOp₂ (quote _⊗_) xs
      convert (def (quote  -_) xs) = convertOp₁ (quote  ⊝_) xs
      convert (def (quote _^_) xs) = convertExp xs
      -- Recognise the underlying implementation of the ring's fields
      convert (def nm          xs) =
        if +′ ⇓≟ nm then convertOp₂ (quote _⊕_) xs else
        if *′ ⇓≟ nm then convertOp₂ (quote _⊗_) xs else
        if -′ ⇓≟ nm then convertOp₁ (quote  ⊝_) xs else
        if ^′ ⇓≟ nm then convertExp xs else `Κ (def nm xs)
      -- Variables
      convert v@(var x _)          = fromMaybe (`Κ v) (varMap x)
      -- Special case to recognise "suc" for naturals
      convert (`suc x)             = quote _⊕_ $ᵉ (`Κ (toTerm 1) ⟨∷⟩ convert x ⟨∷⟩ [])
      convert t                    = `Κ t

      -- Application of a ring operator often doesn't have a type as
      -- simple as "Carrier → Carrier → Carrier": there may be hidden
      -- arguments, etc. Here, we do our best to handle those cases,
      -- by just taking the last two explicit arguments.
      convertOp₂ : Name → List (Arg Term) → Term
      convertOp₂ nm (x ⟨∷⟩ y ⟨∷⟩ []) = nm $ᵉ (convert x ⟨∷⟩ convert y ⟨∷⟩ [])
      convertOp₂ nm (x ∷ xs)         = convertOp₂ nm xs
      convertOp₂ _  _                = unknown

      convertOp₁ : Name → List (Arg Term) → Term
      convertOp₁ nm (x ⟨∷⟩ []) = nm $ᵉ (convert x ⟨∷⟩ [])
      convertOp₁ nm (x ∷ xs)   = convertOp₁ nm xs
      convertOp₁ _  _          = unknown

      convertExp : List (Arg Term) → Term
      convertExp (x ⟨∷⟩ y ⟨∷⟩ []) = quote _⊛_ $ᵉ (convert x ⟨∷⟩ y ⟨∷⟩ [])
      convertExp (x ∷ xs)         = convertExp xs
      convertExp _                = unknown

------------------------------------------------------------------------
-- Macros
------------------------------------------------------------------------
-- Quantified macro

open RingReflection
open RingSolverReflection

malformedForallTypeError : ∀ {a} {A : Set a} → Term → TC A
malformedForallTypeError found = typeError
  ( strErr "Malformed call to solve."
  ∷ strErr "Expected target type to be like: ∀ x y → x + y ≈ y + x."
  ∷ strErr "Instead: "
  ∷ termErr found
  ∷ [])

quantifiedVarMap : ℕ → VarMap
quantifiedVarMap numVars i =
  if i <ᵇ numVars
    then just (var i [])
    else nothing

constructCallToSolver : Term → RingOperatorNames → List String → Term → Term → Term
constructCallToSolver `ring opNames variables `lhs `rhs = `solver `ring numVars
  (prependVLams variables (_`⊜_ `ring numVars (conv `lhs) (conv `rhs)))
  (prependHLams variables (`refl `ring))
  where
  numVars : ℕ
  numVars = List.length variables

  conv : Term → Term
  conv = convertTerm `ring numVars opNames (quantifiedVarMap numVars)

-- This is the main macro which solves for equations in which the
-- variables are universally quantified over:
--
--   lemma : ∀ x y → x + y ≈ y + x
--   lemma = solve-∀ ring
--
-- where ring is your implementation of AlmostCommutativeRing.
-- (Find some example implementations in
-- Polynomial.Solver.Ring.AlmostCommutativeRing.Instances).
solve-∀-macro : Name → Term → TC ⊤
solve-∀-macro ring hole = do
  `ring ← checkIsRing (def ring [])
  commitTC
  operatorNames ← getRingOperatorNames `ring

  -- Obtain and sanitise the goal type
  `hole ← inferType hole >>= reduce
  let variablesAndTypes , equation = stripPis `hole
  let variables = List.map proj₁ variablesAndTypes
  just (lhs ∷ rhs ∷ []) ← pure (getVisibleArgs 2 equation)
    where nothing → malformedForallTypeError `hole

  let solverCall = constructCallToSolver `ring operatorNames variables lhs rhs
  unify hole solverCall

macro
  solve-∀ : Name → Term → TC ⊤
  solve-∀ = solve-∀-macro

------------------------------------------------------------------------
-- Unquantified macro

malformedArgumentListError : ∀ {a} {A : Set a} → Term → TC A
malformedArgumentListError found = typeError
  ( strErr "Malformed call to solve."
  ∷ strErr "First argument should be a list of free variables."
  ∷ strErr "Instead: "
  ∷ termErr found
  ∷ [])

malformedGoalError : ∀ {a} {A : Set a} → Term → TC A
malformedGoalError found = typeError
  ( strErr "Malformed call to solve."
  ∷ strErr "Goal type should be of the form: LHS ≈ RHS"
  ∷ strErr "Instead: "
  ∷ termErr found
  ∷ [])

checkIsListOfVariables : Term → Term → TC Term
checkIsListOfVariables `ring `xs = checkType `xs (`List (`Carrier `ring)) >>= normalise

-- Extracts the deBruijn indices from a list of variables
getVariableIndices : Term → Maybe NatSet
getVariableIndices = go []
  where
  go : NatSet → Term → Maybe NatSet
  go t (var i [] `∷` xs) = go (insert i t) xs
  go t `[]`              = just t
  go _ _                 = nothing

constructSolution : Term → RingOperatorNames → NatSet → Term → Term → Term
constructSolution `ring opNames variables `lhs `rhs =
  `trans `ring (`sym `ring (conv `lhs)) (conv `rhs)
  where
  numVars = List.length variables

  varMap : VarMap
  varMap i = Maybe.map (λ x → `I `ring numVars (toFinTerm x)) (lookup i variables)

  ρ : Term
  ρ = curriedTerm variables

  conv = λ t → `correct `ring numVars (convertTerm `ring numVars opNames varMap t) ρ

-- Use this macro when you want to solve something *under* a lambda. For example:
-- say you have a long proof, and you just want the solver to deal with an
-- intermediate step. Call it like so:
--
--   lemma₃ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
--   lemma₃ x y = begin
--     x + y * 1 + 3 ≈⟨ +-comm x (y * 1) ⟨ +-cong ⟩ refl ⟩
--     y * 1 + x + 3 ≈⟨ solve (x ∷ y ∷ []) Int.ring ⟩
--     3 + y + x     ≡⟨ refl ⟩
--     2 + 1 + y + x ∎
--
-- The first argument is the free variables, and the second is the
-- ring implementation (as before).
solve-macro : Term → Name → Term → TC ⊤
solve-macro variables ring hole = do
  `ring ← checkIsRing (def ring [])
  commitTC
  operatorNames ← getRingOperatorNames `ring

  -- Obtain and sanitise the list of variables
  listOfVariables′ ← checkIsListOfVariables `ring variables
  commitTC
  just variableIndices ← pure (getVariableIndices listOfVariables′)
    where nothing → malformedArgumentListError listOfVariables′

  -- Obtain and santise the goal type
  hole′ ← inferType hole >>= reduce
  just (lhs ∷ rhs ∷ []) ← pure (getVisibleArgs 2 hole′)
    where nothing → malformedGoalError hole′

  let solution = constructSolution `ring operatorNames variableIndices lhs rhs
  unify hole solution

macro
  solve : Term → Name → Term → TC ⊤
  solve = solve-macro
