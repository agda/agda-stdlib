------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver that uses reflection to automatically obtain and solve
-- equations over rings.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.RingSolver where

open import Agda.Builtin.Reflection

open import Algebra
open import Data.Fin   as Fin   using (Fin)
open import Data.Vec   as Vec   using (Vec; _∷_; [])
open import Data.List  as List  using (List; _∷_; [])
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat            using (ℕ; suc; zero; _<ᵇ_)
open import Data.Nat.Reflection using (toTerm; toFinTerm)
open import Data.Bool           using (Bool; if_then_else_; true; false)
open import Data.Unit           using (⊤)
open import Data.String         using (String)
open import Data.Product        using (_,_)
open import Function
open import Reflection.Argument
open import Reflection.Term
open import Reflection.TypeChecking.MonadSyntax

open import Tactic.RingSolver.NonReflective renaming (solve to solve-fn)
open import Tactic.RingSolver.Core.AlmostCommutativeRing
open import Tactic.RingSolver.Core.NatSet as NatSet
open import Tactic.RingSolver.Core.ReflectionHelp

open AlmostCommutativeRing

------------------------------------------------------------------------
-- Processing
------------------------------------------------------------------------

private
  record RingNames : Set where
    constructor +⇒_*⇒_^⇒_-⇒_
    field
      +′ *′ ^′ -′ : Maybe Name

  checkIsRing : Term → TC Term
  checkIsRing ring = checkType ring (def (quote AlmostCommutativeRing) (2 ⋯⟨∷⟩ []))

  getVariableIDs : Term → Maybe NatSet
  getVariableIDs = go []
    where
    go : NatSet → Term → Maybe NatSet
    go t (con (quote List._∷_) (_ ∷ _ ∷ var i [] ⟨∷⟩ xs ⟨∷⟩ _)) = go (insert i t) xs
    go t (con (quote List.List.[]) _)                           = just t
    go _ _                                                      = nothing

  module OverRing (ring : Term) where

    -- Takes the name of a function that takes the ring as it's first
    -- explicit argument and the terms of it's arguments and inserts
    -- the required ring arguments
    --   e.g. "_+_" $ʳ xs = "_+_ {_} {_} ring xs"
    _$ʳ_ : Name → Args Term → Term
    nm $ʳ args = def nm (2 ⋯⟅∷⟆ ring ⟨∷⟩ args)

    checkIsListOfVariables : Term → TC Term
    checkIsListOfVariables xs =
      checkType xs (def (quote List) (1 ⋯⟅∷⟆ (quote Carrier $ʳ []) ⟨∷⟩ [])) >>= normalise

    getFieldName : Name → TC (Maybe Name)
    getFieldName nm = normalise (nm $ʳ []) <&> λ where
      (def f args) → just f
      _            → nothing

    getRingOperatorNames : TC RingNames
    getRingOperatorNames = ⦇
      +⇒ getFieldName (quote _+_)
      *⇒ getFieldName (quote _*_)
      ^⇒ getFieldName (quote _^_)
      -⇒ getFieldName (quote -_)
      ⦈

    module _ (nms : RingNames) (numVars : ℕ) where
      open RingNames nms

      -- This function applies the hidden arguments that the constructors
      -- that Expr needs. The first is the universe level, the second is the
      -- type it contains, and the third is the number of variables it's
      -- indexed by. All three of these could likely be inferred, but to
      -- make things easier we supply the third because we know it.
      _$ᵉ_ : Name → List (Arg Term) → Term
      e $ᵉ xs = con e (1 ⋯⟅∷⟆ quote Carrier $ʳ [] ⟅∷⟆ toTerm numVars ⟅∷⟆ xs)

      -- A constant expression.
      Κ′ : Term → Term
      Κ′ x = quote Κ $ᵉ (x ⟨∷⟩ [])

      _⇓≟_ : Maybe Name → Name → Bool
      nothing ⇓≟ _ = false
      just x  ⇓≟ y = primQNameEquality x y
      {-# INLINE _⇓≟_ #-}

      module ToExpr (Ι′ : ℕ → Maybe Term) where
        mutual
          -- Application of a ring operator often doesn't have a type as
          -- simple as "Carrier → Carrier → Carrier": there may be hidden
          -- arguments, etc. Here, we do our best to handle those cases,
          -- by just taking the last two explicit arguments.
          E⟨_⟩₂ : Name → List (Arg Term) → Term
          E⟨ nm ⟩₂ (x ⟨∷⟩ y ⟨∷⟩ []) = nm $ᵉ (E x ⟨∷⟩ E y ⟨∷⟩ [])
          E⟨ nm ⟩₂ (x ∷ xs)         = E⟨ nm ⟩₂ xs
          E⟨ nm ⟩₂ _                = unknown

          E⟨_⟩₁ : Name → List (Arg Term) → Term
          E⟨ nm ⟩₁ (x ⟨∷⟩ []) = nm $ᵉ (E x ⟨∷⟩ [])
          E⟨ nm ⟩₁ (x ∷ xs)   = E⟨ nm ⟩₁ xs
          E⟨ _  ⟩₁ _          = unknown

          E⟨^⟩ : List (Arg Term) → Term
          E⟨^⟩ (x ⟨∷⟩ y ⟨∷⟩ []) = quote _⊛_ $ᵉ (E x ⟨∷⟩ y ⟨∷⟩ [])
          E⟨^⟩ (x ∷ xs)         = E⟨^⟩ xs
          E⟨^⟩ _                = unknown

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
          E : Term → Term
          -- Recognise the ring's fields
          E (def (quote _+_) xs) = E⟨ quote _⊕_ ⟩₂ xs
          E (def (quote _*_) xs) = E⟨ quote _⊗_ ⟩₂ xs
          E (def (quote _^_) xs) = E⟨^⟩ xs
          E (def (quote -_)  xs) = E⟨ quote ⊝_ ⟩₁ xs
          -- Recognise the underlying implementation of the ring's fields
          E (def nm          xs) = if +′ ⇓≟ nm then E⟨ quote _⊕_ ⟩₂ xs else
                                   if *′ ⇓≟ nm then E⟨ quote _⊗_ ⟩₂ xs else
                                   if ^′ ⇓≟ nm then E⟨^⟩ xs else
                                   if -′ ⇓≟ nm then E⟨ quote ⊝_ ⟩₁ xs else
                                   Κ′ (def nm xs)
          -- Variables
          E v@(var x _)          = fromMaybe (Κ′ v) (Ι′ x)
          -- Special case to recognise "suc" for naturals
          E (con (quote ℕ.suc) (x ⟨∷⟩ [])) = quote _⊕_ $ᵉ (Κ′ (toTerm 1) ⟨∷⟩ E x ⟨∷⟩ [])
          E t                    = Κ′ t

      callSolver : Vec String numVars → Term → Term → Args Type
      callSolver nms lhs rhs =
          2 ⋯⟅∷⟆ ring ⟨∷⟩ toTerm numVars ⟨∷⟩
          vlams nms (quote _⊜_  $ʳ (toTerm numVars ⟨∷⟩ E lhs ⟨∷⟩ E rhs ⟨∷⟩ [])) ⟨∷⟩
          hlams nms (quote refl $ʳ (1 ⋯⟅∷⟆ [])) ⟨∷⟩
          []
        where
        Ι′ : ℕ → Maybe Term
        Ι′ i = if i <ᵇ numVars then just (var i []) else nothing
        open ToExpr Ι′

      constructSoln : NatSet → Term → Term → Term
      constructSoln t lhs rhs =
          quote trans $ʳ (3 ⋯⟅∷⟆
            quote sym $ʳ (2 ⋯⟅∷⟆
              quote Ops.correct $ʳ (1 ⋯⟅∷⟆ E lhs ⟨∷⟩ ρ ⟨∷⟩ []) ⟨∷⟩ [])
            ⟨∷⟩
            (quote Ops.correct $ʳ (1 ⋯⟅∷⟆ E rhs ⟨∷⟩ ρ ⟨∷⟩ [])) ⟨∷⟩
            [])
        where
        Ι′ : ℕ → Maybe Term
        Ι′ i = Maybe.map (λ x → quote Ι $ᵉ (toFinTerm x ⟨∷⟩ [])) (lookup i t)

        open ToExpr Ι′
        ρ : Term
        ρ = curriedTerm t

------------------------------------------------------------------------
-- Macros
------------------------------------------------------------------------

-- This is the main macro which solves for equations in which the variables
-- are universally quantified over:
--
--   lemma : ∀ x y → x + y ≈ y + x
--   lemma = solve-∀ TypeRing
--
-- where TypRing is your implementation of AlmostCommutativeRing. (Find some
-- example implementations in Polynomial.Solver.Ring.AlmostCommutativeRing.Instances).

solve-∀-macro : Name → Term → TC ⊤
solve-∀-macro ring hole = do
  ring′ ← checkIsRing (def ring [])
  commitTC
  let open OverRing ring′
  operatorNames ← getRingOperatorNames
  hole′ ← inferType hole >>= reduce
  let variables , k , equation = underPi hole′
  just (lhs ∷ rhs ∷ []) ← pure (getArgs 2 equation)
    where nothing → typeError (strErr "Malformed call to solve." ∷
                               strErr "Expected target type to be like: ∀ x y → x + y ≈ y + x." ∷
                               strErr "Instead: " ∷
                               termErr hole′ ∷
                               [])
  unify hole (def (quote solve-fn) (callSolver operatorNames variables k lhs rhs))

macro
  solve-∀ : Name → Term → TC ⊤
  solve-∀ = solve-∀-macro

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
--
-- One thing to note here is that we need to be able to infer *both* sides of
-- the equality, which the normal equaltional reasoning combinators don't let you
-- do. You'll need the combinators defined in Relation.Binary.Reasoning.Inference.
-- These are just as powerful as the others, but have slightly better inference properties.

solve-macro : Term → Name → Term → TC ⊤
solve-macro i ring hole = do
  ring′ ← checkIsRing (def ring [])
  commitTC
  let open OverRing ring′
  operatorNames ← getRingOperatorNames
  listOfVariables′ ← checkIsListOfVariables i
  commitTC
  hole′ ← inferType hole >>= reduce
  just vars′ ← pure (getVariableIDs listOfVariables′)
    where nothing → typeError (strErr "Malformed call to solve." ∷
                               strErr "First argument should be a list of free variables." ∷
                               strErr "Instead: " ∷
                               termErr listOfVariables′ ∷
                               [])
  just (lhs ∷ rhs ∷ []) ← pure (getArgs 2 hole′)
    where nothing → typeError (strErr "Malformed call to solve." ∷
                               strErr "First argument should be a list of free variables." ∷
                               strErr "Instead: " ∷
                               termErr hole′ ∷
                               [])
  unify hole (constructSoln operatorNames (List.length vars′) vars′ lhs rhs)

macro
  solve : Term → Name → Term → TC ⊤
  solve = solve-macro
