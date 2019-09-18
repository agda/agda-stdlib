{-# OPTIONS --without-K --safe #-}

module Algebra.Solver.Ring.Simple.Reflection where

open import Agda.Builtin.Reflection
open import Reflection.Helpers

open import Algebra.Solver.Ring.Simple.Solver renaming (solve to solve-fn)
open AlmostCommutativeRing

open import Data.NatSet

open import Data.Fin   as Fin   using (Fin)
open import Data.Vec   as Vec   using (Vec; _∷_; [])
open import Data.List  as List  using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing; fromMaybe)
open import Agda.Builtin.Nat    using (_<_)
open import Data.Nat            using (ℕ; suc; zero)
open import Data.Bool           using (Bool; if_then_else_; true; false)
open import Data.Unit           using (⊤)
open import Data.String         using (String)
open import Data.Product        using (_,_)
open import Function

module Internal where
  _∈Ring : Term → TC Term
  ring ∈Ring = checkType ring (def (quote AlmostCommutativeRing) (unknown ⟨∷⟩ unknown ⟨∷⟩ []))

  vars : Term → Maybe NatSet
  vars = go []
    where
    go : NatSet → Term → Maybe NatSet
    go t (con (quote List._∷_) (_ ∷ _ ∷ var i [] ⟨∷⟩ xs ⟨∷⟩ _)) = go (insert i t) xs
    go t (con (quote List.List.[]) _) = just t
    go _ _ = nothing

  module OverRing (ring : Term) where
    _∈List⟨Carrier⟩ : Term → TC Term
    t ∈List⟨Carrier⟩ =
      checkType t
        (quote List ⟨ def ⟩ 1 ⋯⟅∷⟆ def (quote Carrier) (2 ⋯⟅∷⟆ ring ⟨∷⟩ []) ⟨∷⟩ []) >>= normalise

    record Ring⇓ : Set where
      constructor +⇒_*⇒_^⇒_-⇒_
      field +′ *′ ^′ -′ : Maybe Name

    ring⇓ : TC Ring⇓
    ring⇓ = ⦇ +⇒ ⟦ quote _+_ ⇓⟧ₙ *⇒ ⟦ quote _*_ ⇓⟧ₙ ^⇒ ⟦ quote _^_ ⇓⟧ₙ -⇒ ⟦ quote -_ ⇓⟧ₙ ⦈
      where
      ⟦_⇓⟧ₙ : Name → TC (Maybe Name)
      ⟦ nm ⇓⟧ₙ =
        normalise (nm ⟨ def ⟩ 2 ⋯⟅∷⟆ ring ⟨∷⟩ [])
          <&> λ where (def f args) → just f
                      _ → nothing

    module _ (nms : Ring⇓) where
      open Ring⇓ nms

      module _ (numVars : ℕ) where

        -- This function applies the hidden arguments that the constructors
        -- that Expr needs. The first is the universe level, the second is the
        -- type it contains, and the third is the number of variables it's
        -- indexed by. All three of these could likely be inferred, but to
        -- make things easier we supply the third because we know it.
        infixr 5 E⟅∷⟆_
        E⟅∷⟆_ : List (Arg Term) → List (Arg Term)
        E⟅∷⟆ xs = 1 ⋯⟅∷⟆
                  (quote Carrier ⟨ def ⟩ 2 ⋯⟅∷⟆ ring ⟨∷⟩ []) ⟅∷⟆
                  ℕ′ numVars ⟅∷⟆
                  xs

        -- A constant expression.
        Κ′ : Term → Term
        Κ′ x = quote Κ ⟨ con ⟩ E⟅∷⟆ x ⟨∷⟩ []

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
            E⟨ nm ⟩₂ (x ⟨∷⟩ y ⟨∷⟩ []) = nm ⟨ con ⟩ E⟅∷⟆ E x ⟨∷⟩ E y ⟨∷⟩ []
            E⟨ nm ⟩₂ (x ∷ xs) = E⟨ nm ⟩₂ xs
            E⟨ nm ⟩₂ _ = unknown

            E⟨_⟩₁ : Name → List (Arg Term) → Term
            E⟨ nm ⟩₁ (x ⟨∷⟩ []) = nm ⟨ con ⟩ E⟅∷⟆ E x ⟨∷⟩ []
            E⟨ nm ⟩₁ (x ∷ xs) = E⟨ nm ⟩₁ xs
            E⟨ _ ⟩₁ _ = unknown

            E⟨^⟩ : List (Arg Term) → Term
            E⟨^⟩ (x ⟨∷⟩ y ⟨∷⟩ []) = quote _⊛_ ⟨ con ⟩ E⟅∷⟆ E x ⟨∷⟩ y ⟨∷⟩ []
            E⟨^⟩ (x ∷ xs) = E⟨^⟩ xs
            E⟨^⟩ _ = unknown

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
            E (def (quote _+_) xs) = E⟨ quote _⊕_ ⟩₂ xs
            E (def (quote _*_) xs) = E⟨ quote _⊗_ ⟩₂ xs
            E (def (quote _^_) xs) = E⟨^⟩ xs
            E (def (quote -_) xs) = E⟨ quote ⊝_ ⟩₁ xs
            E (def nm xs) = if +′ ⇓≟ nm then E⟨ quote _⊕_ ⟩₂ xs else
                            if *′ ⇓≟ nm then E⟨ quote _⊗_ ⟩₂ xs else
                            if ^′ ⇓≟ nm then E⟨^⟩ xs else
                            if -′ ⇓≟ nm then E⟨ quote ⊝_ ⟩₁ xs else
                            Κ′ (def nm xs)
            E v@(var x _) = fromMaybe (Κ′ v) (Ι′ x)
            E t = Κ′ t

        callSolver : Vec String numVars → Term → Term → List (Arg Type)
        callSolver nms lhs rhs =
            2 ⋯⟅∷⟆ ring ⟨∷⟩ ℕ′ numVars ⟨∷⟩
            vlams nms (quote _⊜_ ⟨ def ⟩ 2 ⋯⟅∷⟆ ring ⟨∷⟩ ℕ′ numVars ⟨∷⟩ E lhs ⟨∷⟩ E rhs ⟨∷⟩ []) ⟨∷⟩
            hlams nms (quote refl ⟨ def ⟩ 2 ⋯⟅∷⟆ ring ⟨∷⟩ 1 ⋯⟅∷⟆ []) ⟨∷⟩
            []
          where
          Ι′ : ℕ → Maybe Term
          Ι′ i = if i < numVars then just (var i []) else nothing
          open ToExpr Ι′

        constructSoln : NatSet → Term → Term → Term
        constructSoln t lhs rhs =
            quote trans ⟨ def ⟩ 2 ⋯⟅∷⟆ ring ⟨∷⟩ 3 ⋯⟅∷⟆
              (quote sym ⟨ def ⟩ 2 ⋯⟅∷⟆ ring ⟨∷⟩ 2 ⋯⟅∷⟆
                  (quote Ops.correct ⟨ def ⟩ 2 ⋯⟅∷⟆ ring ⟨∷⟩ 1 ⋯⟅∷⟆ E lhs ⟨∷⟩ ρ ⟨∷⟩ []) ⟨∷⟩ [])
              ⟨∷⟩
              (quote Ops.correct ⟨ def ⟩ 2 ⋯⟅∷⟆ ring ⟨∷⟩ 1 ⋯⟅∷⟆ E rhs ⟨∷⟩ ρ ⟨∷⟩ []) ⟨∷⟩
              []
          where
          Ι′ : ℕ → Maybe Term
          Ι′ i = Maybe.map (λ x → quote Ι ⟨ con ⟩ E⟅∷⟆ Fin′ x ⟨∷⟩ []) (lookup i t)

          open ToExpr Ι′
          ρ : Term
          ρ = curriedTerm t
open Internal

-- This is the main macro you'll probably be using. Call it like this:
--
--   lemma : ∀ x y → x + y ≈ y + x
--   lemma = solve TypeRing
--
-- where TypRing is your implementation of AlmostCommutativeRing. (Find some
-- example implementations in Polynomial.Solver.Ring.AlmostCommutativeRing.Instances).
macro
  solve : Name → Term → TC ⊤
  solve ring hole = do
    ring′ ← def ring [] ∈Ring
    commitTC
    let open OverRing ring′
    nms ← ring⇓
    hole′ ← inferType hole >>= reduce
    let i , k , xs = underPi hole′
    just (lhs ∷ rhs ∷ []) ← pure (getArgs 2 xs)
      where nothing → typeError (strErr "Malformed call to solve." ∷
                                 strErr "Expected target type to be like: ∀ x y → x + y ≈ y + x." ∷
                                 strErr "Instead: " ∷
                                 termErr hole′ ∷
                                 [])
    unify hole (quote solve-fn ⟨ def ⟩ callSolver nms i k lhs rhs)

-- Use this macro when you want to solve something *under* a lambda. For example:
-- say you have a long proof, and you just want the solver to deal with an
-- intermediate step. Call it like so:
--
--   lemma₃ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
--   lemma₃ x y = begin
--     x + y * 1 + 3 ≈⟨ +-comm x (y * 1) ⟨ +-cong ⟩ refl ⟩
--     y * 1 + x + 3 ≈⟨ solveOver (x ∷ y ∷ []) Int.ring ⟩
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

solveOver-macro : Term → Name → Term → TC ⊤
solveOver-macro i ring hole = do
  ring′ ← def ring [] ∈Ring
  commitTC
  let open OverRing ring′
  nms ← ring⇓
  i′ ← i ∈List⟨Carrier⟩
  commitTC
  hole′ ← inferType hole >>= reduce
  just vars′ ← pure (vars i′)
    where nothing → typeError (strErr "Malformed call to solveOver." ∷
                                strErr "First argument should be a list of free variables." ∷
                                strErr "Instead: " ∷
                                termErr i′ ∷
                                [])
  just (lhs ∷ rhs ∷ []) ← pure (getArgs 2 hole′)
    where nothing → typeError (strErr "Malformed call to solveOver." ∷
                                strErr "First argument should be a list of free variables." ∷
                                strErr "Instead: " ∷
                                termErr hole′ ∷
                                [])
  unify hole (constructSoln nms (List.length vars′) vars′ lhs rhs)

macro
  solveOver : Term → Name → Term → TC ⊤
  solveOver = solveOver-macro
