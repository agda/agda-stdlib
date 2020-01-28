------------------------------------------------------------------------
-- The Agda standard library
--
-- Helper reflection functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.RingSolver.Core.ReflectionHelp where

open import Agda.Builtin.Reflection

open import Data.List as List using (List; []; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; suc; zero)
open import Data.Nat.GeneralisedArithmetic using (fold)
open import Data.Fin as Fin using (Fin)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.String using (String)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product
open import Function
open import Level using (Level)

open import Tactic.RingSolver.Core.NatSet as NatSet

private
  variable
    a : Level
    A : Set a

-- TO-DO - once `Reflection` is --safe after v1.3 a lot of this can be simplified

infixr 5 _⟨∷⟩_ _⟅∷⟆_
pattern _⟨∷⟩_ x xs = arg (arg-info visible relevant) x ∷ xs
pattern _⟅∷⟆_ x xs = arg (arg-info hidden  relevant) x ∷ xs

infixr 5 _⋯⟅∷⟆_
_⋯⟅∷⟆_ : ℕ → List (Arg Term) → List (Arg Term)
zero  ⋯⟅∷⟆ xs = xs
suc i ⋯⟅∷⟆ xs = unknown ⟅∷⟆ i ⋯⟅∷⟆ xs
{-# INLINE _⋯⟅∷⟆_ #-}

ℕ′ : ℕ → Term
ℕ′ zero    = con (quote zero) []
ℕ′ (suc i) = con (quote suc)  (ℕ′ i ⟨∷⟩ [])

Fin′ : ℕ → Term
Fin′ zero    = con (quote Fin.zero) (1 ⋯⟅∷⟆ [])
Fin′ (suc i) = con (quote Fin.suc)  (1 ⋯⟅∷⟆ Fin′ i ⟨∷⟩ [])

hlams : ∀ {n} → Vec String n → Term → Term
hlams vs xs = Vec.foldr (const Term) (λ v vs → lam hidden (abs v vs)) xs vs

vlams : ∀ {n} → Vec String n → Term → Term
vlams vs xs = Vec.foldr (const Term) (λ v vs → lam visible (abs v vs)) xs vs

getVisible : Arg Term → Maybe Term
getVisible (arg (arg-info visible relevant) x) = just x
getVisible _                                   = nothing

getArgs : ∀ n → Term → Maybe (Vec Term n)
getArgs n (def _ xs) = Maybe.map Vec.reverse (List.foldl f c (List.mapMaybe getVisible xs) n)
  where
  f : (∀ n → Maybe (Vec Term n)) → Term → ∀ n → Maybe (Vec Term n)
  f xs x zero    = just []
  f xs x (suc n) = Maybe.map (x ∷_) (xs n)

  c : ∀ n → Maybe (Vec Term n)
  c zero     = just []
  c (suc _ ) = nothing
getArgs _ _ = nothing

underPi : Term → ∃[ n ] (Vec String n × Term)
underPi = go (λ xs y → _ , xs , y)
  where
  go : (∀ {n} → Vec String n → Term → A) → Term → A
  go k (pi a (abs s x)) = go (k ∘ (s ∷_)) x
  go k t                = k [] t

curriedTerm : NatSet → Term
curriedTerm = List.foldr go (quote Vec.[] ⟨ con ⟩ 2 ⋯⟅∷⟆ []) ∘ NatSet.toList
  where
  go : ℕ → Term → Term
  go x xs = quote Vec._∷_ ⟨ con ⟩ 3 ⋯⟅∷⟆ var x [] ⟨∷⟩ xs ⟨∷⟩ []
