------------------------------------------------------------------------
-- The Agda standard library
--
-- Computing free variable annotations on reflected syntax.
------------------------------------------------------------------------

{-# OPTIONS --safe --with-K #-}

module Reflection.Annotated.Free where

open import Data.Bool.Base               using (if_then_else_)
open import Data.Nat.Base                using (ℕ; _∸_; compare; _<ᵇ_; less; equal; greater)
open import Data.List.Base               using (List; []; _∷_; [_]; concatMap; length)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Product                 using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base             using (String)

open import Reflection
open import Reflection.Universe
open import Reflection.Annotated

------------------------------------------------------------------------
-- Free variable sets as lists of natural numbers

FVs : Set
FVs = List ℕ -- ordered, no duplicates

private

  infixr 3 _∪_

  _∪_ : FVs → FVs → FVs
  []     ∪ ys = ys
  xs     ∪ [] = xs
  x ∷ xs ∪ y ∷ ys with compare x y | x ∷ xs ∪ ys
  ... | less    x _ | _   = x ∷ (xs ∪ y ∷ ys)
  ... | equal   x   | _   = x ∷ (xs ∪ ys)
  ... | greater y _ | rec = y ∷ rec

  insert : ℕ → FVs → FVs
  insert x []       = x ∷ []
  insert x (y ∷ xs) with compare x y
  ... | less    x k = x ∷ y ∷ xs
  ... | equal   x   = y ∷ xs
  ... | greater y k = y ∷ insert x xs

  close : ℕ → FVs → FVs
  close k = concatMap λ x → if x <ᵇ k then [] else [ x ∸ k ]


------------------------------------------------------------------------
-- Annotation function computing free variables

freeVars : AnnotationFun (λ _ → FVs)
freeVars ⟨term⟩    (var x (⟨ fv ⟩ _))                                      = insert x fv
freeVars ⟨pat⟩     (var x)                                                 = x ∷ []
freeVars ⟨pat⟩     (absurd x)                                              = x ∷ []
         -- Note: variables are bound in the clause telescope, so we treat pattern variables as free
freeVars ⟨clause⟩  (clause {tel = Γ} (⟨ fvΓ ⟩ _) (⟨ fvps ⟩ _) (⟨ fvt ⟩ _)) = fvΓ ∪ close (length Γ) (fvps ∪ fvt)
freeVars ⟨clause⟩  (absurd-clause {tel = Γ} (⟨ fvΓ ⟩ _) (⟨ fvps ⟩ _))      = fvΓ ∪ close (length Γ) fvps
freeVars (⟨abs⟩ u) (abs _ (⟨ fv ⟩ _))                                      = close 1 fv
freeVars ⟨tel⟩     (⟨ fv ⟩ _ ∷ xs)                                         = fv ∪ close 1 (freeVars _ xs)
freeVars u         t                                                       = defaultAnn [] _∪_ u t

annotateFVs : ∀ {u} → (t : ⟦ u ⟧) → Annotated (λ _ → FVs) t
annotateFVs = annotate freeVars
