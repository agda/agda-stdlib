------------------------------------------------------------------------
-- The Agda standard library
--
-- Symmetric closures of binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Closure.Symmetric where

open import Function.Base using (id; _on_)
open import Level using (Level; _⊔_)
open import Relation.Binary
import Relation.Binary.Construct.On as On

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a
    R S : Rel A ℓ

------------------------------------------------------------------------
-- Definition

data SymClosure {A : Set a} (R : Rel A ℓ) (a b : A) : Set ℓ where
  fwd : R a b → SymClosure R a b
  bwd : R b a → SymClosure R a b

------------------------------------------------------------------------
-- Properties

-- Symmetric closures are symmetric.
symmetric : (R : Rel A ℓ) → Symmetric (SymClosure R)
symmetric _ (fwd aRb) = bwd aRb
symmetric _ (bwd bRa) = fwd bRa

------------------------------------------------------------------------
-- Operations

-- A generalised variant of map which allows the index type to change.
gmap : (f : A → B) → R =[ f ]⇒ S → SymClosure R =[ f ]⇒ SymClosure S
gmap _ g (fwd aRb) = fwd (g aRb)
gmap _ g (bwd bRa) = bwd (g bRa)

map : R ⇒ S → SymClosure R ⇒ SymClosure S
map = gmap id

module _ (S-symmetric : Symmetric S) (R⇒S : R ⇒ S) where
  fold : SymClosure R ⇒ S
  fold (fwd aRb) = R⇒S aRb
  fold (bwd bRa) = S-symmetric (R⇒S bRa)

module _ (S-symmetric : Symmetric S) (f : A → B) (R⇒S : R =[ f ]⇒ S) where
  gfold : SymClosure R =[ f ]⇒ S
  gfold = fold (On.symmetric f S S-symmetric) R⇒S

return : R ⇒ SymClosure R
return = fwd

join : SymClosure (SymClosure R) ⇒ SymClosure R
join = fold (symmetric _) id

infix 10 _⋆

_⋆ : R ⇒ SymClosure S → SymClosure R ⇒ SymClosure S
_⋆ f m = join (map f m)
