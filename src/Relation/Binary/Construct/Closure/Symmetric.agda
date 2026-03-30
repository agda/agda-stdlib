------------------------------------------------------------------------
-- The Agda standard library
--
-- Symmetric closures of binary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Closure.Symmetric where

open import Function.Base using (id; _on_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel; _=[_]⇒_; _⇒_)
open import Relation.Binary.Definitions using (Symmetric)
import Relation.Binary.Construct.On as On

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B C : Set a
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

-- A generalised variant of `map` where *both* index types can change.
hmap : ∀ (g : C → A) (f : C → B) → (R on g) ⇒ (S on f) →
       ((SymClosure R) on g) ⇒ ((SymClosure S) on f)
hmap _ _ g*R⇒f*S (fwd aRb) = fwd (g*R⇒f*S aRb)
hmap _ _ g*R⇒f*S (bwd bRa) = bwd (g*R⇒f*S bRa)

-- Hence: SymClosure commutes with `on`
on⁺ : (g : B → A) → ((SymClosure R) on g) ⇒ SymClosure (R on g)
on⁺ g = hmap g id id

on⁻ : (g : B → A) → SymClosure (R on g) ⇒ ((SymClosure R) on g)
on⁻ g = hmap id g id

-- And: the 'usual' generalised variant of `map`
gmap : (f : A → B) → R =[ f ]⇒ S → SymClosure R =[ f ]⇒ SymClosure S
gmap = hmap id

map : R ⇒ S → SymClosure R ⇒ SymClosure S
map = gmap id

fold : Symmetric S → R ⇒ S → SymClosure R ⇒ S
fold S-sym R⇒S (fwd aRb) = R⇒S aRb
fold S-sym R⇒S (bwd bRa) = S-sym (R⇒S bRa)

-- A generalised variant of `fold`.
gfold : Symmetric S → (f : A → B) → R =[ f ]⇒ S → SymClosure R =[ f ]⇒ S
gfold {S = S} S-sym f R⇒S = fold (On.symmetric f S S-sym) R⇒S

-- `return` could also be called `singleton`.
return : R ⇒ SymClosure R
return = fwd

-- `join` could also be called `concat`.
join : SymClosure (SymClosure R) ⇒ SymClosure R
join = fold (symmetric _) id

infix 10 _⋆

_⋆ : R ⇒ SymClosure S → SymClosure R ⇒ SymClosure S
_⋆ f m = join (map f m)
