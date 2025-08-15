------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between module-like algebraic structures
------------------------------------------------------------------------
{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Module.Morphism.Structures where

open import Algebra.Module.Bundles.Raw
import Algebra.Module.Morphism.Polymorphic.Structures as Polymorphic
open import Function.Base using (id)

module LeftSemimoduleMorphisms {r} {m₁} {ℓm₁} {m₂} {ℓm₂} {R : Set r} (M₁ : RawLeftSemimodule R m₁ ℓm₁) (M₂ : RawLeftSemimodule R m₂ ℓm₂)
  = Polymorphic.LeftSemimoduleMorphisms {m₁ = m₁} {ℓm₁ = ℓm₁} {m₂ = m₂} {ℓm₂ = ℓm₂} (id {A = R}) M₁ M₂

module LeftModuleMorphisms {r} {m₁} {ℓm₁} {m₂} {ℓm₂} {R : Set r}
  = Polymorphic.LeftModuleMorphisms {m₁ = m₁} {ℓm₁ = ℓm₁} {m₂ = m₂} {ℓm₂ = ℓm₂} (id {A = R})

module RightSemimoduleMorphisms {r} {m₁} {ℓm₁} {m₂} {ℓm₂} {R : Set r}
  = Polymorphic.RightSemimoduleMorphisms {m₁ = m₁} {ℓm₁ = ℓm₁} {m₂ = m₂} {ℓm₂ = ℓm₂} (id {A = R})

module RightModuleMorphisms {r} {m₁} {ℓm₁} {m₂} {ℓm₂} {R : Set r}
  = Polymorphic.RightModuleMorphisms {m₁ = m₁} {ℓm₁ = ℓm₁} {m₂ = m₂} {ℓm₂ = ℓm₂} (id {A = R})

module BisemimoduleMorphisms {r} {s} {m₁} {ℓm₁} {m₂} {ℓm₂} {R : Set r} {S : Set s}
  = Polymorphic.BisemimoduleMorphisms {m₁ = m₁} {ℓm₁ = ℓm₁} {m₂ = m₂} {ℓm₂ = ℓm₂} (id {A = R}) (id {A = S})

module BimoduleMorphisms {r} {s} {m₁} {ℓm₁} {m₂} {ℓm₂} {R : Set r} {S : Set s}
  = Polymorphic.BimoduleMorphisms {m₁ = m₁} {ℓm₁ = ℓm₁} {m₂ = m₂} {ℓm₂ = ℓm₂} (id {A = R}) (id {A = S})

module SemimoduleMorphisms {r} {m₁} {ℓm₁} {m₂} {ℓm₂} {R : Set r}
  = Polymorphic.SemimoduleMorphisms {m₁ = m₁} {ℓm₁ = ℓm₁} {m₂ = m₂} {ℓm₂ = ℓm₂} (id {A = R})

module ModuleMorphisms {r} {m₁} {ℓm₁} {m₂} {ℓm₂} {R : Set r}
  = Polymorphic.ModuleMorphisms {m₁ = m₁} {ℓm₁ = ℓm₁} {m₂ = m₂} {ℓm₂ = ℓm₂} (id {A = R})

open LeftSemimoduleMorphisms public
open LeftModuleMorphisms public
open RightSemimoduleMorphisms public
open RightModuleMorphisms public
open BisemimoduleMorphisms public
open BimoduleMorphisms public
open SemimoduleMorphisms public
open ModuleMorphisms public
