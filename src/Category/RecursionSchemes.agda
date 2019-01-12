------------------------------------------------------------------------
-- The Agda standard library
--
-- Recursion schemes on initial objects of endofunctor algebras
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Category as Cat
open import Category.Functor
open import Category.Structures
open import Category.Algebra
open import Category.Construct.Algebra using (algebraCat)
open import Category.InitialObject
import Category.Structures using (module Endo)

open Cat.Category using (rawCategory)

module Category.RecursionSchemes {o m r}
                                 {cat : Category o m r}
                                 {F : EndoFunctor (rawCategory cat)}
                                 (ini : Initial (rawCategory (algebraCat cat F))) where
private
  rawF = Functor.rawFunctor F
  algCat = algebraCat cat F
  rawAlgCat = Category.rawCategory algCat

open RawFunctor rawF renaming (F to fun)
open Endo rawAlgCat using (IsInitial)
open Cat.Category cat hiding (module  ≈-Reasoning)
open Cat.Category algCat using (module ≈-Reasoning)
open Category.Construct.Algebra cat F
open Initial ini renaming (⊥ to inF; ! to ⦅_⦆F)
open _⇒alg_
open _≈alg_

private
  open Algebra inF renaming (Carrier to I)
  outF : I ⇒ fun I
  outF = translation ⦅ coalg ⦆F where
    coalg : Algebra rawF
    coalg = record { Carrier = fun I ; evaluate = fmap (evaluate inF) }
  by-universality : ∀ {alg : Algebra rawF}
                  → {morph1 : inF ⇒alg alg}
                  → {morph2 : inF ⇒alg alg}
                  → morph1 ≈alg morph2
  by-universality {alg} {morph1} {morph2} = begin
    morph1                  ≈⟨ ≈sym (!-unique morph1) ⟩
    ⦅ alg ⦆F                 ≈⟨ !-unique morph2 ⟩
    morph2                  ∎ where open ≈-Reasoning
  by-universality′ : ∀ {alg : Algebra rawF}
                   → (morph1 : inF ⇒alg alg)
                   → (morph2 : inF ⇒alg alg)
                   → translation morph1 ≈ translation morph2
  by-universality′ m n = morphs-eq (by-universality {morph1 = m} {morph2 = n})

⦅_⦆ : (alg : Algebra rawF) → I ⇒ Carrier alg
⦅ alg ⦆ = translation ⦅ alg ⦆F
cata : ∀ {U} → fun U ⇒ U → I ⇒ U
cata {U} alg = ⦅ record { evaluate = alg } ⦆

cata-refl : ⦅ inF ⦆ ≈ id
cata-refl = by-universality′ ⦅ inF ⦆F (id⇒alg inF)

cata-fusion : ∀ {ψ : Algebra rawF}{ϕ : Algebra rawF}{f : Carrier ϕ ⇒ Carrier ψ}
              → evaluate ψ ∘ fmap f ≈ f ∘ evaluate ϕ
              → f ∘ ⦅ ϕ ⦆ ≈ ⦅ ψ ⦆
cata-fusion {ψ = ψ}{ϕ}{f} eq = by-universality′ (ϕ→ψ ∘alg ⦅ ϕ ⦆F) ⦅ ψ ⦆F where
  ϕ→ψ : ϕ ⇒alg ψ
  ϕ→ψ = record { translation = f ; commutes = eq }
