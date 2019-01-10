------------------------------------------------------------------------
-- The Agda standard library
--
-- Recursion schemes on initial objects of endofunction algebras
------------------------------------------------------------------------

open import Category.Category

module Category.RecursionSchemes {ℓ}{cat : Category ℓ} where
open Category cat

open import Category.Functor cat cat renaming (RawFunctor to RawEndoFunctor)
open import Category.Structures using (IsCategory; IsFunctor)

module _ {fun : Obj → Obj}
         {F : RawEndoFunctor fun}
         {isCat : IsCategory cat}
         {isFun : IsFunctor cat cat F} where
  open import Category.Algebra cat
  open AlgebraCategory F isCat isFun
    using (AlgebraMorphism; _≈alg_; algebraCat; algebraCatIsCategory; idAlgebraMorphism; _∘alg_)
  open RawEndoFunctor F
  open import Category.InitialObject algebraCat
  open import Category.Structures algebraCat using (IsInitial)
  open IsCategory algebraCatIsCategory using (module ≈-Reasoning)
  module _ {ini : RawInitial}
           (isIni : IsInitial ini) where
    open Algebra
    open AlgebraMorphism
    open IsInitial isIni
    open _≈alg_
    private
      open RawInitial ini renaming (universality to ⦅_⦆F)
      open Algebra Universal renaming (Carrier to I) public
      outF : I ⇒ fun I
      outF = translation ⦅ coalg ⦆F where
        coalg : Algebra F
        coalg = record { Carrier = fun I ; evaluate = fmap (evaluate Universal) }
      by-universality : ∀ {alg : Algebra F}
                      → {morph1 : AlgebraMorphism Universal alg}
                      → {morph2 : AlgebraMorphism Universal alg}
                      → morph1 ≈alg morph2
      by-universality {alg} {morph1} {morph2} = begin
        morph1                  ≈⟨ ≈sym (uniqueUniversality morph1) ⟩
        ⦅ alg ⦆F                 ≈⟨ uniqueUniversality morph2 ⟩
        morph2                  ∎ where open ≈-Reasoning
      by-universality′ : ∀ {alg : Algebra F}
                       → (morph1 : AlgebraMorphism Universal alg)
                       → (morph2 : AlgebraMorphism Universal alg)
                       → translation morph1 ≈ translation morph2
      by-universality′ m n = (by-universality {morph1 = m} {morph2 = n}) .morphs-eq

    ⦅_⦆ : (alg : Algebra F) → I ⇒ Carrier alg
    ⦅ alg ⦆ = translation ⦅ alg ⦆F
    -- cata lifts a morphism to an algebra
    cata : ∀ {U} → fun U ⇒ U → I ⇒ U
    cata {U} alg = ⦅ record { Carrier = U; evaluate = alg } ⦆

    cata-refl : ⦅ Universal ⦆ ≈ id
    cata-refl = by-universality′ ⦅ Universal ⦆F (idAlgebraMorphism Universal)

    cata-fusion : ∀ {ψ : Algebra F}{ϕ : Algebra F}{f : Carrier ϕ ⇒ Carrier ψ}
                  → evaluate ψ ∘ fmap f ≈ f ∘ evaluate ϕ
                  → f ∘ ⦅ ϕ ⦆ ≈ ⦅ ψ ⦆
    cata-fusion {ψ = ψ}{ϕ}{f} eq = by-universality′ (ϕ→ψ ∘alg ⦅ ϕ ⦆F) ⦅ ψ ⦆F where
      ϕ→ψ : AlgebraMorphism ϕ ψ
      ϕ→ψ = record { translation = f ; commutes = eq }
