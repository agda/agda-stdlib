------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of 'pre-free' and 'free' magma
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Bundles.Free.Pointed where

open import Algebra.Core
open import Algebra.Bundles using (Pointed)
open import Algebra.Bundles.Raw using (RawPointed)
import Algebra.Definitions as Definitions using (Congruent₂)
import Algebra.Structures as Structures using (IsPointed)
open import Algebra.Morphism.Structures using (IsPointedHomomorphism)
import Algebra.Morphism.Construct.Identity as Identity
import Algebra.Morphism.Construct.Composition as Compose
open import Effect.Functor
open import Effect.Monad
open import Function.Base using (id; _∘_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Morphism using (IsRelHomomorphism)
open import Level using (Level; suc; _⊔_)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary
  using (Setoid; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary.Morphism.Bundles using (SetoidHomomorphism)
import Relation.Binary.Morphism.Construct.Identity as Identity
import Relation.Binary.Morphism.Construct.Composition as Compose
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong₂) renaming (refl to ≡-refl; isEquivalence to ≡-isEquivalence)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    ℓ a ℓa b ℓb c ℓc m ℓm n ℓn : Level
    A : Set a
    B : Set b
    C : Set c


------------------------------------------------------------------------
-- Morphisms between Pointeds: belongs in its own place
-- Algebra.Morphism.Bundles
-- open import Algebra.Morphism.Bundles using (PointedHomomorphism)
------------------------------------------------------------------------

record PointedHomomorphism (𝓐 : Pointed a ℓa) (𝓑 : Pointed b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where

  open Pointed 𝓐 renaming (rawPointed to rawPointedᴬ; setoid to setoidᴬ; Carrier to UA)
  open Pointed 𝓑 renaming (rawPointed to rawPointedᴮ; setoid to setoidᴮ; Carrier to UB)

  field
    ⟦_⟧ : UA → UB

    isPointedHomomorphism : IsPointedHomomorphism rawPointedᴬ rawPointedᴮ ⟦_⟧

  open IsPointedHomomorphism isPointedHomomorphism public

  setoidHomomorphism : SetoidHomomorphism setoidᴬ setoidᴮ
  setoidHomomorphism = record { ⟦_⟧ = ⟦_⟧ ; isRelHomomorphism = isRelHomomorphism }

 
------------------------------------------------------------------------
-- Syntax: 'pre'-free algebra

module Syntax where

  data Syntax (A : Set a) : Set a where

    var : A → Syntax A
    pt₀ : Syntax A

-- Functor instance

  map : (A → B) → Syntax A → Syntax B
  map f (var a) = var (f a)
  map f pt₀     = pt₀

  map-id : ∀ (t : Syntax A) → map id t ≡ t
  map-id (var a) = ≡-refl
  map-id pt₀     = ≡-refl

  map-∘ : (g : A → B) → (f : B → C) → ∀ t → map (f ∘ g) t ≡ (map f ∘ map g) t
  map-∘ g f (var a) = ≡-refl
  map-∘ g f pt₀     = ≡-refl

  syntaxRawFunctor : RawFunctor (Syntax {a})
  syntaxRawFunctor = record { _<$>_ = map }

-- Monad instance

  bind : Syntax A → (A → Syntax B) → Syntax B
  bind (var x) h = h x
  bind pt₀     _ = pt₀

  syntaxRawMonad : RawMonad (Syntax {a})
  syntaxRawMonad = mkRawMonad Syntax var bind

------------------------------------------------------------------------
-- parametrised 'equational' theory over the 'pre'-free algebra

module EquationalTheory {A : Set a} (_≈ᴬ_ : Rel A ℓ) where

  open Syntax

  infix 4 _≈_

  data _≈_ : Rel (Syntax A) (a ⊔ ℓ)

  open Definitions _≈_

  data _≈_ where

    var : {a b : A} → a ≈ᴬ b → var a ≈ var b
    pt₀ : pt₀ ≈ pt₀

  refl : Reflexive _≈ᴬ_ → Reflexive _≈_
  refl r {var _} = var r
  refl r {pt₀}   = pt₀

  sym : Symmetric _≈ᴬ_ → Symmetric _≈_
  sym s (var s₀) = var (s s₀)
  sym s pt₀     = pt₀

  trans : Transitive _≈ᴬ_ → Transitive _≈_
  trans t (var r) (var s) = var (t r s)
  trans t pt₀     pt₀     = pt₀

  preservesEquivalence : IsEquivalence _≈ᴬ_ → IsEquivalence _≈_
  preservesEquivalence isEq = record
    { refl = refl Eq.refl ; sym = sym Eq.sym ; trans = trans Eq.trans }
    where module Eq = IsEquivalence isEq

  varIsRelHomomorphism : IsRelHomomorphism _≈ᴬ_ _≈_ var
  varIsRelHomomorphism = record { cong = var }


------------------------------------------------------------------------
-- Free algebra on a Set
{-
   in the propositional case, we can immediately define the following
   but how best to organise this under the Algebra.Bundles.Free hierarchy?
   e.g. should we distinguish Free.Pointed.Setoid from Free.Pointed.Propositional?
-}

module FreeRawPointed (A : Set a) where

  open Syntax

  open EquationalTheory {A = A} _≡_

-- inductively-defined equational theory conincides with _≡_

  ≈⇒≡ : ∀ {m n} → m ≈ n → m ≡ n
  ≈⇒≡ (var ≡-refl) = ≡-refl
  ≈⇒≡ pt₀          = ≡-refl

  ≡⇒≈ : ∀ {m n} → m ≡ n → m ≈ n
  ≡⇒≈ ≡-refl = refl ≡-refl

  freeRawPointed : RawPointed a a
  freeRawPointed = record { Carrier = Syntax A ; _≈_ = _≡_ ; pt₀ = pt₀ }

  open Structures {A = Syntax A} _≡_

  isPointed : IsPointed pt₀
  isPointed = record { isEquivalence = ≡-isEquivalence }

  freePointed : Pointed a a
  freePointed = record { RawPointed freeRawPointed ; isPointed = isPointed }

------------------------------------------------------------------------
-- Free algebra on a Setoid

module FreePointed (𝓐 : Setoid a ℓa) where

  open Setoid 𝓐 renaming (isEquivalence to isEqᴬ; _≈_ to _≈ᴬ_)

  open Syntax

  open EquationalTheory _≈ᴬ_ public
    renaming (_≈_ to _≈ᵀ_) hiding (refl; sym; trans)

  open Structures _≈ᵀ_

  isPointed : IsPointed pt₀
  isPointed = record { isEquivalence = preservesEquivalence isEqᴬ }

  freePointed : Pointed a (a ⊔ ℓa)
  freePointed = record { Carrier = Syntax Carrier; _≈_ = _≈ᵀ_ ; pt₀ = pt₀ ; isPointed = isPointed }

-- reexport some substructure

  open Pointed freePointed public using (rawPointed; setoid; Carrier; _≈_)
  
  varSetoidHomomorphism : SetoidHomomorphism 𝓐 setoid
  varSetoidHomomorphism = record { ⟦_⟧ = var; isRelHomomorphism = varIsRelHomomorphism }

------------------------------------------------------------------------
-- Semantics: in terms of concrete Pointed instances

module _ (𝓟 : Pointed m ℓm) where

  open Pointed 𝓟 renaming (setoid to setoidᴾ; Carrier to UP; pt₀ to ptᴾ)
  open Syntax

------------------------------------------------------------------------
-- Eval, as the unique fold ⟦_⟧_ over Syntax

  module Eval (𝓐 : Setoid a ℓa) where

    open Setoid 𝓐 renaming (Carrier to UA)

    ⟦_⟧_ : Syntax UA → (UA → UP) → UP
    ⟦ var a ⟧ η = η a
    ⟦ pt₀ ⟧ η   = ptᴾ

------------------------------------------------------------------------
-- Any Pointed *is* an algebra for the Syntax Functor
  
  alg : Syntax UP → UP
  alg t = ⟦ t ⟧ id where open Eval setoidᴾ

------------------------------------------------------------------------
-- ⟦_⟧_ defines the (unique) lifting of Setoid homomorphisms to Pointed homomorphisms

module LeftAdjoint {𝓐 : Setoid a ℓa} (𝓟 : Pointed m ℓm)
       (𝓗 :  SetoidHomomorphism 𝓐 (Pointed.setoid 𝓟)) where

  open Pointed 𝓟
    renaming (Carrier to UP; _≈_ to _≈ᴾ_; pt₀ to ptᴾ; refl to reflᴾ
             ; setoid to setoidᴾ; rawPointed to rawPointedᴾ
             ; isPointed to isPointedᴾ)

  open ≈-Reasoning setoidᴾ

  open Syntax

  open Setoid 𝓐 renaming (Carrier to UA; _≈_ to _≈ᴬ_)

  open Eval 𝓟 𝓐 public

  open FreePointed 𝓐 renaming (setoid to FA; Carrier to UFA)

  open SetoidHomomorphism 𝓗 renaming (⟦_⟧ to η; isRelHomomorphism to hom-η) 

  private
  
    ⟦_⟧ᴾ : UFA → UP
    ⟦_⟧ᴾ = ⟦_⟧ η

  open Structures _≈ᴾ_
  open IsPointed isPointedᴾ
  open IsRelHomomorphism hom-η renaming (cong to cong-η)

  module Existence where
  
    private
      algᴾ = alg 𝓟

    unfold-⟦_⟧ᴾ : ∀ t → ⟦ t ⟧ᴾ ≈ᴾ algᴾ (map η t)
    unfold-⟦ var a ⟧ᴾ = reflᴾ
    unfold-⟦ pt₀ ⟧ᴾ   = reflᴾ

    cong-⟦_⟧ : ∀ {s t} → s ≈ t → ⟦ s ⟧ᴾ ≈ᴾ ⟦ t ⟧ᴾ
    cong-⟦ var r ⟧ = cong-η r
    cong-⟦ pt₀ ⟧   = reflᴾ

    isRelHomomorphismᴾ : IsRelHomomorphism _≈_ _≈ᴾ_ ⟦_⟧ᴾ
    isRelHomomorphismᴾ = record { cong = cong-⟦_⟧ }

    setoidHomomorphismᴾ : SetoidHomomorphism FA setoidᴾ
    setoidHomomorphismᴾ = record { ⟦_⟧ = ⟦_⟧ᴾ ; isRelHomomorphism = isRelHomomorphismᴾ }

    isPointedHomomorphismᴾ : IsPointedHomomorphism rawPointed rawPointedᴾ ⟦_⟧ᴾ
    isPointedHomomorphismᴾ = record { isRelHomomorphism = isRelHomomorphismᴾ
                                    ; homo = reflᴾ}

    magmaHomomorphismᴾ : PointedHomomorphism freePointed 𝓟
    magmaHomomorphismᴾ = record { ⟦_⟧ = ⟦_⟧ᴾ
                               ; isPointedHomomorphism = isPointedHomomorphismᴾ }

  record η-PointedHomomorphism : Set (suc (a ⊔ m ⊔ ℓa ⊔ ℓm)) where

    field
      magmaHomomorphism : PointedHomomorphism freePointed 𝓟
    open PointedHomomorphism magmaHomomorphism public renaming (homo to ⟦⟧-homo)
    field
      ⟦_⟧∘var≈ᴾη : ∀ a → ⟦ var a ⟧ ≈ᴾ η a

  ⟦⟧ᴾ-η-PointedHomomorphism : η-PointedHomomorphism
  ⟦⟧ᴾ-η-PointedHomomorphism = record { magmaHomomorphism = Existence.magmaHomomorphismᴾ
                                   ; ⟦_⟧∘var≈ᴾη = Existence.unfold-⟦_⟧ᴾ ∘ var } 

  module Uniqueness (η-magmaHomomorphism : η-PointedHomomorphism) where
      
    open η-PointedHomomorphism η-magmaHomomorphism
      
    isUnique⟦_⟧ᴾ : ∀ t → ⟦ t ⟧ ≈ᴾ ⟦ t ⟧ᴾ
    isUnique⟦ var a ⟧ᴾ = ⟦ a ⟧∘var≈ᴾη
    isUnique⟦ pt₀ ⟧ᴾ   = ⟦⟧-homo
      
  module Corollary (𝓗 𝓚 : η-PointedHomomorphism)
    where
      open η-PointedHomomorphism 𝓗 renaming (⟦_⟧ to ⟦_⟧ᴴ)
      open η-PointedHomomorphism 𝓚 renaming (⟦_⟧ to ⟦_⟧ᴷ)
      open Uniqueness 𝓗 renaming (isUnique⟦_⟧ᴾ to isUnique⟦_⟧ᴴ)
      open Uniqueness 𝓚 renaming (isUnique⟦_⟧ᴾ to isUnique⟦_⟧ᴷ)
      
      isUnique⟦_⟧ :  ∀ t → ⟦ t ⟧ᴴ ≈ᴾ ⟦ t ⟧ᴷ
      isUnique⟦ t ⟧ = begin ⟦ t ⟧ᴴ ≈⟨ isUnique⟦ t ⟧ᴴ ⟩ ⟦ t ⟧ᴾ ≈˘⟨ isUnique⟦ t ⟧ᴷ ⟩ ⟦ t ⟧ᴷ ∎

------------------------------------------------------------------------
-- Immediate corollary: alg is in fact a PointedHomomorphism

module _ (𝓟 : Pointed m ℓm) where
  open Pointed 𝓟 renaming (setoid to setoidᴾ)
  open FreePointed setoidᴾ
  
  algPointedHomomorphism : PointedHomomorphism freePointed 𝓟
  algPointedHomomorphism = Existence.magmaHomomorphismᴾ
    where open LeftAdjoint 𝓟 (Identity.setoidHomomorphism setoidᴾ)


------------------------------------------------------------------------
-- Action of FreePointed on Setoid homomorphisms

module FreePointedFunctor {𝓐 : Setoid a ℓa} {𝓑 : Setoid b ℓb}
       (𝓗 : SetoidHomomorphism 𝓐 𝓑) where

  open FreePointed 𝓐 renaming (freePointed to freePointedᴬ)
  open FreePointed 𝓑 renaming (freePointed to freePointedᴮ
                             ; varSetoidHomomorphism to 𝓥ᴮ)

  mapPointedHomomorphism : PointedHomomorphism freePointedᴬ freePointedᴮ
  mapPointedHomomorphism = Existence.magmaHomomorphismᴾ
    where open LeftAdjoint freePointedᴮ (Compose.setoidHomomorphism 𝓗 𝓥ᴮ)

------------------------------------------------------------------------
-- Naturality of alg

module Naturality {𝓟 : Pointed m ℓm} {𝓠 : Pointed n ℓn} where
  open Pointed 𝓟 using () renaming (setoid to setoidᴾ)
  open Pointed 𝓠 using () renaming (_≈_ to _≈ᴺ_; refl to reflᴺ; trans to transᴺ)

  module _ (𝓕 : PointedHomomorphism 𝓟 𝓠) where
    open PointedHomomorphism 𝓕 using (⟦_⟧; isPointedHomomorphism; setoidHomomorphism)
    open FreePointedFunctor setoidHomomorphism using (mapPointedHomomorphism)
    open PointedHomomorphism mapPointedHomomorphism
      renaming (⟦_⟧ to map; isPointedHomomorphism to map-isPointedHomomorphism; setoidHomomorphism to mapSetoidHomomorphism)
    open FreePointed setoidᴾ renaming (freePointed to freePointedᴾ)
    open LeftAdjoint 𝓠 setoidHomomorphism
    open PointedHomomorphism (algPointedHomomorphism 𝓟)
      renaming (⟦_⟧ to algᴾ; isPointedHomomorphism to algᴾ-isPointedHomomorphism)
    open PointedHomomorphism (algPointedHomomorphism 𝓠)
      renaming (⟦_⟧ to algᴺ; isPointedHomomorphism to algᴺ-isPointedHomomorphism)

    naturality : ∀ t → ⟦ algᴾ t ⟧ ≈ᴺ algᴺ (map t)
    naturality = Corollary.isUnique⟦_⟧ 𝓗 𝓚
      where
        H K : PointedHomomorphism freePointedᴾ 𝓠
        H = record { ⟦_⟧ = ⟦_⟧ ∘ algᴾ
            ; isPointedHomomorphism = Compose.isPointedHomomorphism transᴺ algᴾ-isPointedHomomorphism isPointedHomomorphism }

        K = record { ⟦_⟧ = algᴺ ∘  map
            ; isPointedHomomorphism = Compose.isPointedHomomorphism transᴺ map-isPointedHomomorphism algᴺ-isPointedHomomorphism }

        𝓗 𝓚 : η-PointedHomomorphism
        𝓗 = record { magmaHomomorphism = H ; ⟦_⟧∘var≈ᴾη = λ _ → reflᴺ }
        𝓚 = record { magmaHomomorphism = K ; ⟦_⟧∘var≈ᴾη = λ _ → reflᴺ }


------------------------------------------------------------------------
-- Functoriality of FreePointedFunctor.map : by analogy with naturality

module IdentityLaw (𝓐 : Setoid a ℓa) where

  open FreePointed 𝓐 renaming (varSetoidHomomorphism to 𝓥)
  open Setoid setoid renaming (_≈_ to _≈FA_; refl to reflFA)                             

  Id : PointedHomomorphism freePointed freePointed
  Id = record
    { ⟦_⟧ = id
    ; isPointedHomomorphism = Identity.isPointedHomomorphism rawPointed reflFA}

  open FreePointedFunctor (Identity.setoidHomomorphism 𝓐)
  open PointedHomomorphism mapPointedHomomorphism renaming (⟦_⟧ to map-Id)

  map-id : ∀ t → map-Id t ≈FA t
  map-id = Corollary.isUnique⟦_⟧ 𝓘ᴬ 𝓘
    where
      open LeftAdjoint freePointed 𝓥
      𝓘ᴬ 𝓘 : η-PointedHomomorphism
      𝓘ᴬ = record { magmaHomomorphism = mapPointedHomomorphism ; ⟦_⟧∘var≈ᴾη = λ _ → reflFA }
      𝓘 = record { magmaHomomorphism = Id ; ⟦_⟧∘var≈ᴾη = λ _ → reflFA }

module CompositionLaw
  {𝓐 : Setoid a ℓa} {𝓑 : Setoid b ℓb} {𝓒 : Setoid c ℓc}
  (𝓗 : SetoidHomomorphism 𝓐 𝓑) (𝓚 : SetoidHomomorphism 𝓑 𝓒) where

  𝓕 : SetoidHomomorphism 𝓐 𝓒
  𝓕 = Compose.setoidHomomorphism 𝓗 𝓚

  open FreePointed 𝓐 renaming (freePointed to freePointedA)
  open FreePointed 𝓑 renaming (freePointed to freePointedB)
  open FreePointed 𝓒 renaming (freePointed to freePointedC
                             ; setoid to setoidFC
                             ; varSetoidHomomorphism to 𝓥)
  open Setoid setoidFC renaming (_≈_ to _≈FC_; refl to reflFC; trans to transFC)                             
  𝓥∘𝓕 = Compose.setoidHomomorphism 𝓕 𝓥
  open FreePointedFunctor 𝓕 renaming (mapPointedHomomorphism to MapAC)
  open FreePointedFunctor 𝓗 renaming (mapPointedHomomorphism to MapAB)
  open FreePointedFunctor 𝓚 renaming (mapPointedHomomorphism to MapBC)
  open PointedHomomorphism MapAC renaming (⟦_⟧ to mapAC)
  open PointedHomomorphism MapAB renaming (⟦_⟧ to mapAB; isPointedHomomorphism to isPointedAB)
  open PointedHomomorphism MapBC renaming (⟦_⟧ to mapBC; isPointedHomomorphism to isPointedBC)

  MapBC∘MapAB : PointedHomomorphism freePointedA freePointedC
  MapBC∘MapAB = record
    { ⟦_⟧ = mapBC ∘ mapAB
    ; isPointedHomomorphism = Compose.isPointedHomomorphism transFC isPointedAB isPointedBC}

  map-∘ : ∀ t → mapAC t ≈FC mapBC (mapAB t)
  map-∘ = Corollary.isUnique⟦_⟧ 𝓐𝓒 𝓑𝓒∘𝓐𝓑
    where
      open LeftAdjoint freePointedC 𝓥∘𝓕
      𝓐𝓒 𝓑𝓒∘𝓐𝓑 : η-PointedHomomorphism
      𝓐𝓒 = record { magmaHomomorphism = MapAC ; ⟦_⟧∘var≈ᴾη = λ _ → reflFC }
      𝓑𝓒∘𝓐𝓑 = record { magmaHomomorphism = MapBC∘MapAB ; ⟦_⟧∘var≈ᴾη = λ _ → reflFC }


------------------------------------------------------------------------
-- Monad instance, etc.: TODO


