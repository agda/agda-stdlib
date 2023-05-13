------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of 'pre-free' and 'free' magma
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Bundles.Free.Magma where

open import Algebra.Core
open import Algebra.Bundles using (Magma)
open import Algebra.Bundles.Raw using (RawMagma)
import Algebra.Definitions as Definitions using (Congruent₂)
import Algebra.Structures as Structures using (IsMagma)
open import Algebra.Morphism.Structures using (IsMagmaHomomorphism)
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
  using (_≡_; _≗_; cong₂) renaming (refl to ≡-refl; isEquivalence to ≡-isEquivalence)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    ℓ a ℓa b ℓb c ℓc m ℓm n ℓn : Level
    A : Set a
    B : Set b
    C : Set c


------------------------------------------------------------------------
-- Morphisms between Magmas: belongs in its own place
-- Algebra.Morphism.Bundles
-- open import Algebra.Morphism.Bundles using (MagmaHomomorphism)
------------------------------------------------------------------------

record MagmaHomomorphism (𝓐 : Magma a ℓa) (𝓑 : Magma b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where

  open Magma 𝓐 renaming (rawMagma to rawMagmaᴬ; setoid to setoidᴬ; Carrier to UA)
  open Magma 𝓑 renaming (rawMagma to rawMagmaᴮ; setoid to setoidᴮ; Carrier to UB)

  field
    ⟦_⟧ : UA → UB

    isMagmaHomomorphism : IsMagmaHomomorphism rawMagmaᴬ rawMagmaᴮ ⟦_⟧

  open IsMagmaHomomorphism isMagmaHomomorphism public

  setoidHomomorphism : SetoidHomomorphism setoidᴬ setoidᴮ
  setoidHomomorphism = record { ⟦_⟧ = ⟦_⟧ ; isRelHomomorphism = isRelHomomorphism }

------------------------------------------------------------------------
-- Syntax: 'pre'-free algebra

module Syntax where

  infixl 7 _∙_

  data Syntax (A : Set a) : Set a where

    var : A → Syntax A
    _∙_ : Op₂ (Syntax A)

-- Functor instance

  map : (A → B) → Syntax A → Syntax B
  map f (var a) = var (f a)
  map f (s ∙ t) = (map f s) ∙ (map f t)

  map-id : map {A = A} id ≗ id
  map-id (var a) = ≡-refl
  map-id (s ∙ t) = cong₂ _∙_ (map-id s) (map-id t)

  map-∘ : (g : A → B) → (f : B → C) → map (f ∘ g) ≗ (map f ∘ map g)
  map-∘ g f (var a) = ≡-refl
  map-∘ g f (s ∙ t) = cong₂ _∙_ (map-∘ g f s) (map-∘ g f t)

  syntaxRawFunctor : RawFunctor (Syntax {a})
  syntaxRawFunctor = record { _<$>_ = map }

-- Monad instance

  bind : Syntax A → (A → Syntax B) → Syntax B
  bind (var x) h = h x
  bind (s ∙ t) h = bind s h ∙ bind t h

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
    _∙_ : Congruent₂ _∙_

  refl : Reflexive _≈ᴬ_ → Reflexive _≈_
  refl r {var _} = var r
  refl r {_ ∙ _} = (refl r) ∙ (refl r)

  sym : Symmetric _≈ᴬ_ → Symmetric _≈_
  sym s (var s₀)  = var (s s₀)
  sym s (s₁ ∙ s₂) = sym s s₁ ∙ sym s s₂

  trans : Transitive _≈ᴬ_ → Transitive _≈_
  trans t (var r₀)  (var s₀)  = var (t r₀ s₀)
  trans t (r₁ ∙ r₂) (s₁ ∙ s₂) = trans t r₁ s₁ ∙ trans t r₂ s₂

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
   e.g. should we distinguish Free.Magma.Setoid from Free.Magma.Propositional?
-}

module FreeRawMagma (A : Set a) where

  open Syntax

  open EquationalTheory {A = A} _≡_

-- inductively-defined equational theory conincides with _≡_

  ≈⇒≡ : ∀ {m n} → m ≈ n → m ≡ n
  ≈⇒≡ (var ≡-refl) = ≡-refl
  ≈⇒≡ (eq₁ ∙ eq₂) = cong₂ _∙_ (≈⇒≡ eq₁) (≈⇒≡ eq₂)

  ≡⇒≈ : ∀ {m n} → m ≡ n → m ≈ n
  ≡⇒≈ ≡-refl = refl ≡-refl

  freeRawMagma : RawMagma a a
  freeRawMagma = record { Carrier = Syntax A ; _≈_ = _≡_ ; _∙_ = _∙_ }

  open Structures {A = Syntax A} _≡_

  isMagma : IsMagma _∙_
  isMagma = record { isEquivalence = ≡-isEquivalence ; ∙-cong = cong₂ _∙_ }

  freeMagma : Magma a a
  freeMagma = record { RawMagma freeRawMagma ; isMagma = isMagma }


------------------------------------------------------------------------
-- Free algebra on a Setoid

module FreeMagma (𝓐 : Setoid a ℓa) where

  open Setoid 𝓐 renaming (isEquivalence to isEqᴬ; _≈_ to _≈ᴬ_)

  open Syntax

  open EquationalTheory _≈ᴬ_ public
    renaming (_≈_ to _≈ᵀ_) hiding (refl; sym; trans)

  open Structures _≈ᵀ_

  isMagma : IsMagma  _∙_
  isMagma = record { isEquivalence = preservesEquivalence isEqᴬ ; ∙-cong = _∙_ }

  freeMagma : Magma a (a ⊔ ℓa)
  freeMagma = record { Carrier = Syntax Carrier; _≈_ = _≈ᵀ_ ; _∙_ = _∙_ ; isMagma = isMagma }

-- re-export some substructure

  open Magma freeMagma public using (rawMagma; setoid; Carrier; _≈_)

  varSetoidHomomorphism : SetoidHomomorphism 𝓐 setoid
  varSetoidHomomorphism = record { ⟦_⟧ = var; isRelHomomorphism = varIsRelHomomorphism }


------------------------------------------------------------------------
-- Semantics: in terms of concrete Magma instances

module _ (𝓜 : Magma m ℓm) where

  open Magma 𝓜 renaming (setoid to setoidᴹ; Carrier to UM; _∙_ to _∙ᴹ_)
  open Syntax

------------------------------------------------------------------------
-- Eval, as the unique fold ⟦_⟧_ over Syntax

  module Eval (𝓐 : Setoid a ℓa) where

    open Setoid 𝓐 renaming (Carrier to UA)

    ⟦_⟧_ : Syntax UA → (UA → UM) → UM
    ⟦ var a ⟧ η = η a
    ⟦ s ∙ t ⟧ η = ⟦ s ⟧ η ∙ᴹ ⟦ t ⟧ η

------------------------------------------------------------------------
-- Any Magma *is* an algebra for the Syntax Functor

  alg : Syntax UM → UM
  alg t = ⟦ t ⟧ id where open Eval setoidᴹ

------------------------------------------------------------------------
-- ⟦_⟧_ defines the (unique) lifting of Setoid homomorphisms to Magma homomorphisms

module LeftAdjoint {𝓐 : Setoid a ℓa} (𝓜 : Magma m ℓm)
       (𝓗 :  SetoidHomomorphism 𝓐 (Magma.setoid 𝓜)) where

  open Magma 𝓜
    renaming (Carrier to UM; _≈_ to _≈ᴹ_; _∙_ to _∙ᴹ_
             ; setoid to setoidᴹ; rawMagma to rawMagmaᴹ
             ; isMagma to isMagmaᴹ)

  open ≈-Reasoning setoidᴹ

  open Syntax

  open Setoid 𝓐 renaming (Carrier to UA; _≈_ to _≈ᴬ_)

  open Eval 𝓜 𝓐 public

  open FreeMagma 𝓐 renaming (setoid to FA; Carrier to UFA)

  open SetoidHomomorphism 𝓗 renaming (⟦_⟧ to η; isRelHomomorphism to hom-η)

  private

    ⟦_⟧ᴹ : UFA → UM
    ⟦_⟧ᴹ = ⟦_⟧ η

  open Structures _≈ᴹ_
  open IsMagma isMagmaᴹ renaming (∙-cong to congᴹ)
  open IsRelHomomorphism hom-η renaming (cong to cong-η)

  module Existence where

    private
      algᴹ = alg 𝓜

    unfold-⟦_⟧ᴹ : ∀ t → ⟦ t ⟧ᴹ ≈ᴹ algᴹ (map η t)
    unfold-⟦ var a ⟧ᴹ = begin η a ∎
    unfold-⟦ s ∙ t ⟧ᴹ = congᴹ unfold-⟦ s ⟧ᴹ unfold-⟦ t ⟧ᴹ

    cong-⟦_⟧ : ∀ {s t} → s ≈ t → ⟦ s ⟧ᴹ ≈ᴹ ⟦ t ⟧ᴹ
    cong-⟦ var r ⟧ = cong-η r
    cong-⟦ s ∙ t ⟧ = congᴹ cong-⟦ s ⟧ cong-⟦ t ⟧

    isRelHomomorphismᴹ : IsRelHomomorphism _≈_ _≈ᴹ_ ⟦_⟧ᴹ
    isRelHomomorphismᴹ = record { cong = cong-⟦_⟧ }

    setoidHomomorphismᴹ : SetoidHomomorphism FA setoidᴹ
    setoidHomomorphismᴹ = record { ⟦_⟧ = ⟦_⟧ᴹ ; isRelHomomorphism = isRelHomomorphismᴹ }

    isMagmaHomomorphismᴹ : IsMagmaHomomorphism rawMagma rawMagmaᴹ ⟦_⟧ᴹ
    isMagmaHomomorphismᴹ = record { isRelHomomorphism = isRelHomomorphismᴹ
                                  ; homo = λ s t → begin ⟦ s ⟧ᴹ ∙ᴹ ⟦ t ⟧ᴹ ∎ }

    magmaHomomorphismᴹ : MagmaHomomorphism freeMagma 𝓜
    magmaHomomorphismᴹ = record { ⟦_⟧ = ⟦_⟧ᴹ
                               ; isMagmaHomomorphism = isMagmaHomomorphismᴹ }

  record η-MagmaHomomorphism : Set (suc (a ⊔ m ⊔ ℓa ⊔ ℓm)) where

    field
      magmaHomomorphism : MagmaHomomorphism freeMagma 𝓜
    open MagmaHomomorphism magmaHomomorphism public renaming (homo to ⟦⟧-homo)
    field
      ⟦_⟧∘var≈ᴹη : ∀ a → ⟦ var a ⟧ ≈ᴹ η a

  ⟦⟧ᴹ-η-MagmaHomomorphism : η-MagmaHomomorphism
  ⟦⟧ᴹ-η-MagmaHomomorphism = record { magmaHomomorphism = Existence.magmaHomomorphismᴹ
                                   ; ⟦_⟧∘var≈ᴹη = Existence.unfold-⟦_⟧ᴹ ∘ var }

  module Uniqueness (η-magmaHomomorphism : η-MagmaHomomorphism) where

    open η-MagmaHomomorphism η-magmaHomomorphism

    isUnique⟦_⟧ᴹ : ∀ t → ⟦ t ⟧ ≈ᴹ ⟦ t ⟧ᴹ
    isUnique⟦ var a ⟧ᴹ = ⟦ a ⟧∘var≈ᴹη
    isUnique⟦ s ∙ t ⟧ᴹ = begin
        ⟦ s Syntax.∙ t ⟧  ≈⟨ ⟦⟧-homo s t ⟩
        ⟦ s ⟧ ∙ᴹ ⟦ t ⟧    ≈⟨ congᴹ isUnique⟦ s ⟧ᴹ isUnique⟦ t ⟧ᴹ ⟩
        ⟦ s ⟧ᴹ ∙ᴹ ⟦ t ⟧ᴹ  ∎

  module Corollary (𝓗 𝓚 : η-MagmaHomomorphism)
    where
      open η-MagmaHomomorphism 𝓗 renaming (⟦_⟧ to ⟦_⟧ᴴ)
      open η-MagmaHomomorphism 𝓚 renaming (⟦_⟧ to ⟦_⟧ᴷ)
      open Uniqueness 𝓗 renaming (isUnique⟦_⟧ᴹ to isUnique⟦_⟧ᴴ)
      open Uniqueness 𝓚 renaming (isUnique⟦_⟧ᴹ to isUnique⟦_⟧ᴷ)

      isUnique⟦_⟧ :  ∀ t → ⟦ t ⟧ᴴ ≈ᴹ ⟦ t ⟧ᴷ
      isUnique⟦ t ⟧ = begin ⟦ t ⟧ᴴ ≈⟨ isUnique⟦ t ⟧ᴴ ⟩ ⟦ t ⟧ᴹ ≈˘⟨ isUnique⟦ t ⟧ᴷ ⟩ ⟦ t ⟧ᴷ ∎

------------------------------------------------------------------------
-- Immediate corollary: alg is in fact a MagmaHomomorphism

module _ (𝓜 : Magma m ℓm) where
  open Magma 𝓜 renaming (setoid to setoidᴹ; _≈_ to _≈ᴹ_; isMagma to isMagmaᴹ)
  open FreeMagma setoidᴹ

  algMagmaHomomorphism : MagmaHomomorphism freeMagma 𝓜
  algMagmaHomomorphism = Existence.magmaHomomorphismᴹ
    where open LeftAdjoint 𝓜 (Identity.setoidHomomorphism setoidᴹ)


------------------------------------------------------------------------
-- Action of FreeMagma on Setoid homomorphisms

module FreeMagmaFunctor {𝓐 : Setoid a ℓa} {𝓑 : Setoid b ℓb}
       (𝓗 : SetoidHomomorphism 𝓐 𝓑) where

  open FreeMagma 𝓐 renaming (freeMagma to freeMagmaᴬ)
  open FreeMagma 𝓑 renaming (freeMagma to freeMagmaᴮ
                             ; varSetoidHomomorphism to 𝓥ᴮ)

  mapMagmaHomomorphism : MagmaHomomorphism freeMagmaᴬ freeMagmaᴮ
  mapMagmaHomomorphism = Existence.magmaHomomorphismᴹ
    where open LeftAdjoint freeMagmaᴮ (Compose.setoidHomomorphism 𝓗 𝓥ᴮ)

------------------------------------------------------------------------
-- Naturality of alg

module Naturality {𝓜 : Magma m ℓm} {𝓝 : Magma n ℓn} where
  open Magma 𝓜 using () renaming (setoid to setoidᴹ)
  open Magma 𝓝 using () renaming (_≈_ to _≈ᴺ_; refl to reflᴺ; trans to transᴺ)

  module _ (𝓕 : MagmaHomomorphism 𝓜 𝓝) where
    open MagmaHomomorphism 𝓕 using (⟦_⟧; isMagmaHomomorphism; setoidHomomorphism)
    open FreeMagmaFunctor setoidHomomorphism using (mapMagmaHomomorphism)
    open MagmaHomomorphism mapMagmaHomomorphism
      renaming (⟦_⟧ to map; isMagmaHomomorphism to map-isMagmaHomomorphism; setoidHomomorphism to mapSetoidHomomorphism)
    open FreeMagma setoidᴹ renaming (freeMagma to freeMagmaᴹ)
    open LeftAdjoint 𝓝 setoidHomomorphism
    open MagmaHomomorphism (algMagmaHomomorphism 𝓜)
      renaming (⟦_⟧ to algᴹ; isMagmaHomomorphism to algᴹ-isMagmaHomomorphism)
    open MagmaHomomorphism (algMagmaHomomorphism 𝓝)
      renaming (⟦_⟧ to algᴺ; isMagmaHomomorphism to algᴺ-isMagmaHomomorphism)

    naturality : ∀ t → ⟦ algᴹ t ⟧ ≈ᴺ algᴺ (map t)
    naturality = Corollary.isUnique⟦_⟧ 𝓗 𝓚
      where
        H K : MagmaHomomorphism freeMagmaᴹ 𝓝
        H = record { ⟦_⟧ = ⟦_⟧ ∘ algᴹ
            ; isMagmaHomomorphism = Compose.isMagmaHomomorphism transᴺ algᴹ-isMagmaHomomorphism isMagmaHomomorphism }

        K = record { ⟦_⟧ = algᴺ ∘  map
            ; isMagmaHomomorphism = Compose.isMagmaHomomorphism transᴺ map-isMagmaHomomorphism algᴺ-isMagmaHomomorphism }

        𝓗 𝓚 : η-MagmaHomomorphism
        𝓗 = record { magmaHomomorphism = H ; ⟦_⟧∘var≈ᴹη = λ _ → reflᴺ }
        𝓚 = record { magmaHomomorphism = K ; ⟦_⟧∘var≈ᴹη = λ _ → reflᴺ }


------------------------------------------------------------------------
-- Functoriality of FreeMagmaFunctor.map : by analogy with naturality

module IdentityLaw (𝓐 : Setoid a ℓa) where

  open FreeMagma 𝓐 renaming (varSetoidHomomorphism to 𝓥)
  open Setoid setoid renaming (_≈_ to _≈FA_; refl to reflFA)

  Id : MagmaHomomorphism freeMagma freeMagma
  Id = record
    { ⟦_⟧ = id
    ; isMagmaHomomorphism = Identity.isMagmaHomomorphism rawMagma reflFA}

  open FreeMagmaFunctor (Identity.setoidHomomorphism 𝓐)
  open MagmaHomomorphism mapMagmaHomomorphism renaming (⟦_⟧ to map-Id)

  map-id : ∀ t → map-Id t ≈FA t
  map-id = Corollary.isUnique⟦_⟧ 𝓘ᴬ 𝓘
    where
      open LeftAdjoint freeMagma 𝓥
      𝓘ᴬ 𝓘 : η-MagmaHomomorphism
      𝓘ᴬ = record { magmaHomomorphism = mapMagmaHomomorphism ; ⟦_⟧∘var≈ᴹη = λ _ → reflFA }
      𝓘 = record { magmaHomomorphism = Id ; ⟦_⟧∘var≈ᴹη = λ _ → reflFA }

module CompositionLaw
  {𝓐 : Setoid a ℓa} {𝓑 : Setoid b ℓb} {𝓒 : Setoid c ℓc}
  (𝓗 : SetoidHomomorphism 𝓐 𝓑) (𝓚 : SetoidHomomorphism 𝓑 𝓒) where

  𝓕 : SetoidHomomorphism 𝓐 𝓒
  𝓕 = Compose.setoidHomomorphism 𝓗 𝓚

  open FreeMagma 𝓐 renaming (freeMagma to freeMagmaA)
  open FreeMagma 𝓑 renaming (freeMagma to freeMagmaB)
  open FreeMagma 𝓒 renaming (freeMagma to freeMagmaC
                             ; setoid to setoidFC
                             ; varSetoidHomomorphism to 𝓥)
  open Setoid setoidFC renaming (_≈_ to _≈FC_; refl to reflFC; trans to transFC)
  𝓥∘𝓕 = Compose.setoidHomomorphism 𝓕 𝓥
  open FreeMagmaFunctor 𝓕 renaming (mapMagmaHomomorphism to MapAC)
  open FreeMagmaFunctor 𝓗 renaming (mapMagmaHomomorphism to MapAB)
  open FreeMagmaFunctor 𝓚 renaming (mapMagmaHomomorphism to MapBC)
  open MagmaHomomorphism MapAC renaming (⟦_⟧ to mapAC)
  open MagmaHomomorphism MapAB renaming (⟦_⟧ to mapAB; isMagmaHomomorphism to isMagmaAB)
  open MagmaHomomorphism MapBC renaming (⟦_⟧ to mapBC; isMagmaHomomorphism to isMagmaBC)

  MapBC∘MapAB : MagmaHomomorphism freeMagmaA freeMagmaC
  MapBC∘MapAB = record
    { ⟦_⟧ = mapBC ∘ mapAB
    ; isMagmaHomomorphism = Compose.isMagmaHomomorphism transFC isMagmaAB isMagmaBC}

  map-∘ : ∀ t → mapAC t ≈FC mapBC (mapAB t)
  map-∘ = Corollary.isUnique⟦_⟧ 𝓐𝓒 𝓑𝓒∘𝓐𝓑
    where
      open LeftAdjoint freeMagmaC 𝓥∘𝓕
      𝓐𝓒 𝓑𝓒∘𝓐𝓑 : η-MagmaHomomorphism
      𝓐𝓒 = record { magmaHomomorphism = MapAC ; ⟦_⟧∘var≈ᴹη = λ _ → reflFC }
      𝓑𝓒∘𝓐𝓑 = record { magmaHomomorphism = MapBC∘MapAB ; ⟦_⟧∘var≈ᴹη = λ _ → reflFC }


------------------------------------------------------------------------
-- Monad instance, etc.: TODO
