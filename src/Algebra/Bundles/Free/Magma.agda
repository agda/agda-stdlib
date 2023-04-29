------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of 'pre-free' and 'free' magma
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Bundles.Free.Magma where

open import Algebra.Core
import Algebra.Definitions as Definitions using (Congruent₂)
import Algebra.Structures as Structures using (IsMagma)
open import Algebra.Morphism.Structures using (IsMagmaHomomorphism)
open import Algebra.Bundles using (Magma)
open import Algebra.Bundles.Raw using (RawMagma)
open import Effect.Functor
open import Effect.Monad
open import Function.Base using (id; _∘_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Morphism using (IsRelHomomorphism)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary
  using (Setoid; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary.Morphism.Bundles using (SetoidHomomorphism)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong₂) renaming (refl to ≡-refl; isEquivalence to ≡-isEquivalence)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    a ℓa b ℓb c ℓ m ℓm : Level
    A : Set a
    B : Set b
    C : Set c
    𝓐 : Setoid a ℓa
    𝓑 : Setoid b ℓb

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

  map-id : ∀ (t : Syntax A) → map id t ≡ t
  map-id (var a) = ≡-refl
  map-id (s ∙ t) = cong₂ _∙_ (map-id s) (map-id t)

  map-∘ : (g : A → B) → (f : B → C) → ∀ t → map (f ∘ g) t ≡ (map f ∘ map g) t
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

module EquationalTheory {A : Set a} (R : Rel A ℓ) where

  open Syntax

  infix 4 _≈_

  data _≈_ : Rel (Syntax A) (a ⊔ ℓ)

  open Definitions _≈_

  data _≈_ where

    var : {a b : A} → (R a b) → var a ≈ var b
    _∙_ : Congruent₂ _∙_

  refl : Reflexive R → Reflexive _≈_
  refl r {var _} = var r
  refl r {_ ∙ _} = (refl r) ∙ (refl r)

  sym : Symmetric R → Symmetric _≈_
  sym s (var r)   = var (s r)
  sym s (r₁ ∙ r₂) = sym s r₁ ∙ sym s r₂

  trans : Transitive R → Transitive _≈_
  trans t (var r)   (var s)   = var (t r s)
  trans t (r₁ ∙ r₂) (s₁ ∙ s₂) = trans t r₁ s₁ ∙ trans t r₂ s₂

  preservesEquivalence : IsEquivalence R → IsEquivalence _≈_
  preservesEquivalence isEq = record
    { refl = refl Eq.refl ; sym = sym Eq.sym ; trans = trans Eq.trans }
    where module Eq = IsEquivalence isEq

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

-- reexport some substructure

  open Magma freeMagma public using (rawMagma; Carrier; _≈_)

------------------------------------------------------------------------
-- Semantics: in terms of concrete Magma instances

module _ (𝓜 : Magma m ℓm) where

  open Magma 𝓜
    renaming (Carrier to UM; _≈_ to _≈ᴹ_; _∙_ to _∙ᴹ_
             ; setoid to setoidᴹ; rawMagma to rawMagmaᴹ
             ; isMagma to isMagmaᴹ)
  open ≈-Reasoning setoidᴹ

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
-- Properties of ⟦_⟧_

  module Properties {a ℓa} (𝓐 : Setoid a ℓa) where

    open Setoid 𝓐 renaming (Carrier to UA; _≈_ to _≈ᴬ_)

    open Eval 𝓐 public

    open FreeMagma 𝓐 renaming (Carrier to UFA)

    module Existence {η : UA → UM} (hom-η : IsRelHomomorphism _≈ᴬ_ _≈ᴹ_ η) where

      ⟦_⟧ᴹ : UFA → UM
      ⟦_⟧ᴹ = ⟦_⟧ η

      open Structures _≈ᴹ_
      open IsMagma isMagmaᴹ renaming (∙-cong to congᴹ)
      open IsRelHomomorphism hom-η renaming (cong to cong-η)

      cong-⟦_⟧ : ∀ {s t} → s ≈ t → ⟦ s ⟧ᴹ ≈ᴹ ⟦ t ⟧ᴹ
      cong-⟦ var r ⟧ = cong-η r
      cong-⟦ s ∙ t ⟧ = congᴹ cong-⟦ s ⟧ cong-⟦ t ⟧

      isRelHomomorphism : IsRelHomomorphism _≈_ _≈ᴹ_ ⟦_⟧ᴹ
      isRelHomomorphism = record { cong = cong-⟦_⟧ }

      isMagmaHomomorphism : IsMagmaHomomorphism rawMagma rawMagmaᴹ ⟦_⟧ᴹ
      isMagmaHomomorphism = record { isRelHomomorphism = isRelHomomorphism
                                   ; homo = λ s t → begin ⟦ s ⟧ᴹ ∙ᴹ ⟦ t ⟧ᴹ ∎ }

      unfold-⟦_⟧ᴹ : ∀ t → ⟦ t ⟧ᴹ ≈ᴹ alg (map η t)
      unfold-⟦ var a ⟧ᴹ = begin η a ∎
      unfold-⟦ s ∙ t ⟧ᴹ = congᴹ unfold-⟦ s ⟧ᴹ unfold-⟦ t ⟧ᴹ

      module Uniqueness {h : UFA → UM}
        (isHom : IsMagmaHomomorphism rawMagma rawMagmaᴹ h)
        (h∘var≈ᴹη : ∀ a → h (var a) ≈ᴹ η a) where

        isUnique⟦_⟧ᴹ : ∀ t → h t ≈ᴹ ⟦ t ⟧ᴹ
        isUnique⟦ var a ⟧ᴹ = h∘var≈ᴹη a
        isUnique⟦ s ∙ t ⟧ᴹ = begin
          h (s Syntax.∙ t) ≈⟨ homo s t ⟩
          h s ∙ᴹ h t       ≈⟨ congᴹ isUnique⟦ s ⟧ᴹ isUnique⟦ t ⟧ᴹ ⟩
          ⟦ s ⟧ᴹ ∙ᴹ ⟦ t ⟧ᴹ  ∎ where open IsMagmaHomomorphism isHom

-- immediate corollary

  open FreeMagma setoidᴹ
  open Properties setoidᴹ

  alg-isMagmaHomomorphism : IsMagmaHomomorphism rawMagma rawMagmaᴹ alg
  alg-isMagmaHomomorphism = Existence.isMagmaHomomorphism (record { cong = id })

------------------------------------------------------------------------
-- Functoriality of FreeMagma wrt Setoid homomorphisms

module FreeMagmaFunctor (𝓗 : SetoidHomomorphism 𝓐 𝓑) where

  open Setoid 𝓐  renaming (Carrier to UA; _≈_ to _≈ᴬ_)
  open Setoid 𝓑  renaming (Carrier to UB; _≈_ to _≈ᴮ_)

  open FreeMagma 𝓐
    renaming (freeMagma to freeMagmaᴬ; rawMagma to rawMagmaᴬ
             ; Carrier to UFA; _≈_ to _≈ᵀᴬ_; isMagma to isMagmaᴬ)

  open FreeMagma 𝓑
    renaming (freeMagma to freeMagmaᴮ; rawMagma to rawMagmaᴮ
             ; Carrier to UFB; _≈_ to _≈ᵀᴮ_; isMagma to isMagmaᴮ)

  open Properties freeMagmaᴮ 𝓐

  open SetoidHomomorphism 𝓗

  private
    η : UA → UFB
    η = Syntax.var ∘ ⟦_⟧

    hom-η : IsRelHomomorphism _≈ᴬ_ _≈ᵀᴮ_ η
    hom-η = record { cong = EquationalTheory.var ∘ congᴬᴮ }
      where open IsRelHomomorphism isRelHomomorphism renaming (cong to congᴬᴮ)

  map : IsMagmaHomomorphism rawMagmaᴬ rawMagmaᴮ _
  map = Existence.isMagmaHomomorphism hom-η

------------------------------------------------------------------------
-- Functoriality of FreeMagmaFunctor.map : TODO

------------------------------------------------------------------------
-- Monad instance: TODO

