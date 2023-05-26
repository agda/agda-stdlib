------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of 'pre-free' and 'free' magma
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Free.Magma where

open import Algebra.Core
open import Algebra.Bundles using (Magma)
open import Algebra.Bundles.Raw using (RawMagma)
import Algebra.Definitions as Definitions using (Congruent₂)
import Algebra.Structures as Structures using (IsMagma)
open import Algebra.Morphism.Bundles using (MagmaHomomorphism)
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
  using (_≡_; cong₂; _≗_)
  renaming (refl to ≡-refl; isEquivalence to ≡-isEquivalence)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    ℓ a ℓa b ℓb c ℓc m ℓm n ℓn : Level
    A : Set a
    B : Set b
    C : Set c
    𝓐 : Setoid a ℓa
    𝓑 : Setoid b ℓb
    𝓒 : Setoid c ℓc
    𝓜 : Magma m ℓm
    𝓝 : Magma n ℓn
  

------------------------------------------------------------------------
-- Syntax: 'pre'-free algebra

module Syntax where

  infixl 7 _∙_

  data Syntax (A : Set a) : Set a where

    var : A → Syntax A
    _∙_ : Op₂ (Syntax A)

  _∙-cong_ : ∀ {s s′ t t′ : Syntax A} → s ≡ s′ → t ≡ t′ → s ∙ t ≡ s′ ∙ t′
  _∙-cong_ = cong₂ _∙_

-- Functor instance

  map : (A → B) → Syntax A → Syntax B
  map f (var a) = var (f a)
  map f (s ∙ t) = (map f s) ∙ (map f t)

  map-id : map {A = A} id ≗ id
  map-id (var a) = ≡-refl
  map-id (s ∙ t) = (map-id s) ∙-cong (map-id t)

  map-∘ : (g : A → B) → (f : B → C) → map (f ∘ g) ≗ (map f ∘ map g)
  map-∘ g f (var a) = ≡-refl
  map-∘ g f (s ∙ t) = (map-∘ g f s) ∙-cong (map-∘ g f t)

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

  data _≈_ : Rel (Syntax A) (a ⊔ ℓ) where

    var : {a b : A} → a ≈ᴬ b → var a ≈ var b
    _∙_ : Definitions.Congruent₂ _≈_ _∙_

  refl : Reflexive _≈ᴬ_ → Reflexive _≈_
  refl r {var _} = var r
  refl r {_ ∙ _} = (refl r) ∙ (refl r)

  sym : Symmetric _≈ᴬ_ → Symmetric _≈_
  sym s (var s₀)  = var (s s₀)
  sym s (s₁ ∙ s₂) = sym s s₁ ∙ sym s s₂

  trans : Transitive _≈ᴬ_ → Transitive _≈_
  trans t (var r₀)  (var s₀)  = var (t r₀ s₀)
  trans t (r₁ ∙ r₂) (s₁ ∙ s₂) = trans t r₁ s₁ ∙ trans t r₂ s₂

  isEquivalence : IsEquivalence _≈ᴬ_ → IsEquivalence _≈_
  isEquivalence isEq = record
    { refl = refl Eq.refl
    ; sym = sym Eq.sym
    ; trans = trans Eq.trans
    }
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
  ≈⇒≡ (eq₁ ∙ eq₂) = (≈⇒≡ eq₁) ∙-cong (≈⇒≡ eq₂)

  ≡⇒≈ : ∀ {m n} → m ≡ n → m ≈ n
  ≡⇒≈ ≡-refl = refl ≡-refl

  freeRawMagma : RawMagma a a
  freeRawMagma = record
    { Carrier = Syntax A
    ; _≈_ = _≡_
    ; _∙_ = _∙_
    }

  open Structures {A = Syntax A} _≡_

  isMagma : IsMagma _∙_
  isMagma = record
    { isEquivalence = ≡-isEquivalence
    ; ∙-cong = _∙-cong_
    }

  magma : Magma a a
  magma = record { isMagma = isMagma }


------------------------------------------------------------------------
-- Free algebra on a Setoid

module FreeMagma (𝓐 : Setoid a ℓa) where

  private
    module A = Setoid 𝓐

  open Syntax

  open EquationalTheory A._≈_ public
    hiding (refl; sym; trans)

  open Structures _≈_

  isMagma : IsMagma  _∙_
  isMagma = record
    { isEquivalence = isEquivalence A.isEquivalence
    ; ∙-cong = _∙_
    }

  magma : Magma a (a ⊔ ℓa)
  magma = record { isMagma = isMagma }

-- re-export some substructure

  open Magma magma public using (rawMagma; setoid; Carrier)

  varSetoidHomomorphism : SetoidHomomorphism 𝓐 setoid
  varSetoidHomomorphism = record
    { ⟦_⟧ = var
    ; isRelHomomorphism = varIsRelHomomorphism
    }


------------------------------------------------------------------------
-- Semantics: in terms of concrete Magma instances

module _ (𝓜 : Magma m ℓm) where

  private
    module M = Magma 𝓜
  open Syntax

------------------------------------------------------------------------
-- Eval, as the unique fold ⟦_⟧_ over Syntax

  module Eval (𝓐 : Setoid a ℓa) where

    private
      module A = Setoid 𝓐

    ⟦_⟧_ : Syntax A.Carrier → (A.Carrier → M.Carrier) → M.Carrier
    ⟦ var a ⟧ η = η a
    ⟦ s ∙ t ⟧ η = ⟦ s ⟧ η M.∙ ⟦ t ⟧ η

------------------------------------------------------------------------
-- Any Magma *is* an algebra for the Syntax Functor

  alg : Syntax M.Carrier → M.Carrier
  alg t = ⟦ t ⟧ id where open Eval M.setoid

------------------------------------------------------------------------
-- ⟦_⟧_ defines the (unique) lifting of Setoid homomorphisms to Magma homomorphisms

module LeftAdjoint {𝓐 : Setoid a ℓa} (𝓜 : Magma m ℓm)
       (𝓗 :  SetoidHomomorphism 𝓐 (Magma.setoid 𝓜)) where

  private
    module M = Magma 𝓜
    module A = Setoid 𝓐
    module FA = FreeMagma 𝓐

  open ≈-Reasoning M.setoid

  open Syntax

  open SetoidHomomorphism 𝓗 renaming (⟦_⟧ to η; isRelHomomorphism to hom-η)

  private

    ⟦_⟧η : FA.Carrier → M.Carrier
    ⟦_⟧η = ⟦_⟧ η where open Eval 𝓜 𝓐

  open Structures M._≈_
  open IsMagma M.isMagma renaming (∙-cong to congᴹ)
  open IsRelHomomorphism hom-η renaming (cong to cong-η)

  module Existence where

    unfold-⟦_⟧ : ∀ t → ⟦ t ⟧η M.≈ alg 𝓜 (map η t)
    unfold-⟦ var a ⟧ = begin η a ∎
    unfold-⟦ s ∙ t ⟧ = congᴹ unfold-⟦ s ⟧ unfold-⟦ t ⟧

    cong-⟦_⟧ : ∀ {s t} → s FA.≈ t → ⟦ s ⟧η M.≈ ⟦ t ⟧η
    cong-⟦ FA.var r ⟧ = cong-η r
    cong-⟦ s FA.∙ t ⟧ = congᴹ cong-⟦ s ⟧ cong-⟦ t ⟧

    isRelHomomorphism : IsRelHomomorphism FA._≈_ M._≈_ ⟦_⟧η
    isRelHomomorphism = record { cong = cong-⟦_⟧ }

    setoidHomomorphism : SetoidHomomorphism FA.setoid M.setoid
    setoidHomomorphism = record
      { ⟦_⟧ = ⟦_⟧η
      ; isRelHomomorphism = isRelHomomorphism
      }

    isMagmaHomomorphism : IsMagmaHomomorphism FA.rawMagma M.rawMagma ⟦_⟧η
    isMagmaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = λ s t → M.refl
      }

    magmaHomomorphism : MagmaHomomorphism FA.magma 𝓜
    magmaHomomorphism = record
      { ⟦_⟧ = ⟦_⟧η
      ; isMagmaHomomorphism = isMagmaHomomorphism
      }

  record η-MagmaHomomorphism : Set (suc (a ⊔ m ⊔ ℓa ⊔ ℓm)) where

    field
      magmaHomomorphism : MagmaHomomorphism FA.magma 𝓜
    open MagmaHomomorphism magmaHomomorphism public renaming (homo to ⟦⟧-homo)
    field
      ⟦_⟧∘var≈η : ∀ a → ⟦ var a ⟧ M.≈ η a

  ⟦⟧-η-MagmaHomomorphism : η-MagmaHomomorphism
  ⟦⟧-η-MagmaHomomorphism = record
    { magmaHomomorphism = Existence.magmaHomomorphism
    ; ⟦_⟧∘var≈η = Existence.unfold-⟦_⟧ ∘ var
    }

  module Uniqueness (η-magmaHomomorphism : η-MagmaHomomorphism) where

    open η-MagmaHomomorphism η-magmaHomomorphism

    isUnique⟦_⟧ : ∀ t → ⟦ t ⟧ M.≈ ⟦ t ⟧η
    isUnique⟦ var a ⟧ = ⟦ a ⟧∘var≈η
    isUnique⟦ s ∙ t ⟧ = begin
      ⟦ s Syntax.∙ t ⟧  ≈⟨ ⟦⟧-homo s t ⟩
      ⟦ s ⟧ M.∙ ⟦ t ⟧   ≈⟨ congᴹ isUnique⟦ s ⟧ isUnique⟦ t ⟧ ⟩
      ⟦ s ⟧η M.∙ ⟦ t ⟧η  ∎

  module Corollary (𝓗 𝓚 : η-MagmaHomomorphism) where
  
    open η-MagmaHomomorphism 𝓗 using () renaming (⟦_⟧ to ⟦_⟧ᴴ)
    open η-MagmaHomomorphism 𝓚 using () renaming (⟦_⟧ to ⟦_⟧ᴷ)
    open Uniqueness 𝓗 renaming (isUnique⟦_⟧ to isUnique⟦_⟧ᴴ)
    open Uniqueness 𝓚 renaming (isUnique⟦_⟧ to isUnique⟦_⟧ᴷ)

    isUnique⟦_⟧ :  ∀ t → ⟦ t ⟧ᴴ M.≈ ⟦ t ⟧ᴷ
    isUnique⟦ t ⟧ = begin ⟦ t ⟧ᴴ ≈⟨ isUnique⟦ t ⟧ᴴ ⟩ ⟦ t ⟧η ≈˘⟨ isUnique⟦ t ⟧ᴷ ⟩ ⟦ t ⟧ᴷ ∎

------------------------------------------------------------------------
-- Immediate corollary: alg is in fact a MagmaHomomorphism

module _ (𝓜 : Magma m ℓm) where

  private
    module M = Magma 𝓜

  algMagmaHomomorphism : MagmaHomomorphism (FreeMagma.magma M.setoid) 𝓜
  algMagmaHomomorphism = Existence.magmaHomomorphism
    where open LeftAdjoint 𝓜 (Identity.setoidHomomorphism M.setoid)


------------------------------------------------------------------------
-- Action of FreeMagma on Setoid homomorphisms

module FreeMagmaFunctor (𝓗 : SetoidHomomorphism 𝓐 𝓑) where
  private
    module FA = FreeMagma 𝓐
    module FB = FreeMagma 𝓑
  
  magmaHomomorphism : MagmaHomomorphism FA.magma FB.magma
  magmaHomomorphism = Existence.magmaHomomorphism
    where open LeftAdjoint FB.magma (Compose.setoidHomomorphism 𝓗 FB.varSetoidHomomorphism)

------------------------------------------------------------------------
-- Naturality of alg

module Naturality (𝓕 : MagmaHomomorphism 𝓜 𝓝) where

  private 
    module M = Magma 𝓜
    module N = Magma 𝓝
    module F = MagmaHomomorphism 𝓕
    Free𝓕 = FreeMagmaFunctor.magmaHomomorphism (F.setoidHomomorphism)
    module AlgM = MagmaHomomorphism (algMagmaHomomorphism 𝓜)
    module AlgN = MagmaHomomorphism (algMagmaHomomorphism 𝓝)
    
    module Map = MagmaHomomorphism Free𝓕

  naturality : ∀ t → F.⟦ AlgM.⟦ t ⟧ ⟧ N.≈ AlgN.⟦ Map.⟦ t ⟧ ⟧
  naturality = Corollary.isUnique⟦_⟧ 𝓗 𝓚
    where
      open LeftAdjoint 𝓝 F.setoidHomomorphism
      𝓗 𝓚 : η-MagmaHomomorphism
      𝓗 = record
        { magmaHomomorphism = Compose.magmaHomomorphism (algMagmaHomomorphism 𝓜) 𝓕
        ; ⟦_⟧∘var≈η = λ _ → N.refl
        }
      𝓚 = record
        { magmaHomomorphism = Compose.magmaHomomorphism Free𝓕 (algMagmaHomomorphism 𝓝)
        ; ⟦_⟧∘var≈η = λ _ → N.refl
        }



------------------------------------------------------------------------
-- Functoriality of FreeMagmaFunctor.map : by analogy with naturality

module IdentityLaw (𝓐 : Setoid a ℓa) where

  private
    module A = Setoid 𝓐
    module FA = FreeMagma 𝓐
    module UFA = Setoid FA.setoid
    module IA = FreeMagmaFunctor (Identity.setoidHomomorphism 𝓐)
    module MapId = MagmaHomomorphism IA.magmaHomomorphism

  map-id : ∀ t → MapId.⟦ t ⟧ UFA.≈ t
  map-id = Corollary.isUnique⟦_⟧ 𝓘ᴬ 𝓘
    where
      open LeftAdjoint FA.magma FA.varSetoidHomomorphism
      𝓘ᴬ 𝓘 : η-MagmaHomomorphism
      𝓘ᴬ = record
            { magmaHomomorphism = IA.magmaHomomorphism
            ; ⟦_⟧∘var≈η = λ _ → UFA.refl
            }
      𝓘 = record
           { magmaHomomorphism = Identity.magmaHomomorphism _
           ; ⟦_⟧∘var≈η = λ _ → UFA.refl
           }

module CompositionLaw (𝓗 : SetoidHomomorphism 𝓐 𝓑) (𝓚 : SetoidHomomorphism 𝓑 𝓒) where

  private
    module FA = FreeMagma 𝓐
    module FB = FreeMagma 𝓑
    module FC = FreeMagma 𝓒
    module UFC = Setoid FC.setoid
    Free𝓗 = FreeMagmaFunctor.magmaHomomorphism 𝓗
    Free𝓚 = FreeMagmaFunctor.magmaHomomorphism 𝓚
    module MapAB = MagmaHomomorphism Free𝓗
    module MapBC = MagmaHomomorphism Free𝓚
    𝓕 : SetoidHomomorphism 𝓐 𝓒
    𝓕 = Compose.setoidHomomorphism 𝓗 𝓚
    Free𝓕 = FreeMagmaFunctor.magmaHomomorphism 𝓕
    module MapAC = MagmaHomomorphism Free𝓕

  map-∘ : ∀ t → MapAC.⟦ t ⟧ UFC.≈ MapBC.⟦ MapAB.⟦ t ⟧ ⟧
  map-∘ = Corollary.isUnique⟦_⟧ 𝓐𝓒 𝓑𝓒∘𝓐𝓑
    where
      open LeftAdjoint FC.magma (Compose.setoidHomomorphism 𝓕 FC.varSetoidHomomorphism)
      𝓐𝓒 𝓑𝓒∘𝓐𝓑 : η-MagmaHomomorphism
      𝓐𝓒 = record
        { magmaHomomorphism = Free𝓕
        ; ⟦_⟧∘var≈η = λ _ → UFC.refl
        }
      𝓑𝓒∘𝓐𝓑 = record
        { magmaHomomorphism = Compose.magmaHomomorphism Free𝓗 Free𝓚
        ; ⟦_⟧∘var≈η = λ _ → UFC.refl
        }


------------------------------------------------------------------------
-- Monad instance, etc.: TODO

