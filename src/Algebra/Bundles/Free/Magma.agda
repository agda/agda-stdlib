------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of 'pre-free' and 'free' magma
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Bundles.Free.Magma where

open import Algebra.Core
import Algebra.Definitions as Defs using (Congruent₂)
import Algebra.Structures as Strs using (IsMagma)
open import Algebra.Morphism.Structures using (IsMagmaHomomorphism)
open import Algebra.Bundles using (Magma)
open import Algebra.Bundles.Raw using (RawMagma)
open import Function.Base using (id; _∘_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Morphism using (IsRelHomomorphism)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary
  using (Setoid; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong₂) renaming (refl to ≡-refl; isEquivalence to ≡-isEquivalence)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning


------------------------------------------------------------------------
-- 'pre'-free algebra

infixl 7 _∙_

data PreFreeMagma {a} (A : Set a) : Set a where

  var : A → PreFreeMagma A
  _∙_ : Op₂ (PreFreeMagma A)

module _ {a b} {A : Set a} {B : Set b} where

  map : (A → B) → PreFreeMagma A → PreFreeMagma B
  map f (var a) = var (f a)
  map f (s ∙ t) = (map f s) ∙ (map f t)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

  map-id : ∀ (t : PreFreeMagma A) → map id t ≡ t
  map-id (var a) = ≡-refl
  map-id (s ∙ t) = cong₂ _∙_ (map-id s) (map-id t)

  map-∘ : (g : A → B) → (f : B → C) → ∀ t → map (f ∘ g) t ≡ (map f ∘ map g) t
  map-∘ g f (var a) = ≡-refl
  map-∘ g f (s ∙ t) = cong₂ _∙_ (map-∘ g f s) (map-∘ g f t)

------------------------------------------------------------------------
-- Functor, RawMonad instance: TODO

------------------------------------------------------------------------
-- parametrised 'equational' theory over the 'pre'-free algebra

module PreFreeTheory {c ℓ} {A : Set c} (R : Rel A ℓ) where

  data PreFreeMagmaTheory : Rel (PreFreeMagma A) (c ⊔ ℓ)

  open Defs PreFreeMagmaTheory

  data PreFreeMagmaTheory where

    var : ∀ {a b} → (R a b) → PreFreeMagmaTheory (var a) (var b)
    _∙_ : Congruent₂ _∙_

PreFreeTheorySyntax : ∀ {c ℓ} {A : Set c} (R : Rel A ℓ) → Rel (PreFreeMagma A) (c ⊔ ℓ)
PreFreeTheorySyntax R = PreFreeMagmaTheory where open PreFreeTheory R

syntax PreFreeTheorySyntax R m n = m ≈[ R ] n

module PreservesEquivalence {c ℓ} {A : Set c} (R : Rel A ℓ) where

  open PreFreeTheory R

  _≈R_ = λ m n → m ≈[ R ] n

  refl : Reflexive R → Reflexive _≈R_
  refl r {var _} = var r
  refl r {_ ∙ _} = (refl r) ∙ (refl r)

  sym : Symmetric R → Symmetric _≈R_
  sym s (var r)   = var (s r)
  sym s (r₁ ∙ r₂) = sym s r₁ ∙ sym s r₂

  trans : Transitive R → Transitive _≈R_
  trans t (var r)   (var s)   = var (t r s)
  trans t (r₁ ∙ r₂) (s₁ ∙ s₂) = trans t r₁ s₁ ∙ trans t r₂ s₂

  preservesEquivalence : IsEquivalence R → IsEquivalence _≈R_
  preservesEquivalence isEq = record { refl = refl r ; sym = sym s ; trans = trans t }
    where open IsEquivalence isEq renaming (refl to r; sym to s; trans to t)

------------------------------------------------------------------------
-- Free algebra on a Setoid

module FreeMagmaOn {c ℓ} (S : Setoid c ℓ) where

  open Setoid S renaming (Carrier to A; isEquivalence to isEq)

  open PreFreeTheory _≈_ public

  open PreservesEquivalence _≈_

  open Strs _≈R_

  isMagma : IsMagma  _∙_
  isMagma = record { isEquivalence = preservesEquivalence isEq ; ∙-cong = _∙_ }

  freeMagma : Magma c (c ⊔ ℓ)
  freeMagma = record { Carrier = PreFreeMagma A; _≈_ = _≈R_ ; _∙_ = _∙_ ; isMagma = isMagma }

{- in the propositional case, we can immediately define the following
   but how best to organise this under the Algebra.Bundles.Free hierarchy? -}

------------------------------------------------------------------------
-- Free algebra on a Set

module FreeMagma {c} (A : Set c) where

  private Carrier = PreFreeMagma A

  _≈_ : Rel Carrier c
  m ≈ n = m ≈[ _≡_ ] n

  open PreFreeTheory {A = A} _≡_

  ≈⇒≡ : ∀ {m n} → m ≈ n → m ≡ n
  ≈⇒≡ (var ≡-refl) = ≡-refl
  ≈⇒≡ (eq₁ ∙ eq₂) = cong₂ _∙_ (≈⇒≡ eq₁) (≈⇒≡ eq₂)

  refl : Reflexive _≈_
  refl {var _} = var ≡-refl
  refl {_ ∙ _} = refl ∙ refl

  ≡⇒≈ : ∀ {m n} → m ≡ n → m ≈ n
  ≡⇒≈ ≡-refl = refl

  rawFreeMagma : RawMagma c c
  rawFreeMagma = record { Carrier = Carrier ; _≈_ = _≡_ ; _∙_ = _∙_ }

  open Strs {A = Carrier} _≡_

  isMagma : IsMagma _∙_
  isMagma = record { isEquivalence = ≡-isEquivalence ; ∙-cong = cong₂ _∙_ }

  freeMagma : Magma c c
  freeMagma = record { RawMagma rawFreeMagma ; isMagma = isMagma }

------------------------------------------------------------------------
-- Eval, as the unique fold ⟦_⟧_ over PreFreeMagma A

module Eval {a ℓa m ℓm} (𝓐 : Setoid a ℓa) (𝓜 : Magma m ℓm) where

  open Setoid 𝓐 renaming (Carrier to A)

  open Magma 𝓜 renaming (Carrier to M; _∙_ to _∙ᴹ_)

  ⟦_⟧_ : PreFreeMagma A → (A → M) → M
  ⟦ var a ⟧ η = η a
  ⟦ s ∙ t ⟧ η = ⟦ s ⟧ η ∙ᴹ ⟦ t ⟧ η

------------------------------------------------------------------------
-- Any Magma *is* an algebra for the PreFreeMagma Functor

module Alg {m ℓm} (𝓜 : Magma m ℓm) where

  open Magma 𝓜 renaming (setoid to setoidᴹ; Carrier to M)

  open Eval setoidᴹ 𝓜

  algᴹ : PreFreeMagma M → M
  algᴹ t = ⟦ t ⟧ id

------------------------------------------------------------------------
-- Properties of ⟦_⟧_

module Properties {a ℓa m ℓm} (𝓐 : Setoid a ℓa) (𝓜 : Magma m ℓm) where

  open Setoid 𝓐 renaming (Carrier to A; _≈_ to _≈ᴬ_)

  open Magma 𝓜
    renaming (Carrier to M; _≈_ to _≈ᴹ_; _∙_ to _∙ᴹ_
             ; setoid to setoidᴹ; rawMagma to rawMagmaᴹ; refl to reflᴹ
             ; isMagma to isMagmaᴹ)

  open Eval 𝓐 𝓜

  open Alg 𝓜

  open FreeMagmaOn 𝓐

  open Magma freeMagma renaming (rawMagma to rawMagmaᴬ; Carrier to FA)

  module _ {η : A → M} (hom-η : IsRelHomomorphism _≈ᴬ_ _≈ᴹ_ η) where

    ⟦_⟧ᴹ : FA → M
    ⟦_⟧ᴹ = ⟦_⟧ η

    open Strs _≈ᴹ_
    open IsMagma isMagmaᴹ renaming (∙-cong to congᴹ)
    open IsRelHomomorphism hom-η renaming (cong to cong-η)

    cong : ∀ {s t} → s ≈ t → ⟦ s ⟧ᴹ ≈ᴹ ⟦ t ⟧ᴹ
    cong (var r) = cong-η r
    cong (s ∙ t) = congᴹ (cong s) (cong t)

    isRelHomomorphism : IsRelHomomorphism _≈_ _≈ᴹ_ ⟦_⟧ᴹ
    isRelHomomorphism = record { cong = cong }

    isMagmaHomomorphism : IsMagmaHomomorphism rawMagmaᴬ rawMagmaᴹ ⟦_⟧ᴹ
    isMagmaHomomorphism = record { isRelHomomorphism = isRelHomomorphism
                                 ; homo = λ _ _ → reflᴹ
                                 }

    unfold-⟦_⟧ᴹ : ∀ t → ⟦ t ⟧ᴹ ≈ᴹ algᴹ (map η t)
    unfold-⟦ var a ⟧ᴹ = reflᴹ
    unfold-⟦ s ∙ t ⟧ᴹ = congᴹ unfold-⟦ s ⟧ᴹ unfold-⟦ t ⟧ᴹ

    module _ {h : FA → M} (isHom : IsMagmaHomomorphism rawMagmaᴬ rawMagmaᴹ h)
             (h∘var≈ᴹη : ∀ a → h (var a) ≈ᴹ η a) where

      open IsMagmaHomomorphism isHom

      open ≈-Reasoning setoidᴹ

      isUnique⟦_⟧ᴹ : ∀ t → h t ≈ᴹ ⟦ t ⟧ᴹ
      isUnique⟦ var a ⟧ᴹ = h∘var≈ᴹη a
      isUnique⟦ s ∙ t ⟧ᴹ = begin
        h (s PreFreeMagma.∙ t) ≈⟨ homo s t ⟩
        (h s) ∙ᴹ (h t)         ≈⟨ congᴹ isUnique⟦ s ⟧ᴹ isUnique⟦ t ⟧ᴹ ⟩
        ⟦ s ⟧ᴹ ∙ᴹ (⟦ t ⟧ᴹ)   ∎

------------------------------------------------------------------------
-- Monad instance: TODO

