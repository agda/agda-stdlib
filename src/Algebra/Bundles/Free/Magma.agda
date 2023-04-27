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
open import Algebra.Bundles using (Magma)
open import Algebra.Bundles.Raw using (RawMagma)
open import Relation.Binary.Core using (Rel)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary using (Setoid; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong₂) renaming (refl to ≡refl; isEquivalence to ≡isEquivalence)

------------------------------------------------------------------------
-- 'pre'-free algebra

infixl 7 _∙_

data PreFreeMagma {c} (A : Set c) : Set c where

  var : A → PreFreeMagma A
  _∙_ : Op₂ (PreFreeMagma A)

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

  refl : (Reflexive R) → Reflexive _≈R_
  refl r {var _} = var r
  refl r {_ ∙ _} = (refl r) ∙ (refl r)

  sym : (Symmetric R) → Symmetric _≈R_
  sym s (var r)   = var (s r)
  sym s (r₁ ∙ r₂) = sym s r₁ ∙ sym s r₂

  trans : (Transitive R) → Transitive _≈R_
  trans t (var r)   (var s)   = var (t r s)
  trans t (r₁ ∙ r₂) (s₁ ∙ s₂) = trans t r₁ s₁ ∙ trans t r₂ s₂

  preservesEquivalence : IsEquivalence R → IsEquivalence _≈R_
  preservesEquivalence eq = record { refl = refl r ; sym = sym s ; trans = trans t }
    where open IsEquivalence eq renaming (refl to r; sym to s; trans to t) 

------------------------------------------------------------------------
-- Free algebra on a Setoid

module FreeMagmaOn {c ℓ} (S : Setoid c ℓ) where

  open Setoid S renaming (Carrier to A; isEquivalence to isEq)

  open PreFreeTheory _≈_

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
  ≈⇒≡ (var ≡refl) = ≡refl
  ≈⇒≡ (eq₁ ∙ eq₂) = cong₂ _∙_ (≈⇒≡ eq₁) (≈⇒≡ eq₂)

  refl : Reflexive _≈_
  refl {var _} = var ≡refl
  refl {_ ∙ _} = refl ∙ refl

  ≡⇒≈ : ∀ {m n} → m ≡ n → m ≈ n
  ≡⇒≈ ≡refl = refl

  rawFreeMagma : RawMagma c c
  rawFreeMagma = record { Carrier = Carrier ; _≈_ = _≡_ ; _∙_ = _∙_ }

  open Strs {A = Carrier} _≡_

  isMagma : IsMagma _∙_
  isMagma = record { isEquivalence = ≡isEquivalence ; ∙-cong = cong₂ _∙_ }
  
  freeMagma : Magma c c
  freeMagma = record { RawMagma rawFreeMagma ; isMagma = isMagma }

