------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Algebra where

open import Algebra
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Bool.Base using (true; false)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
import Data.Empty as Empty
open import Data.Product
open import Data.Product.Properties
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (id; _∘′_; _∘_; flip; const)
open import Function.Bundles using (_↔_; Inverse; mk↔)
import Function.Construct.Identity as Identity
open import Function.Properties.Inverse using (↔-isEquivalence)
open import Level using (Level; suc)
import Function.Definitions as FuncDef
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Relation.Nullary.Decidable using (True)
import Relation.Nullary.Indexed as Ind
open import Relation.Nullary using (Dec; ¬_; _because_; ofⁿ)
open import Relation.Nullary.Reflects using (invert)

------------------------------------------------------------------------

private
  variable
    a b c d p : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

  -- The module is needed because we need to pass `A` and `B` to `FuncDef`
  module _ {A : Set a} {B : Set b} where
    open FuncDef {A = A} {B} _≡_ _≡_

    -- mk↔ is a bit of a pain to use because here f and f⁻¹ need to always
    -- be specified.
    inverse : (f : A → B) (f⁻¹ : B → A) → Inverseˡ f f⁻¹ → Inverseʳ f f⁻¹ → A ↔ B
    inverse f f⁻¹ left right = mk↔ {f = f} {f⁻¹} (left , right)

------------------------------------------------------------------------
-- Properties of Σ

-- Σ is associative
Σ-assoc : {B : A → Set b} {C : (a : A) → B a → Set c} →
          Σ (Σ A B) (uncurry C) ↔ Σ A (λ a → Σ (B a) (C a))
Σ-assoc = inverse assocʳ assocˡ cong′ cong′

-- Σ is associative, alternate formulation
Σ-assoc-alt : {B : A → Set b} {C : Σ A B → Set c} →
          Σ (Σ A B) C ↔ Σ A (λ a → Σ (B a) (curry C a))
Σ-assoc-alt = inverse assocʳ-curried assocˡ-curried cong′ cong′

------------------------------------------------------------------------
-- Algebraic properties

-- × is associative
×-assoc : ∀ ℓ → Associative {ℓ = ℓ} _↔_ _×_
×-assoc ℓ _ _ _ = inverse assocʳ′ assocˡ′ cong′ cong′

-- × is commutative.
-- (we don't use Commutative because it isn't polymorphic enough)
×-comm : (A : Set a) (B : Set b) → (A × B) ↔ (B × A)
×-comm _ _ = inverse swap swap swap-involutive swap-involutive

-- ⊤ is the identity for ×
×-identityˡ : ∀ ℓ → LeftIdentity {ℓ = ℓ} _↔_ ⊤ _×_
×-identityˡ _ _ = inverse proj₂ (tt ,_) cong′ cong′

×-identityʳ : ∀ ℓ → RightIdentity {ℓ = ℓ} _↔_ ⊤ _×_
×-identityʳ _ _ = inverse proj₁ (_, tt) cong′ cong′

×-identity : ∀ ℓ → Identity _↔_ ⊤ _×_
×-identity ℓ = ×-identityˡ ℓ , ×-identityʳ ℓ

-- ⊥ is the zero for ×
×-zeroˡ : ∀ ℓ → LeftZero {ℓ = ℓ} _↔_ ⊥ _×_
×-zeroˡ ℓ A = inverse proj₁ ⊥-elim ⊥-elim λ ()

×-zeroʳ : ∀ ℓ → RightZero {ℓ = ℓ} _↔_ ⊥ _×_
×-zeroʳ ℓ A = inverse proj₂ ⊥-elim ⊥-elim λ ()

×-zero : ∀ ℓ → Zero _↔_ ⊥ _×_
×-zero ℓ  = ×-zeroˡ ℓ , ×-zeroʳ ℓ

-- × is a congruence
×-cong : A ↔ B → C ↔ D → (A × C) ↔ (B × D)
×-cong i j = inverse (map I.f J.f) (map I.f⁻¹ J.f⁻¹)
  (λ {(a , b) → cong₂ _,_ (I.inverseˡ a) (J.inverseˡ b)})
  (λ {(a , b) → cong₂ _,_ (I.inverseʳ a) (J.inverseʳ b)})
  where module I = Inverse i; module J = Inverse j

------------------------------------------------------------------------
-- Algebraic structures

module _ (ℓ : Level) where

  ×-isMagma : IsMagma {ℓ = ℓ} _↔_ _×_
  ×-isMagma = record
    { isEquivalence = ↔-isEquivalence
    ; ∙-cong        = ×-cong
    }

  ×-isSemigroup : IsSemigroup _↔_ _×_
  ×-isSemigroup = record
    { isMagma = ×-isMagma
    ; assoc   = λ _ _ _ → Σ-assoc
    }

  ×-isMonoid : IsMonoid _↔_ _×_ ⊤
  ×-isMonoid = record
    { isSemigroup = ×-isSemigroup
    ; identity    = ×-identityˡ ℓ , ×-identityʳ ℓ
    }

  ×-isCommutativeMonoid : IsCommutativeMonoid _↔_ _×_ ⊤
  ×-isCommutativeMonoid = record
    { isMonoid = ×-isMonoid
    ; comm     = ×-comm
    }

------------------------------------------------------------------------
-- Algebraic bundles

  ×-magma : Magma (suc ℓ) ℓ
  ×-magma = record
    { isMagma = ×-isMagma
    }

  ×-semigroup : Semigroup (suc ℓ) ℓ
  ×-semigroup = record
    { isSemigroup = ×-isSemigroup
    }

  ×-monoid : Monoid (suc ℓ) ℓ
  ×-monoid = record
    { isMonoid = ×-isMonoid
    }

  ×-commutativeMonoid : CommutativeMonoid (suc ℓ) ℓ
  ×-commutativeMonoid = record
    { isCommutativeMonoid = ×-isCommutativeMonoid
    }

------------------------------------------------------------------------
-- Some reordering lemmas

ΠΠ↔ΠΠ : (P : A → B → Set p) → ((x : A) (y : B) → P x y) ↔ ((y : B) (x : A) → P x y)
ΠΠ↔ΠΠ _ = inverse flip flip cong′ cong′

∃∃↔∃∃ : (P : A → B → Set p) → (∃₂ λ x y → P x y) ↔ (∃₂ λ y x → P x y)
∃∃↔∃∃ P = inverse to from cong′ cong′
  where
  to : (∃₂ λ x y → P x y) → (∃₂ λ y x → P x y)
  to (x , y , Pxy) = (y , x , Pxy)

  from : (∃₂ λ y x → P x y) → (∃₂ λ x y → P x y)
  from (y , x , Pxy) = (x , y , Pxy)

------------------------------------------------------------------------
-- Implicit and explicit function spaces are isomorphic

Π↔Π : {B : A → Set b} → ((x : A) → B x) ↔ ({x : A} → B x)
Π↔Π = inverse (λ f {x} → f x) (λ f _ → f) cong′ cong′

------------------------------------------------------------------------
-- → preserves ↔ (assuming extensionality)

→-cong : {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  Extensionality a c → Extensionality b d →
  A ↔ B → C ↔ D → (A → C) ↔ (B → D)
→-cong extAC extBD A↔B C↔D = inverse (λ h → C↔D.f ∘ h ∘ A↔B.f⁻¹ ) (λ g → C↔D.f⁻¹ ∘ g ∘ A↔B.f)
  (λ h → extBD λ x → begin
    C↔D.f (C↔D.f⁻¹ (h (A↔B.f (A↔B.f⁻¹ x)))) ≡⟨ C↔D.inverseˡ _ ⟩
    h (A↔B.f (A↔B.f⁻¹ x))                   ≡⟨ cong h (A↔B.inverseˡ x) ⟩
    h x                                     ∎)
  -- same but with inverseʳ
  λ h → extAC  λ x → trans (C↔D.inverseʳ _) (cong h (A↔B.inverseʳ x))
  where
  module A↔B = Inverse A↔B
  module C↔D = Inverse C↔D
  open ≡-Reasoning

------------------------------------------------------------------------
-- ¬_ preserves ↔ (assuming extensionality)

¬-cong : ∀ {c} → Extensionality a c → Extensionality b c →
         {A : Set a} {B : Set b} →
         A ↔ B → (Ind.¬ c A) ↔ (Ind.¬ c B)
¬-cong extA extB A≈B = →-cong extA extB A≈B (Identity.id-↔ ⊥)

------------------------------------------------------------------------
-- A lemma relating True dec and P, where dec : Dec P

True↔ : ∀ {p} {P : Set p}
        (dec : Dec P) → ((p₁ p₂ : P) → p₁ ≡ p₂) → True dec ↔ P
True↔ ( true because  [p]) irr =
  inverse (λ _ → invert [p]) _ (λ pp → irr (invert [p]) pp) cong′
True↔ (false because ofⁿ ¬p) _ =
  inverse (λ ()) (invert (ofⁿ ¬p)) (Empty.⊥-elim ∘ ¬p) λ ()

------------------------------------------------------------------------
-- Equality between pairs can be expressed as a pair of equalities

Σ-≡,≡↔≡ : {B : A → Set b} {p₁ p₂ : Σ A B} →
          (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
             subst B p (proj₂ p₁) ≡ proj₂ p₂) ↔
          (p₁ ≡ p₂)
Σ-≡,≡↔≡ {A = A} {B = B} = inverse to from right-inverse-of left-inverse-of
  where
  to : {p₁ p₂ : Σ A B} →
       Σ (proj₁ p₁ ≡ proj₁ p₂)
         (λ p → subst B p (proj₂ p₁) ≡ proj₂ p₂) →
       p₁ ≡ p₂
  to (refl , refl) = refl

  from : {p₁ p₂ : Σ A B} →
         p₁ ≡ p₂ →
         Σ (proj₁ p₁ ≡ proj₁ p₂)
           (λ p → subst B p (proj₂ p₁) ≡ proj₂ p₂)
  from refl = refl , refl

  left-inverse-of : {p₁ p₂ : Σ A B}
                    (p : Σ (proj₁ p₁ ≡ proj₁ p₂)
                           (λ x → subst B x (proj₂ p₁) ≡ proj₂ p₂)) →
                    from (to p) ≡ p
  left-inverse-of (refl , refl) = refl

  right-inverse-of : {p₁ p₂ : Σ A B} (p : p₁ ≡ p₂) → to (from p) ≡ p
  right-inverse-of refl = refl

-- the non-dependent case. Proofs are exactly as above, and straightforward.
×-≡,≡↔≡ : ∀ {a b} {A : Set a} {B : Set b} {p₁ p₂ : A × B} →
          (proj₁ p₁ ≡ proj₁ p₂ × proj₂ p₁ ≡ proj₂ p₂) ↔ p₁ ≡ p₂
×-≡,≡↔≡ {A = A} {B} =
  inverse (λ {(refl , refl) → refl}) (λ { refl → refl , refl})
    (λ { refl → refl}) λ {(refl , refl) → refl}
