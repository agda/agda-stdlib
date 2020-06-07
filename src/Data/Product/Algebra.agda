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
open import Level using (Level)
import Function.Definitions as FuncDef
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; isEquivalence; cong; cong₂; trans; subst; module ≡-Reasoning)
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

private
  -- convenient abbreviations
  irefl : {f : A → B} (x : A) → f x ≡ f x
  irefl _ = refl

------------------------------------------------------------------------
-- Properties of ×

-- × is associative

×-assoc : ∀ ℓ → Associative {ℓ = ℓ} _↔_ _×_
×-assoc ℓ _ _ _ = inverse assocʳ′ assocˡ′ irefl irefl

-- × is commutative.
-- We don't use Commutative because it isn't polymorphic enough.

×-comm : (A : Set a) (B : Set b) → (A × B) ↔ (B × A)
×-comm _ _ = inverse swap swap swap-involutive swap-involutive

-- ⊤ is both left and right identity for ×
×-identityˡ : ∀ ℓ → LeftIdentity _↔_ (⊤ {ℓ}) _×_
×-identityˡ _ _ = inverse proj₂ (tt ,_) irefl irefl

×-identityʳ : ∀ ℓ → RightIdentity _↔_ (⊤ {ℓ}) _×_
×-identityʳ _ _ = inverse proj₁ (_, tt) irefl irefl

×-identity : ∀ ℓ → Identity _↔_ (⊤) _×_
×-identity ℓ = ×-identityˡ ℓ , ×-identityʳ ℓ

-- × has ⊥ has its zero

×-zeroˡ : ∀ ℓ → LeftZero _↔_ (⊥ {ℓ}) _×_
×-zeroˡ ℓ A = inverse proj₁ ⊥-elim ⊥-elim λ ()

×-zeroʳ : ∀ ℓ → RightZero _↔_ (⊥ {ℓ}) _×_
×-zeroʳ ℓ A = inverse proj₂ ⊥-elim ⊥-elim λ ()

×-zero : ∀ ℓ → Zero _↔_ (⊥) _×_
×-zero ℓ  = ×-zeroˡ ℓ , ×-zeroʳ ℓ

-- × is a congruence
infix 4 _×-cong_

_×-cong_ : A ↔ B → C ↔ D → (A × C) ↔ (B × D)
i ×-cong j = inverse (map I.f J.f) (map I.f⁻¹ J.f⁻¹)
  (λ {(a , b) → cong₂ _,_ (I.inverseˡ a) (J.inverseˡ b) })
  λ {(a , b) → cong₂ _,_ (I.inverseʳ a) (J.inverseʳ b)}
  where module I = Inverse i
        module J = Inverse j

------------------------------------------------------------------------
-- Properties of Σ

-- Σ is associative
Σ-assoc : {B : A → Set b} {C : (a : A) → B a → Set c} →
          Σ (Σ A B) (uncurry C) ↔ Σ A (λ a → Σ (B a) (C a))
Σ-assoc = inverse assocʳ assocˡ irefl irefl

-- Σ is associative, alternate formulation
Σ-assoc-alt : {B : A → Set b} {C : Σ A B → Set c} →
          Σ (Σ A B) C ↔ Σ A (λ a → Σ (B a) (curry C a))
Σ-assoc-alt = inverse assocʳ-alt assocˡ-alt irefl irefl

------------------------------------------------------------------------
-- Some reordering lemmas

ΠΠ↔ΠΠ : (P : A → B → Set p) → ((x : A) (y : B) → P x y) ↔ ((y : B) (x : A) → P x y)
ΠΠ↔ΠΠ _ = inverse flip flip irefl irefl

∃∃↔∃∃ : (P : A → B → Set p) → (∃₂ λ x y → P x y) ↔ (∃₂ λ y x → P x y)
∃∃↔∃∃ P = inverse to from irefl irefl
  where
  to : (∃₂ λ x y → P x y) → (∃₂ λ y x → P x y)
  to (x , y , Pxy) = (y , x , Pxy)

  from : (∃₂ λ y x → P x y) → (∃₂ λ x y → P x y)
  from (y , x , Pxy) = (x , y , Pxy)

------------------------------------------------------------------------
-- Implicit and explicit function spaces are isomorphic

Π↔Π : {B : A → Set b} → ((x : A) → B x) ↔ ({x : A} → B x)
Π↔Π = inverse (λ f {x} → f x) (λ f _ → f) irefl irefl

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
  inverse (λ _ → invert [p]) _ (λ pp → irr (invert [p]) pp) irefl
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

------------------------------------------------------------------------
-- ⊤, _×_ form a commutative monoid

×-isMagma : ∀ ℓ → IsMagma {Level.suc ℓ} _↔_ _×_
×-isMagma ℓ = record
  { isEquivalence = ↔-isEquivalence
  ; ∙-cong        = _×-cong_
  }

×-magma : (ℓ : Level) → Magma _ _
×-magma ℓ = record
  { isMagma = ×-isMagma ℓ
  }

×-isSemigroup : ∀ ℓ → IsSemigroup {Level.suc ℓ} _↔_ _×_
×-isSemigroup ℓ = record
  { isMagma = ×-isMagma ℓ
  ; assoc   = λ _ _ _ → Σ-assoc
  }

×-semigroup : (ℓ : Level) → Semigroup _ _
×-semigroup ℓ = record
  { isSemigroup = ×-isSemigroup ℓ
  }

×-isMonoid : ∀ ℓ → IsMonoid _↔_ _×_ ⊤
×-isMonoid ℓ = record
  { isSemigroup = ×-isSemigroup ℓ
  ; identity    = (×-identityˡ ℓ) , (×-identityʳ ℓ)
  }

×-monoid : (ℓ : Level) → Monoid _ _
×-monoid ℓ = record
  { isMonoid = ×-isMonoid ℓ
  }

×-isCommutativeMonoid : ∀ ℓ → IsCommutativeMonoid _↔_ _×_ ⊤
×-isCommutativeMonoid ℓ = record
  { isMonoid = ×-isMonoid ℓ
  ; comm     = λ _ _ → ×-comm _ _
  }

×-commutativeMonoid : (ℓ : Level) → CommutativeMonoid _ _
×-commutativeMonoid ℓ = record
  { isCommutativeMonoid = ×-isCommutativeMonoid ℓ
  }
