------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic lemmas showing that various types are related (isomorphic or
-- equivalent or…)
------------------------------------------------------------------------

module Function.Related.TypeIsomorphisms where

open import Algebra
import Algebra.FunctionProperties as FP
open import Algebra.Structures
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product as Prod hiding (swap)
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum as Sum
open import Data.Sum.Properties using (swap-involutive)
open import Data.Sum.Relation.Pointwise using (_⊎-cong_)
open import Data.Unit using (⊤)
open import Level using (Level; Lift; lower; 0ℓ; suc)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq using (_⇔_; Equivalence)
open import Function.Inverse as Inv using (_↔_; Inverse; inverse)
open import Function.Related
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Decidable using (True)

------------------------------------------------------------------------
-- Properties of Σ and _×_

-- Σ is associative
Σ-assoc : ∀ {a b c}
            {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} →
          Σ (Σ A B) (uncurry C) ↔ Σ A (λ a → Σ (B a) (C a))
Σ-assoc = inverse (λ where ((a , b) , c) → (a , b , c))
                  (λ where (a , b , c) → ((a , b) , c))
                  (λ _ → P.refl) (λ _ → P.refl)

-- × is commutative

×-comm : ∀ {a b} (A : Set a) (B : Set b) → (A × B) ↔ (B × A)
×-comm _ _ = inverse Prod.swap Prod.swap (λ _ → P.refl) λ _ → P.refl

-- × has ⊤ as its identity

×-identityˡ : ∀ ℓ → FP.LeftIdentity _↔_ (Lift ℓ ⊤) _×_
×-identityˡ _ _ = inverse proj₂ -,_ (λ _ → P.refl) (λ _ → P.refl)

×-identityʳ : ∀ ℓ → FP.RightIdentity _↔_ (Lift ℓ ⊤) _×_
×-identityʳ _ _ = inverse proj₁ (_, _) (λ _ → P.refl) (λ _ → P.refl)

×-identity : ∀ ℓ → FP.Identity _↔_ (Lift ℓ ⊤) _×_
×-identity ℓ = ×-identityˡ ℓ , ×-identityʳ ℓ

-- × has ⊥ has its zero

×-zeroˡ : ∀ ℓ → FP.LeftZero _↔_ (Lift ℓ ⊥) _×_
×-zeroˡ ℓ A = inverse proj₁ (⊥-elim ∘′ lower)
                      (⊥-elim ∘ lower ∘ proj₁) (⊥-elim ∘ lower)

×-zeroʳ : ∀ ℓ → FP.RightZero _↔_ (Lift ℓ ⊥) _×_
×-zeroʳ ℓ A = inverse proj₂ (⊥-elim ∘′ lower)
                     (⊥-elim ∘ lower ∘ proj₂) (⊥-elim ∘ lower)

×-zero : ∀ ℓ → FP.Zero _↔_ (Lift ℓ ⊥) _×_
×-zero ℓ  = ×-zeroˡ ℓ , ×-zeroʳ ℓ

------------------------------------------------------------------------
-- Properties of ⊎

-- ⊎ is associative

⊎-assoc : ∀ ℓ → FP.Associative {ℓ = ℓ} _↔_ _⊎_
⊎-assoc ℓ _ _ _ = inverse
  [ [ inj₁ , inj₂ ∘′ inj₁ ]′ , inj₂ ∘′ inj₂ ]′
  [ inj₁ ∘′ inj₁ , [ inj₁ ∘′ inj₂ , inj₂ ]′ ]′
  [ [ (λ _ → P.refl) , (λ _ → P.refl) ] , (λ _ → P.refl) ]
  [ (λ _ → P.refl) , [ (λ _ → P.refl) , (λ _ → P.refl) ] ]

-- ⊎ is commutative

⊎-comm : ∀ {a b} (A : Set a) (B : Set b) → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm _ _ = inverse swap swap swap-involutive swap-involutive

-- ⊎ has ⊥ as its identity

⊎-identityˡ : ∀ ℓ → FP.LeftIdentity _↔_ (Lift ℓ ⊥) _⊎_
⊎-identityˡ _ _ = inverse [ (λ ()) , id ]′ inj₂
                          [ (λ ()) , (λ _ → P.refl) ] (λ _ → P.refl)

⊎-identityʳ : ∀ ℓ → FP.RightIdentity _↔_ (Lift ℓ ⊥) _⊎_
⊎-identityʳ _ _ = inverse [ id , (λ ()) ]′ inj₁
                          [ (λ _ → P.refl) , (λ ()) ] (λ _ → P.refl)

⊎-identity : ∀ ℓ → FP.Identity _↔_ (Lift ℓ ⊥) _⊎_
⊎-identity ℓ = ⊎-identityˡ ℓ , ⊎-identityʳ ℓ

------------------------------------------------------------------------
-- Properties of × and ⊎

-- × distributes over ⊎

×-distribˡ-⊎ : ∀ ℓ → FP._DistributesOverˡ_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distribˡ-⊎ ℓ _ _ _ = inverse
  (uncurry λ x → [ inj₁ ∘′ (x ,_) , inj₂ ∘′ (x ,_) ]′)
  [ Prod.map₂ inj₁ , Prod.map₂ inj₂ ]′
  (uncurry λ _ → [ (λ _ → P.refl) , (λ _ → P.refl) ])
  [ (λ _ → P.refl) , (λ _ → P.refl) ]

×-distribʳ-⊎ : ∀ ℓ → FP._DistributesOverʳ_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distribʳ-⊎ ℓ _ _ _ = inverse
  (uncurry [ curry inj₁ , curry inj₂ ]′)
  [ Prod.map₁ inj₁ , Prod.map₁ inj₂ ]′
  (uncurry [ (λ _ _ → P.refl) , (λ _ _ → P.refl) ])
  [ (λ _ → P.refl) , (λ _ → P.refl) ]

×-distrib-⊎ : ∀ ℓ → FP._DistributesOver_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distrib-⊎ ℓ = ×-distribˡ-⊎ ℓ , ×-distribʳ-⊎ ℓ

------------------------------------------------------------------------
-- ⊥, ⊤, _×_ and _⊎_ form a commutative semiring

-- ⊤, _×_ form a commutative monoid

×-isSemigroup : ∀ k ℓ → IsSemigroup {Level.suc ℓ} (Related ⌊ k ⌋) _×_
×-isSemigroup k ℓ = record
  { isEquivalence = SK-isEquivalence k ℓ
  ; assoc         = λ _ _ _ → ↔⇒ Σ-assoc
  ; ∙-cong        = _×-cong_
  }

×-semigroup : Symmetric-kind → (ℓ : Level) → Semigroup _ _
×-semigroup k ℓ = record
  { isSemigroup = ×-isSemigroup k ℓ
  }

×-isMonoid : ∀ k ℓ → IsMonoid (Related ⌊ k ⌋) _×_ (Lift ℓ ⊤)
×-isMonoid k ℓ = record
  { isSemigroup = ×-isSemigroup k ℓ
  ; identity    = (↔⇒ ∘ ×-identityˡ ℓ) , (↔⇒ ∘ ×-identityʳ ℓ)
  }

×-monoid : Symmetric-kind → (ℓ : Level) → Monoid _ _
×-monoid k ℓ = record
  { isMonoid = ×-isMonoid k ℓ
  }

×-isCommutativeMonoid : ∀ k ℓ → IsCommutativeMonoid (Related ⌊ k ⌋) _×_ (Lift ℓ ⊤)
×-isCommutativeMonoid k ℓ = record
  { isSemigroup = ×-isSemigroup k ℓ
  ; identityˡ   = ↔⇒ ∘ ×-identityˡ ℓ
  ; comm        = λ _ _ → ↔⇒ (×-comm _ _)
  }

×-commutativeMonoid : Symmetric-kind → (ℓ : Level) → CommutativeMonoid _ _
×-commutativeMonoid k ℓ = record
  { isCommutativeMonoid = ×-isCommutativeMonoid k ℓ
  }

-- ⊥, _⊎_ form a commutative monoid

⊎-isSemigroup : ∀ k ℓ → IsSemigroup {Level.suc ℓ} (Related ⌊ k ⌋) _⊎_
⊎-isSemigroup k ℓ = record
  { isEquivalence = SK-isEquivalence k ℓ
  ; assoc         = λ A B C → ↔⇒ (⊎-assoc ℓ A B C)
  ; ∙-cong        = _⊎-cong_
  }

⊎-semigroup : Symmetric-kind → (ℓ : Level) → Semigroup _ _
⊎-semigroup k ℓ = record
  { isSemigroup = ⊎-isSemigroup k ℓ
  }

⊎-isMonoid : ∀ k ℓ → IsMonoid (Related ⌊ k ⌋) _⊎_ (Lift ℓ ⊥)
⊎-isMonoid k ℓ = record
  { isSemigroup = ⊎-isSemigroup k ℓ
  ; identity    = (↔⇒ ∘ ⊎-identityˡ ℓ) , (↔⇒ ∘ ⊎-identityʳ ℓ)
  }

⊎-monoid : Symmetric-kind → (ℓ : Level) → Monoid _ _
⊎-monoid k ℓ = record
  { isMonoid = ⊎-isMonoid k ℓ
  }

⊎-isCommutativeMonoid : ∀ k ℓ → IsCommutativeMonoid (Related ⌊ k ⌋) _⊎_ (Lift ℓ ⊥)
⊎-isCommutativeMonoid k ℓ = record
  { isSemigroup = ⊎-isSemigroup k ℓ
  ; identityˡ   = ↔⇒ ∘ ⊎-identityˡ ℓ
  ; comm        = λ _ _ → ↔⇒ (⊎-comm _ _)
  }

⊎-commutativeMonoid : Symmetric-kind → (ℓ : Level) →
                      CommutativeMonoid _ _
⊎-commutativeMonoid k ℓ = record
  { isCommutativeMonoid = ⊎-isCommutativeMonoid k ℓ
  }

×-⊎-isCommutativeSemiring : ∀ k ℓ →
  IsCommutativeSemiring (Related ⌊ k ⌋) _⊎_ _×_ (Lift ℓ ⊥) (Lift ℓ ⊤)
×-⊎-isCommutativeSemiring k ℓ = record
  { +-isCommutativeMonoid = ⊎-isCommutativeMonoid k ℓ
  ; *-isCommutativeMonoid = ×-isCommutativeMonoid k ℓ
  ; distribʳ              = λ A B C → ↔⇒ (×-distribʳ-⊎ ℓ A B C)
  ; zeroˡ                 = ↔⇒ ∘ ×-zeroˡ ℓ
  }

×-⊎-commutativeSemiring : Symmetric-kind → (ℓ : Level) →
                          CommutativeSemiring (Level.suc ℓ) ℓ
×-⊎-commutativeSemiring k ℓ = record
  { isCommutativeSemiring = ×-⊎-isCommutativeSemiring k ℓ
  }

------------------------------------------------------------------------
-- Some reordering lemmas

ΠΠ↔ΠΠ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) →
        ((x : A) (y : B) → P x y) ↔ ((y : B) (x : A) → P x y)
ΠΠ↔ΠΠ _ = inverse flip flip (λ _ → P.refl) (λ _ → P.refl)

∃∃↔∃∃ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) →
        (∃₂ λ x y → P x y) ↔ (∃₂ λ y x → P x y)
∃∃↔∃∃ P = inverse to from (λ _ → P.refl) (λ _ → P.refl)
  where
  to : (∃₂ λ x y → P x y) → (∃₂ λ y x → P x y)
  to (x , y , Pxy) = (y , x , Pxy)

  from : (∃₂ λ y x → P x y) → (∃₂ λ x y → P x y)
  from (y , x , Pxy) = (x , y , Pxy)

------------------------------------------------------------------------
-- Implicit and explicit function spaces are isomorphic

Π↔Π : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) ↔ ({x : A} → B x)
Π↔Π = inverse (λ f {x} → f x) (λ f x → f) (λ _ → P.refl) (λ _ → P.refl)

------------------------------------------------------------------------
-- _→_ preserves the symmetric relations

_→-cong-⇔_ :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  A ⇔ B → C ⇔ D → (A → C) ⇔ (B → D)
A⇔B →-cong-⇔ C⇔D = Eq.equivalence
  (λ f x → Equivalence.to   C⇔D ⟨$⟩ f (Equivalence.from A⇔B ⟨$⟩ x))
  (λ f x → Equivalence.from C⇔D ⟨$⟩ f (Equivalence.to   A⇔B ⟨$⟩ x))

→-cong :
  ∀ {a b c d} →
  P.Extensionality a c → P.Extensionality b d →
  ∀ {k} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  A ∼[ ⌊ k ⌋ ] B → C ∼[ ⌊ k ⌋ ] D → (A → C) ∼[ ⌊ k ⌋ ] (B → D)
→-cong extAC extBD {equivalence} A⇔B C⇔D = A⇔B →-cong-⇔ C⇔D
→-cong extAC extBD {bijection}   A↔B C↔D = record
  { to         = Equivalence.to   A→C⇔B→D
  ; from       = Equivalence.from A→C⇔B→D
  ; inverse-of = record
    { left-inverse-of  = λ f → extAC λ x → begin
        Inverse.from C↔D ⟨$⟩ (Inverse.to C↔D ⟨$⟩
          f (Inverse.from A↔B ⟨$⟩ (Inverse.to A↔B ⟨$⟩ x)))  ≡⟨ Inverse.left-inverse-of C↔D _ ⟩
        f (Inverse.from A↔B ⟨$⟩ (Inverse.to A↔B ⟨$⟩ x))     ≡⟨ P.cong f $ Inverse.left-inverse-of A↔B x ⟩
        f x                                                 ∎
    ; right-inverse-of = λ f → extBD λ x → begin
        Inverse.to C↔D ⟨$⟩ (Inverse.from C↔D ⟨$⟩
          f (Inverse.to A↔B ⟨$⟩ (Inverse.from A↔B ⟨$⟩ x)))  ≡⟨ Inverse.right-inverse-of C↔D _ ⟩
        f (Inverse.to A↔B ⟨$⟩ (Inverse.from A↔B ⟨$⟩ x))     ≡⟨ P.cong f $ Inverse.right-inverse-of A↔B x ⟩
        f x                                                 ∎
    }
  }
  where
  open P.≡-Reasoning
  A→C⇔B→D = ↔⇒ A↔B →-cong-⇔ ↔⇒ C↔D

------------------------------------------------------------------------
-- ¬_ preserves the symmetric relations

¬-cong-⇔ : ∀ {a b} {A : Set a} {B : Set b} →
           A ⇔ B → (¬ A) ⇔ (¬ B)
¬-cong-⇔ A⇔B = A⇔B →-cong-⇔ (⊥ ∎)
  where open EquationalReasoning

¬-cong : ∀ {a b} →
         P.Extensionality a 0ℓ →
         P.Extensionality b 0ℓ →
         ∀ {k} {A : Set a} {B : Set b} →
         A ∼[ ⌊ k ⌋ ] B → (¬ A) ∼[ ⌊ k ⌋ ] (¬ B)
¬-cong extA extB A≈B = →-cong extA extB A≈B (⊥ ∎)
  where open EquationalReasoning

------------------------------------------------------------------------
-- _⇔_ preserves _⇔_

-- The type of the following proof is a bit more general.

Related-cong :
  ∀ {k a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  A ∼[ ⌊ k ⌋ ] B → C ∼[ ⌊ k ⌋ ] D → (A ∼[ ⌊ k ⌋ ] C) ⇔ (B ∼[ ⌊ k ⌋ ] D)
Related-cong {A = A} {B} {C} {D} A≈B C≈D =
  Eq.equivalence (λ A≈C → B  ∼⟨ SK-sym A≈B ⟩
                          A  ∼⟨ A≈C ⟩
                          C  ∼⟨ C≈D ⟩
                          D  ∎)
                 (λ B≈D → A  ∼⟨ A≈B ⟩
                          B  ∼⟨ B≈D ⟩
                          D  ∼⟨ SK-sym C≈D ⟩
                          C  ∎)
  where open EquationalReasoning

------------------------------------------------------------------------
-- A lemma relating True dec and P, where dec : Dec P

True↔ : ∀ {p} {P : Set p}
        (dec : Dec P) → ((p₁ p₂ : P) → p₁ ≡ p₂) → True dec ↔ P
True↔ (yes p) irr = inverse (λ _ → p) (λ _ → _) (λ _ → P.refl) (irr p)
True↔ (no ¬p) _   = inverse (λ()) ¬p (λ()) (⊥-elim ∘ ¬p)

------------------------------------------------------------------------
-- Equality between pairs can be expressed as a pair of equalities

Σ-≡,≡↔≡ : ∀ {a b} {A : Set a} {B : A → Set b} {p₁ p₂ : Σ A B} →
          (∃ λ (p : proj₁ p₁ ≡ proj₁ p₂) →
             P.subst B p (proj₂ p₁) ≡ proj₂ p₂) ↔
          (p₁ ≡ p₂)
Σ-≡,≡↔≡ {A = A} {B} = inverse to from left-inverse-of right-inverse-of
  where
  to : {p₁ p₂ : Σ A B} →
       Σ (proj₁ p₁ ≡ proj₁ p₂)
         (λ p → P.subst B p (proj₂ p₁) ≡ proj₂ p₂) →
       p₁ ≡ p₂
  to (P.refl , P.refl) = P.refl

  from : {p₁ p₂ : Σ A B} →
         p₁ ≡ p₂ →
         Σ (proj₁ p₁ ≡ proj₁ p₂)
           (λ p → P.subst B p (proj₂ p₁) ≡ proj₂ p₂)
  from P.refl = P.refl , P.refl

  left-inverse-of : {p₁ p₂ : Σ A B}
                    (p : Σ (proj₁ p₁ ≡ proj₁ p₂)
                           (λ x → P.subst B x (proj₂ p₁) ≡ proj₂ p₂)) →
                    from (to p) ≡ p
  left-inverse-of (P.refl , P.refl) = P.refl

  right-inverse-of : {p₁ p₂ : Σ A B} (p : p₁ ≡ p₂) → to (from p) ≡ p
  right-inverse-of P.refl = P.refl

×-≡,≡↔≡ : ∀ {a b} {A : Set a} {B : Set b} {p₁ p₂ : A × B} →
          (proj₁ p₁ ≡ proj₁ p₂ × proj₂ p₁ ≡ proj₂ p₂) ↔ p₁ ≡ p₂
×-≡,≡↔≡ {A = A} {B} = inverse to from left-inverse-of right-inverse-of
  where
  to : {p₁ p₂ : A × B} →
       (proj₁ p₁ ≡ proj₁ p₂) × (proj₂ p₁ ≡ proj₂ p₂) → p₁ ≡ p₂
  to (P.refl , P.refl) = P.refl

  from : {p₁ p₂ : A × B} → p₁ ≡ p₂ →
         (proj₁ p₁ ≡ proj₁ p₂) × (proj₂ p₁ ≡ proj₂ p₂)
  from P.refl = P.refl , P.refl

  left-inverse-of : {p₁ p₂ : A × B} →
                    (p : (proj₁ p₁ ≡ proj₁ p₂) × (proj₂ p₁ ≡ proj₂ p₂)) →
                    from (to p) ≡ p
  left-inverse-of (P.refl , P.refl) = P.refl

  right-inverse-of : {p₁ p₂ : A × B} (p : p₁ ≡ p₂) → to (from p) ≡ p
  right-inverse-of P.refl = P.refl

×-≡×≡↔≡,≡ : ∀ {a b} {A : Set a} {B : Set b} {x y} (p : A × B) →
            (x ≡ proj₁ p × y ≡ proj₂ p) ↔ (x , y) ≡ p
×-≡×≡↔≡,≡ {x = x} {y} p = inverse to from from∘to to∘from
   where
   to : (x ≡ proj₁ p × y ≡ proj₂ p) → (x , y) ≡ p
   to = uncurry $ P.cong₂ _,_

   from : (x , y) ≡ p → (x ≡ proj₁ p × y ≡ proj₂ p)
   from = < P.cong proj₁ , P.cong proj₂ >

   from∘to : ∀ v → from (to v) ≡ v
   from∘to _ = P.cong₂ _,_ (P.≡-irrelevance _ _) (P.≡-irrelevance _ _)

   to∘from : ∀ v → to (from v) ≡ v
   to∘from _ = P.≡-irrelevance _ _

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.17

×-CommutativeMonoid = ×-commutativeMonoid
{-# WARNING_ON_USAGE ×-CommutativeMonoid
"Warning: ×-CommutativeMonoid was deprecated in v0.17.
Please use ×-commutativeMonoid instead."
#-}
⊎-CommutativeMonoid = ⊎-commutativeMonoid
{-# WARNING_ON_USAGE ⊎-CommutativeMonoid
"Warning: ⊎-CommutativeMonoid was deprecated in v0.17.
Please use ⊎-commutativeMonoid instead."
#-}
×⊎-CommutativeSemiring = ×-⊎-commutativeSemiring
{-# WARNING_ON_USAGE ×⊎-CommutativeSemiring
"Warning: ×⊎-CommutativeSemiring was deprecated in v0.17.
Please use ×-⊎-commutativeSemiring instead."
#-}
