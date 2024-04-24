------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic lemmas showing that various types are related (isomorphic or
-- equivalent or…)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Related.TypeIsomorphisms where

open import Algebra
open import Algebra.Structures.Biased using (isCommutativeSemiringˡ)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Bool.Base using (true; false)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Product.Base as Product
  using (_×_; Σ; curry; uncurry; _,_; -,_; <_,_>; proj₁; proj₂; ∃₂; ∃)
open import Data.Product.Function.NonDependent.Propositional
open import Data.Sum.Base as Sum
open import Data.Sum.Properties using (swap-involutive)
open import Data.Sum.Function.Propositional using (_⊎-cong_)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Level using (Level; Lift; 0ℓ; suc)
open import Function.Base
open import Function.Bundles
open import Function.Related.Propositional
import Function.Construct.Identity as Identity
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary using (Dec; ¬_; _because_; ofⁿ; contradiction)
import Relation.Nullary.Indexed as I
open import Relation.Nullary.Decidable using (True)

private
  variable
    a b c d : Level
    A B C D : Set a

------------------------------------------------------------------------
-- Properties of Σ and _×_

-- Σ is associative
Σ-assoc : ∀ {A : Set a} {B : A → Set b} {C : (a : A) → B a → Set c} →
          Σ (Σ A B) (uncurry C) ↔ Σ A (λ a → Σ (B a) (C a))
Σ-assoc = mk↔ₛ′ Product.assocʳ Product.assocˡ (λ _ → refl) (λ _ → refl)

-- × is commutative

×-comm : ∀ (A : Set a) (B : Set b) → (A × B) ↔ (B × A)
×-comm _ _ = mk↔ₛ′ Product.swap Product.swap (λ _ → refl) λ _ → refl

-- × has ⊤ as its identity

×-identityˡ : ∀ ℓ → LeftIdentity  {ℓ = ℓ} _↔_ ⊤ _×_
×-identityˡ _ _ = mk↔ₛ′ proj₂ -,_ (λ _ → refl) (λ _ → refl)

×-identityʳ : ∀ ℓ → RightIdentity  {ℓ = ℓ} _↔_ ⊤ _×_
×-identityʳ _ _ = mk↔ₛ′ proj₁ (_, _) (λ _ → refl) (λ _ → refl)

×-identity : ∀ ℓ → Identity _↔_ ⊤ _×_
×-identity ℓ = ×-identityˡ ℓ , ×-identityʳ ℓ

-- × has ⊥ has its zero

×-zeroˡ : ∀ ℓ → LeftZero {ℓ = ℓ} _↔_ ⊥ _×_
×-zeroˡ ℓ A = mk↔ₛ′ proj₁ < id , ⊥-elim > (λ _ → refl) (λ { () })

×-zeroʳ : ∀ ℓ → RightZero {ℓ = ℓ} _↔_ ⊥ _×_
×-zeroʳ ℓ A = mk↔ₛ′ proj₂ < ⊥-elim , id > (λ _ → refl) (λ { () })

×-zero : ∀ ℓ → Zero _↔_ ⊥ _×_
×-zero ℓ  = ×-zeroˡ ℓ , ×-zeroʳ ℓ

------------------------------------------------------------------------
-- Properties of ⊎

-- ⊎ is associative

⊎-assoc : ∀ ℓ → Associative {ℓ = ℓ} _↔_ _⊎_
⊎-assoc ℓ _ _ _ = mk↔ₛ′
  [ [ inj₁ , inj₂ ∘′ inj₁ ]′ , inj₂ ∘′ inj₂ ]′
  [ inj₁ ∘′ inj₁ , [ inj₁ ∘′ inj₂ , inj₂ ]′ ]′
  [ (λ _ → refl) , [ (λ _ → refl) , (λ _ → refl) ] ]
  [ [ (λ _ → refl) , (λ _ → refl) ] , (λ _ → refl) ]

-- ⊎ is commutative

⊎-comm : ∀ (A : Set a) (B : Set b) → (A ⊎ B) ↔ (B ⊎ A)
⊎-comm _ _ = mk↔ₛ′ swap swap swap-involutive swap-involutive

-- ⊎ has ⊥ as its identity

⊎-identityˡ : ∀ ℓ → LeftIdentity _↔_ (⊥ {ℓ}) _⊎_
⊎-identityˡ _ _ = mk↔ₛ′ [ (λ ()) , id ]′ inj₂ (λ _ → refl)
                          [ (λ ()) , (λ _ → refl) ]

⊎-identityʳ : ∀ ℓ → RightIdentity _↔_ (⊥ {ℓ}) _⊎_
⊎-identityʳ _ _ = mk↔ₛ′ [ id , (λ ()) ]′ inj₁ (λ _ → refl)
                          [ (λ _ → refl) , (λ ()) ]

⊎-identity : ∀ ℓ → Identity _↔_ ⊥ _⊎_
⊎-identity ℓ = ⊎-identityˡ ℓ , ⊎-identityʳ ℓ

------------------------------------------------------------------------
-- Properties of × and ⊎

-- × distributes over ⊎

×-distribˡ-⊎ : ∀ ℓ → _DistributesOverˡ_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distribˡ-⊎ ℓ _ _ _ = mk↔ₛ′
  (uncurry λ x → [ inj₁ ∘′ (x ,_) , inj₂ ∘′ (x ,_) ]′)
  [ Product.map₂ inj₁ , Product.map₂ inj₂ ]′
  [ (λ _ → refl) , (λ _ → refl) ]
  (uncurry λ _ → [ (λ _ → refl) , (λ _ → refl) ])

×-distribʳ-⊎ : ∀ ℓ → _DistributesOverʳ_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distribʳ-⊎ ℓ _ _ _ = mk↔ₛ′
  (uncurry [ curry inj₁ , curry inj₂ ]′)
  [ Product.map₁ inj₁ , Product.map₁ inj₂ ]′
  [ (λ _ → refl) , (λ _ → refl) ]
  (uncurry [ (λ _ _ → refl) , (λ _ _ → refl) ])

×-distrib-⊎ : ∀ ℓ → _DistributesOver_ {ℓ = ℓ} _↔_ _×_ _⊎_
×-distrib-⊎ ℓ = ×-distribˡ-⊎ ℓ , ×-distribʳ-⊎ ℓ

------------------------------------------------------------------------
-- ⊥, ⊤, _×_ and _⊎_ form a commutative semiring

-- ⊤, _×_ form a commutative monoid

×-isMagma : ∀ k ℓ → IsMagma {Level.suc ℓ} (Related ⌊ k ⌋) _×_
×-isMagma k ℓ = record
  { isEquivalence = SK-isEquivalence k
  ; ∙-cong        = _×-cong_
  }

×-magma : SymmetricKind → (ℓ : Level) → Magma _ _
×-magma k ℓ = record
  { isMagma = ×-isMagma k ℓ
  }

×-isSemigroup : ∀ k ℓ → IsSemigroup {Level.suc ℓ} (Related ⌊ k ⌋) _×_
×-isSemigroup k ℓ = record
  { isMagma = ×-isMagma k ℓ
  ; assoc   = λ _ _ _ → ↔⇒ Σ-assoc
  }

×-semigroup : SymmetricKind → (ℓ : Level) → Semigroup _ _
×-semigroup k ℓ = record
  { isSemigroup = ×-isSemigroup k ℓ
  }

×-isMonoid : ∀ k ℓ → IsMonoid (Related ⌊ k ⌋) _×_ ⊤
×-isMonoid k ℓ = record
  { isSemigroup = ×-isSemigroup k ℓ
  ; identity    = (↔⇒ ∘ ×-identityˡ ℓ) , (↔⇒ ∘ ×-identityʳ ℓ)
  }

×-monoid : SymmetricKind → (ℓ : Level) → Monoid _ _
×-monoid k ℓ = record
  { isMonoid = ×-isMonoid k ℓ
  }

×-isCommutativeMonoid : ∀ k ℓ → IsCommutativeMonoid (Related ⌊ k ⌋) _×_ ⊤
×-isCommutativeMonoid k ℓ = record
  { isMonoid = ×-isMonoid k ℓ
  ; comm     = λ _ _ → ↔⇒ (×-comm _ _)
  }

×-commutativeMonoid : SymmetricKind → (ℓ : Level) → CommutativeMonoid _ _
×-commutativeMonoid k ℓ = record
  { isCommutativeMonoid = ×-isCommutativeMonoid k ℓ
  }

-- ⊥, _⊎_ form a commutative monoid

⊎-isMagma : ∀ k ℓ → IsMagma {Level.suc ℓ} (Related ⌊ k ⌋) _⊎_
⊎-isMagma k ℓ = record
  { isEquivalence = SK-isEquivalence k
  ; ∙-cong        = _⊎-cong_
  }

⊎-magma : SymmetricKind → (ℓ : Level) → Magma _ _
⊎-magma k ℓ = record
  { isMagma = ⊎-isMagma k ℓ
  }

⊎-isSemigroup : ∀ k ℓ → IsSemigroup {Level.suc ℓ} (Related ⌊ k ⌋) _⊎_
⊎-isSemigroup k ℓ = record
  { isMagma = ⊎-isMagma k ℓ
  ; assoc   = λ A B C → ↔⇒ (⊎-assoc ℓ A B C)
  }

⊎-semigroup : SymmetricKind → (ℓ : Level) → Semigroup _ _
⊎-semigroup k ℓ = record
  { isSemigroup = ⊎-isSemigroup k ℓ
  }

⊎-isMonoid : ∀ k ℓ → IsMonoid (Related ⌊ k ⌋) _⊎_ ⊥
⊎-isMonoid k ℓ = record
  { isSemigroup = ⊎-isSemigroup k ℓ
  ; identity    = (↔⇒ ∘ ⊎-identityˡ ℓ) , (↔⇒ ∘ ⊎-identityʳ ℓ)
  }

⊎-monoid : SymmetricKind → (ℓ : Level) → Monoid _ _
⊎-monoid k ℓ = record
  { isMonoid = ⊎-isMonoid k ℓ
  }

⊎-isCommutativeMonoid : ∀ k ℓ → IsCommutativeMonoid (Related ⌊ k ⌋) _⊎_ ⊥
⊎-isCommutativeMonoid k ℓ = record
  { isMonoid = ⊎-isMonoid k ℓ
  ; comm     = λ _ _ → ↔⇒ (⊎-comm _ _)
  }

⊎-commutativeMonoid : SymmetricKind → (ℓ : Level) →
                      CommutativeMonoid _ _
⊎-commutativeMonoid k ℓ = record
  { isCommutativeMonoid = ⊎-isCommutativeMonoid k ℓ
  }

×-⊎-isCommutativeSemiring : ∀ k ℓ →
  IsCommutativeSemiring (Related ⌊ k ⌋) _⊎_ _×_ ⊥ ⊤
×-⊎-isCommutativeSemiring k ℓ = isCommutativeSemiringˡ record
  { +-isCommutativeMonoid = ⊎-isCommutativeMonoid k ℓ
  ; *-isCommutativeMonoid = ×-isCommutativeMonoid k ℓ
  ; distribʳ              = λ A B C → ↔⇒ (×-distribʳ-⊎ ℓ A B C)
  ; zeroˡ                 = ↔⇒ ∘ ×-zeroˡ ℓ
  }

×-⊎-commutativeSemiring : SymmetricKind → (ℓ : Level) →
                          CommutativeSemiring (Level.suc ℓ) ℓ
×-⊎-commutativeSemiring k ℓ = record
  { isCommutativeSemiring = ×-⊎-isCommutativeSemiring k ℓ
  }

------------------------------------------------------------------------
-- Some reordering lemmas

ΠΠ↔ΠΠ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) →
        ((x : A) (y : B) → P x y) ↔ ((y : B) (x : A) → P x y)
ΠΠ↔ΠΠ _ = mk↔ₛ′ flip flip (λ _ → refl) (λ _ → refl)

∃∃↔∃∃ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) →
        (∃₂ λ x y → P x y) ↔ (∃₂ λ y x → P x y)
∃∃↔∃∃ P = mk↔ₛ′ to from (λ _ → refl) (λ _ → refl)
  where
  to : (∃₂ λ x y → P x y) → (∃₂ λ y x → P x y)
  to (x , y , Pxy) = (y , x , Pxy)

  from : (∃₂ λ y x → P x y) → (∃₂ λ x y → P x y)
  from (y , x , Pxy) = (x , y , Pxy)

------------------------------------------------------------------------
-- Implicit and explicit function spaces are isomorphic

Π↔Π : ∀ {A : Set a} {B : A → Set b} →
      ((x : A) → B x) ↔ ({x : A} → B x)
Π↔Π = mk↔ₛ′ _$- λ- (λ _ → refl) (λ _ → refl)

------------------------------------------------------------------------
-- _→_ preserves the symmetric relations

→-cong-⇔ : A ⇔ B → C ⇔ D → (A → C) ⇔ (B → D)
→-cong-⇔ A⇔B C⇔D = mk⇔
  (λ f → to C⇔D ∘ f ∘ from A⇔B)
  (λ f → from C⇔D ∘ f ∘ to A⇔B)
  where open Equivalence

→-cong-↔ : Extensionality a c → Extensionality b d →
             {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
             A ↔ B → C ↔ D → (A → C) ↔ (B → D)
→-cong-↔ ext₁ ext₂ A↔B C↔D = mk↔ₛ′
  (λ f → to C↔D ∘ f ∘ from A↔B)
  (λ f → from C↔D ∘ f ∘ to A↔B)
  (λ f → ext₂ λ x → begin
    to C↔D (from C↔D (f (to A↔B (from A↔B x)))) ≡⟨ strictlyInverseˡ C↔D _ ⟩
    f (to A↔B (from A↔B x))                     ≡⟨ cong f $ strictlyInverseˡ A↔B x ⟩
    f x                                         ∎)
  (λ f → ext₁ λ x → begin
    from C↔D (to C↔D (f (from A↔B (to A↔B x)))) ≡⟨ strictlyInverseʳ C↔D _ ⟩
    f (from A↔B (to A↔B x))                     ≡⟨ cong f $ strictlyInverseʳ A↔B x ⟩
    f x                                         ∎)
  where open Inverse; open ≡-Reasoning

→-cong :  Extensionality a c → Extensionality b d →
          ∀ {k} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
          A ∼[ ⌊ k ⌋ ] B → C ∼[ ⌊ k ⌋ ] D → (A → C) ∼[ ⌊ k ⌋ ] (B → D)
→-cong extAC extBD {equivalence} = →-cong-⇔
→-cong extAC extBD {bijection}   = →-cong-↔ extAC extBD

------------------------------------------------------------------------
-- ¬_ (at Level 0) preserves the symmetric relations

¬-cong-⇔ : A ⇔ B → (¬ A) ⇔ (¬ B)
¬-cong-⇔ A⇔B = →-cong-⇔ A⇔B (Identity.⇔-id _)

¬-cong : Extensionality a 0ℓ → Extensionality b 0ℓ →
         ∀ {k} {A : Set a} {B : Set b} →
         A ∼[ ⌊ k ⌋ ] B → (¬ A) ∼[ ⌊ k ⌋ ] (¬ B)
¬-cong extA extB A≈B = →-cong extA extB A≈B (K-reflexive refl)

------------------------------------------------------------------------
-- _⇔_ preserves _⇔_

-- The type of the following proof is a bit more general.

Related-cong :
  ∀ {k} →
  A ∼[ ⌊ k ⌋ ] B → C ∼[ ⌊ k ⌋ ] D → (A ∼[ ⌊ k ⌋ ] C) ⇔ (B ∼[ ⌊ k ⌋ ] D)
Related-cong {A = A} {B = B} {C = C} {D = D} A≈B C≈D = mk⇔
  (λ A≈C → B  ∼⟨ SK-sym A≈B ⟩
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
True↔ ( true because  [p]) irr =
  mk↔ₛ′ (λ _ → invert [p]) (λ _ → _) (irr _) (λ _ → refl)
True↔ (false because ofⁿ ¬p) _ =
  mk↔ₛ′ (λ()) (invert (ofⁿ ¬p)) (λ x → flip contradiction ¬p x) (λ ())
