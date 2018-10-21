------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by Heyting Algebra
------------------------------------------------------------------------

open import Relation.Binary.Lattice

module Relation.Binary.Properties.HeytingAlgebra
  {c ℓ₁ ℓ₂} (L : HeytingAlgebra c ℓ₁ ℓ₂) where

open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Relation.Binary
open import Function using (_$_)

open HeytingAlgebra L
open import Algebra.FunctionProperties _≈_
open import Relation.Binary.PartialOrderReasoning poset
open import Relation.Binary.Properties.MeetSemilattice meetSemilattice
open import Relation.Binary.Properties.JoinSemilattice joinSemilattice
open import Relation.Binary.Properties.Lattice lattice

open IsEquivalence isEquivalence using ()
  renaming (sym to ≈-sym; refl to ≈-refl)

------------------------------------------------------------------------
-- Useful lemmas

⇨-eval : ∀ {x y} → (x ⇨ y) ∧ x ≤ y
⇨-eval {x} {y} = transpose-∧ refl

swap-transpose-⇨ : ∀ {x y w} → x ∧ w ≤ y → w ≤ x ⇨ y
swap-transpose-⇨ x∧w≤y = transpose-⇨ $ trans (reflexive $ ∧-comm _ _) x∧w≤y

------------------------------------------------------------------------
-- Various proofs of distributivity

∧-distribˡ-∨-≤ : ∀ x y z → x ∧ (y ∨ z) ≤ x ∧ y ∨ x ∧ z
∧-distribˡ-∨-≤ x y z = trans (reflexive $ ∧-comm _ _)
  (transpose-∧ $ ∨-least (swap-transpose-⇨ (x≤x∨y _ _)) $ swap-transpose-⇨ (y≤x∨y _ _))

∧-distribˡ-∨-≥ : ∀ x y z → x ∧ y ∨ x ∧ z ≤ x ∧ (y ∨ z)
∧-distribˡ-∨-≥ x y z = let
    x∧y≤x , x∧y≤y , _ = infimum x y
    x∧z≤x , x∧z≤z , _ = infimum x z
    y≤y∨z , z≤y∨z , _ = supremum y z
  in ∧-greatest (∨-least x∧y≤x x∧z≤x)
                (∨-least (trans x∧y≤y y≤y∨z) (trans x∧z≤z z≤y∨z))

∧-distribˡ-∨ : _∧_ DistributesOverˡ _∨_
∧-distribˡ-∨ x y z = antisym (∧-distribˡ-∨-≤ x y z) (∧-distribˡ-∨-≥ x y z)

⇨-distribˡ-∧-≤ : ∀ x y z → x ⇨ y ∧ z ≤ (x ⇨ y) ∧ (x ⇨ z)
⇨-distribˡ-∧-≤ x y z = let
     y∧z≤y , y∧z≤z , _ = infimum y z
   in ∧-greatest (transpose-⇨ $ trans ⇨-eval y∧z≤y)
                 (transpose-⇨ $ trans ⇨-eval y∧z≤z)

⇨-distribˡ-∧-≥ : ∀ x y z → (x ⇨ y) ∧ (x ⇨ z) ≤ x ⇨ y ∧ z
⇨-distribˡ-∧-≥ x y z = transpose-⇨ (begin
  (((x ⇨ y) ∧ (x ⇨ z)) ∧ x)      ≈⟨ ∧-cong ≈-refl $ ≈-sym $ ∧-idempotent _ ⟩
  (((x ⇨ y) ∧ (x ⇨ z)) ∧ x  ∧ x) ≈⟨ ≈-sym $ ∧-assoc _ _ _ ⟩
  (((x ⇨ y) ∧ (x ⇨ z)) ∧ x) ∧ x  ≈⟨ ∧-cong (∧-assoc _ _ _) ≈-refl ⟩
  (((x ⇨ y) ∧ (x ⇨ z)  ∧ x) ∧ x) ≈⟨ ∧-cong (∧-cong ≈-refl $ ∧-comm _ _) ≈-refl ⟩
  (((x ⇨ y) ∧ x  ∧ (x ⇨ z)) ∧ x) ≈⟨ ∧-cong (≈-sym $ ∧-assoc _ _ _) ≈-refl ⟩
  (((x ⇨ y) ∧ x) ∧ (x ⇨ z)) ∧ x  ≈⟨ ∧-assoc _ _ _ ⟩
  (((x ⇨ y) ∧ x) ∧ (x ⇨ z)  ∧ x) ≤⟨ ∧-monotonic ⇨-eval ⇨-eval ⟩
  y ∧ z                          ∎)

⇨-distribˡ-∧ : _⇨_ DistributesOverˡ _∧_
⇨-distribˡ-∧ x y z = antisym (⇨-distribˡ-∧-≤ x y z) (⇨-distribˡ-∧-≥ x y z)

⇨-distribˡ-∨-∧-≤ : ∀ x y z → x ∨ y ⇨ z ≤ (x ⇨ z) ∧ (y ⇨ z)
⇨-distribˡ-∨-∧-≤ x y z = let x≤x∨y , y≤x∨y , _ = supremum x y
   in ∧-greatest (transpose-⇨ $ trans (∧-monotonic refl x≤x∨y) ⇨-eval)
                 (transpose-⇨ $ trans (∧-monotonic refl y≤x∨y) ⇨-eval)

⇨-distribˡ-∨-∧-≥ : ∀ x y z → (x ⇨ z) ∧ (y ⇨ z) ≤ x ∨ y ⇨ z
⇨-distribˡ-∨-∧-≥ x y z = transpose-⇨ (trans (reflexive $ ∧-distribˡ-∨ _ _ _)
  (∨-least (trans (transpose-∧ (x∧y≤x _ _)) refl)
           (trans (transpose-∧ (x∧y≤y _ _)) refl)))

⇨-distribˡ-∨-∧ : ∀ x y z → x ∨ y ⇨ z ≈ (x ⇨ z) ∧ (y ⇨ z)
⇨-distribˡ-∨-∧ x y z = antisym (⇨-distribˡ-∨-∧-≤ x y z) (⇨-distribˡ-∨-∧-≥ x y z)

------------------------------------------------------------------------
-- Heyting algebras are distributive lattices

isDistributiveLattice : IsDistributiveLattice _≈_ _≤_ _∨_ _∧_
isDistributiveLattice = record
  { isLattice    = isLattice
  ; ∧-distribˡ-∨ = ∧-distribˡ-∨
  }

distributiveLattice : DistributiveLattice _ _ _
distributiveLattice = record
  { isDistributiveLattice = isDistributiveLattice
  }
