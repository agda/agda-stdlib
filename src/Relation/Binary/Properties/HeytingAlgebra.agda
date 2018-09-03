------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by Heyting Algebra
------------------------------------------------------------------------

open import Relation.Binary.Lattice

module Relation.Binary.Properties.HeytingAlgebra
  {c ℓ₁ ℓ₂} (L : HeytingAlgebra c ℓ₁ ℓ₂) where

open HeytingAlgebra L

open import Level using (_⊔_)

open import Function using (_$_)
open import Data.Product
open import Relation.Binary
open import Algebra.FunctionProperties _≈_
open import Data.Product using (_,_)
import Relation.Binary.SetoidReasoning as SetoidR
import Relation.Binary.PartialOrderReasoning as PoR

open import Relation.Binary.Properties.MeetSemilattice meetSemilattice
open import Relation.Binary.Properties.JoinSemilattice joinSemilattice
open import Relation.Binary.Properties.Lattice lattice
open IsEquivalence isEquivalence using () renaming (sym to ≈-sym; refl to ≈-refl)


⇨-eval : ∀ {x y} → (x ⇨ y) ∧ x ≤ y
⇨-eval {x} {y} = transpose-∧ refl

⇨-distribˡ-∧ : _⇨_ DistributesOverˡ _∧_
⇨-distribˡ-∧ x y z = antisym
  (let y∧z≤y , y∧z≤z , _ = infimum y z
   in ∧-greatest (transpose-⇨ $ trans ⇨-eval y∧z≤y)
                 (transpose-⇨ $ trans ⇨-eval y∧z≤z))
  (transpose-⇨ (begin ((x ⇨ y) ∧ (x ⇨ z)) ∧ x       ≈⟨ ∧-cong ≈-refl $ ≈-sym $ ∧-idempotent _ ⟩
                      ((x ⇨ y) ∧ (x ⇨ z)) ∧ x ∧ x   ≈⟨ ≈-sym $ ∧-assoc _ _ _ ⟩
                      (((x ⇨ y) ∧ (x ⇨ z)) ∧ x) ∧ x ≈⟨ ∧-cong (∧-assoc _ _ _) ≈-refl ⟩
                      ((x ⇨ y) ∧ (x ⇨ z) ∧ x) ∧ x   ≈⟨ ∧-cong (∧-cong ≈-refl $ ∧-comm _ _) ≈-refl ⟩
                      ((x ⇨ y) ∧ x ∧ (x ⇨ z)) ∧ x   ≈⟨ ∧-cong (≈-sym $ ∧-assoc _ _ _) ≈-refl ⟩
                      (((x ⇨ y) ∧ x) ∧ (x ⇨ z)) ∧ x ≈⟨ ∧-assoc _ _ _ ⟩
                      ((x ⇨ y) ∧ x) ∧ (x ⇨ z) ∧ x   ≤⟨ ∧-monotonic ⇨-eval ⇨-eval ⟩
                      y ∧ z                         ∎))
   where open PoR poset

swap-transpose-⇨ : ∀ {x y w} → x ∧ w ≤ y → w ≤ x ⇨ y
swap-transpose-⇨ x∧w≤y = transpose-⇨ $ trans (reflexive $ ∧-comm _ _) x∧w≤y

∧-distribˡ-∨ : _∧_ DistributesOverˡ _∨_
∧-distribˡ-∨ x y z = antisym
  (trans (reflexive $ ∧-comm _ _)
         (transpose-∧ $ ∨-least (swap-transpose-⇨ ∨-fst) $ swap-transpose-⇨ ∨-snd))

  let x∧y≤x , x∧y≤y , _ = infimum x y
      x∧z≤x , x∧z≤z , _ = infimum x z
      y≤y∨z , z≤y∨z , _ = supremum y z
  in ∧-greatest (∨-least x∧y≤x x∧z≤x)
                (∨-least (trans x∧y≤y y≤y∨z)
                         (trans x∧z≤z z≤y∨z))


isDistributiveLattice : IsDistributiveLattice _≈_ _≤_ _∨_ _∧_
isDistributiveLattice = record { isLattice = isLattice ; ∧-distribˡ-∨ = ∧-distribˡ-∨ }

distributiveLattice : DistributiveLattice _ _ _
distributiveLattice = record { isDistributiveLattice = isDistributiveLattice }

⇨-distribˡ-∨-∧ : ∀ x y z → x ∨ y ⇨ z ≈ (x ⇨ z) ∧ (y ⇨ z)
⇨-distribˡ-∨-∧ x y z = antisym
  (let x≤x∨y , y≤x∨y , _ = supremum x y
   in ∧-greatest (transpose-⇨ $ trans (∧-monotonic refl x≤x∨y) ⇨-eval)
                 (transpose-⇨ $ trans (∧-monotonic refl y≤x∨y) ⇨-eval))
  (transpose-⇨ (trans (reflexive $ ∧-distribˡ-∨ _ _ _)
                      (∨-least (trans (transpose-∧ ∧-fst) refl)
                               (trans (transpose-∧ ∧-snd) refl))))
