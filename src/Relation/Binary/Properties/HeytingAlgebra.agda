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


⇨-eval : ∀ x y → (x ⇨ y) ∧ x ≤ y
⇨-eval x y = transposeʳ _ _ _ refl

⇨-∧-distribˡ : _⇨_ DistributesOverˡ _∧_
⇨-∧-distribˡ x y z = antisym
  (let y∧z≤y , y∧z≤z , _ = infimum y z
   in ∧-greatest _ _ _
                 (transposeˡ _ _ _ (trans (⇨-eval _ _) y∧z≤y))
                 (transposeˡ _ _ _ (trans (⇨-eval _ _) y∧z≤z)))
   (transposeˡ _ _ _
               (begin ((x ⇨ y) ∧ (x ⇨ z)) ∧ x       ≈⟨ ∧-cong ≈-refl (≈-sym (∧-idempotent _)) ⟩
                      ((x ⇨ y) ∧ (x ⇨ z)) ∧ x ∧ x   ≈⟨ ≈-sym (∧-assoc _ _ _) ⟩
                      (((x ⇨ y) ∧ (x ⇨ z)) ∧ x) ∧ x ≈⟨ ∧-cong (∧-assoc _ _ _) ≈-refl ⟩
                      ((x ⇨ y) ∧ (x ⇨ z) ∧ x) ∧ x   ≈⟨ ∧-cong (∧-cong ≈-refl (∧-comm _ _)) ≈-refl ⟩
                      ((x ⇨ y) ∧ x ∧ (x ⇨ z)) ∧ x   ≈⟨ ∧-cong (≈-sym (∧-assoc _ _ _)) ≈-refl ⟩
                      (((x ⇨ y) ∧ x) ∧ (x ⇨ z)) ∧ x ≈⟨ ∧-assoc _ _ _ ⟩
                      ((x ⇨ y) ∧ x) ∧ (x ⇨ z) ∧ x   ≤⟨ ∧-monotonic (⇨-eval _ _) (⇨-eval _ _) ⟩
                      y ∧ z                         ∎))
   where open PoR poset

∧-∨-distribˡ : _∧_ DistributesOverˡ _∨_
∧-∨-distribˡ x y z = antisym
  (trans (reflexive (∧-comm _ _))
         (transposeʳ _ _ _ (∨-least _ _ _
                     (transposeˡ _ _ _
                                 (trans (reflexive (∧-comm _ _)) (∨-fst _ _)))
                     (transposeˡ _ _ _
                                 (trans (reflexive (∧-comm _ _)) (∨-snd _ _))))))

  let x∧y≤x  , x∧y≤y , _ = infimum x y
      x∧z≤x  , x∧z≤z , _ = infimum x z
      y≤y∨z  , z≤y∨z , _ = supremum y z
  in ∧-greatest _ _ _
                (∨-least _ _ _ x∧y≤x x∧z≤x)
                (∨-least _ _ _ (trans x∧y≤y y≤y∨z)
                               (trans x∧z≤z z≤y∨z))


isDistributiveLattice : IsDistributiveLattice _≈_ _≤_ _∨_ _∧_
isDistributiveLattice = record { isLattice = isLattice ; ∧-∨-distribˡ = ∧-∨-distribˡ }

distributiveLattice : DistributiveLattice _ _ _
distributiveLattice = record { isDistributiveLattice = isDistributiveLattice }

∨-⇨-distrib : ∀ x y z → x ∨ y ⇨ z ≈ (x ⇨ z) ∧ (y ⇨ z)
∨-⇨-distrib x y z = antisym
  (let x≤x∨y , y≤x∨y , _ = supremum x y
   in ∧-greatest _ _ _
                 (transposeˡ _ _ _ (trans (∧-monotonic refl x≤x∨y) (⇨-eval _ _)))
                 (transposeˡ _ _ _ (trans (∧-monotonic refl y≤x∨y) (⇨-eval _ _))))
  (transposeˡ _ _ _
              (trans (reflexive (∧-∨-distribˡ _ _ _))
                     (∨-least _ _ _ (trans (transposeʳ _ _ _ (∧-fst _ _)) refl)
                                    (trans (transposeʳ _ _ _ (∧-snd _ _)) refl))))
