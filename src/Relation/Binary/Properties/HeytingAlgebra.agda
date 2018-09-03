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

private
  ≈-setoid : Setoid _ _
  ≈-setoid = record { isEquivalence = isEquivalence }

open Setoid ≈-setoid using () renaming (sym to ≈-sym; refl to ≈-refl)


⇨-eval : ∀ x y → (x ⇨ y) ∧ x ≤ y
⇨-eval x y = let _ , transposeʳ = exponential (x ⇨ y) x y
             in transposeʳ refl

⇨-∧-distribʳ : _⇨_ DistributesOverˡ _∧_
⇨-∧-distribʳ x y z = antisym
  (let _     , _     , least = infimum (x ⇨ y) (x ⇨ z)
       app-y , _             = exponential (x ⇨ y ∧ z) x y
       app-z , _             = exponential (x ⇨ y ∧ z) x z
       y∧z≤y , y∧z≤z , _     = infimum y z
   in least _ (app-y (trans (⇨-eval x (y ∧ z)) y∧z≤y))
              (app-z (trans (⇨-eval x (y ∧ z)) y∧z≤z)))
   let app   , _             = exponential ((x ⇨ y) ∧ (x ⇨ z)) x (y ∧ z)
   in app (begin ((x ⇨ y) ∧ (x ⇨ z)) ∧ x       ≈⟨ ∧-cong ≈-refl (≈-sym (∧-idempotent _)) ⟩
                 ((x ⇨ y) ∧ (x ⇨ z)) ∧ x ∧ x   ≈⟨ ≈-sym (∧-assoc _ _ _) ⟩
                 (((x ⇨ y) ∧ (x ⇨ z)) ∧ x) ∧ x ≈⟨ ∧-cong (∧-assoc _ _ _) ≈-refl ⟩
                 ((x ⇨ y) ∧ (x ⇨ z) ∧ x) ∧ x   ≈⟨ ∧-cong (∧-cong ≈-refl (∧-comm _ _)) ≈-refl ⟩
                 ((x ⇨ y) ∧ x ∧ (x ⇨ z)) ∧ x   ≈⟨ ∧-cong (≈-sym (∧-assoc _ _ _)) ≈-refl ⟩
                 (((x ⇨ y) ∧ x) ∧ (x ⇨ z)) ∧ x ≈⟨ ∧-assoc _ _ _ ⟩
                 ((x ⇨ y) ∧ x) ∧ (x ⇨ z) ∧ x   ≤⟨ ∧-monotonic (⇨-eval _ _) (⇨-eval _ _) ⟩
                 y ∧ z                         ∎)
   where open PoR poset

∧-∨-distribˡ : _∧_ DistributesOverˡ _∨_
∧-∨-distribˡ x y z = antisym
  (let rhs                      = (x ∧ y ∨ x ∧ z)
       _     , transposeʳ       = exponential (y ∨ z) x rhs
       _     , _     , greatest = supremum y z
       app-y , _                = exponential y x rhs
       app-z , _                = exponential z x rhs
   in trans (reflexive (∧-comm _ _))
            (transposeʳ (greatest _ (app-y (trans (reflexive (∧-comm _ _))
                                                  (proj₁ (supremum _ _))))
                                    (app-z (trans (reflexive (∧-comm _ _))
                                                  (proj₁ (proj₂ (supremum _ _))))))))
  let _      , _     , least    = infimum x (y ∨ z)
      _      , _     , greatest = supremum (x ∧ y) (x ∧ z)
      x∧y≤x  , x∧y≤y , _        = infimum x y
      x∧z≤x  , x∧z≤z , _        = infimum x z
      y≤y∨z  , z≤y∨z , _        = supremum y z
  in least _ (greatest _ x∧y≤x x∧z≤x)
             (greatest _ (trans x∧y≤y y≤y∨z)
                         (trans x∧z≤z z≤y∨z))


isDistributiveLattice : IsDistributiveLattice _≈_ _≤_ _∨_ _∧_
isDistributiveLattice = record { isLattice = isLattice ; ∧-∨-distribˡ = ∧-∨-distribˡ }

distributiveLattice : DistributiveLattice _ _ _
distributiveLattice = record { isDistributiveLattice = isDistributiveLattice }

∨-⇨-distrib : ∀ x y z → x ∨ y ⇨ z ≈ (x ⇨ z) ∧ (y ⇨ z)
∨-⇨-distrib x y z = antisym
  (let _     , _     , least = infimum (x ⇨ z) (y ⇨ z)
       app-x , _             = exponential (x ∨ y ⇨ z) x z
       app-y , _             = exponential (x ∨ y ⇨ z) y z
       x≤x∨y , y≤x∨y , _     = supremum x y
   in least _ (app-x (trans (∧-monotonic refl x≤x∨y) (⇨-eval _ _)))
              (app-y (trans (∧-monotonic refl y≤x∨y) (⇨-eval _ _))))
   let app   , _             = exponential ((x ⇨ z) ∧ (y ⇨ z)) (x ∨ y) z
   in app (trans (reflexive (∧-∨-distribˡ _ _ _))
          ((greatest (supremum _ _) _ (trans (transposeʳ (exponential _ _ _) (proj₁ (infimum _ _)))
                                             refl)
                                      (trans (transposeʳ (exponential _ _ _) (proj₁ (proj₂ (infimum _ _))))
                                             refl))))
  where greatest : ∀ {A B : Set ℓ₂} {C : Set (c ⊔ ℓ₂)} → A × B × C → C
        greatest (_ , _ , c) = c
        transposeʳ = proj₂
