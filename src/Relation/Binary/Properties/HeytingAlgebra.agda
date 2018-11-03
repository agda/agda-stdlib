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
open import Function using (_$_; flip; _∘_)

open HeytingAlgebra L
open import Algebra.FunctionProperties _≈_
open import Relation.Binary.PartialOrderReasoning poset
open import Relation.Binary.Properties.MeetSemilattice meetSemilattice
open import Relation.Binary.Properties.JoinSemilattice joinSemilattice
import Relation.Binary.Properties.BoundedMeetSemilattice boundedMeetSemilattice as BM
open import Relation.Binary.Properties.Lattice lattice
open import Relation.Binary.Properties.BoundedLattice boundedLattice
open import Relation.Binary.SetoidReasoning
  renaming (_∎ to _▯; _≈⟨_⟩_ to _≈≈⟨_⟩_)
open IsEquivalence isEquivalence using ()
  renaming (sym to ≈-sym; refl to ≈-refl; trans to ≈-trans)

------------------------------------------------------------------------
-- Useful lemmas

⇨-eval : ∀ {x y} → (x ⇨ y) ∧ x ≤ y
⇨-eval {x} {y} = transpose-∧ refl

swap-transpose-⇨ : ∀ {x y w} → x ∧ w ≤ y → w ≤ x ⇨ y
swap-transpose-⇨ x∧w≤y = transpose-⇨ $ trans (reflexive $ ∧-comm _ _) x∧w≤y

------------------------------------------------------------------------
-- Properties of exponential

⇨-unit : ∀ {x} → x ⇨ x ≈ ⊤
⇨-unit = antisym (maximum _) (transpose-⇨ $ reflexive $ BM.identityˡ _)

y≤x⇨y : ∀ {x y} → y ≤ x ⇨ y
y≤x⇨y = transpose-⇨ (x∧y≤x _ _)

⇨-drop : ∀ {x y} → (x ⇨ y) ∧ y ≈ y
⇨-drop = antisym (x∧y≤y _ _) (∧-greatest y≤x⇨y refl)

⇨-app : ∀ {x y} → (x ⇨ y) ∧ x ≈ y ∧ x
⇨-app = antisym (∧-greatest ⇨-eval (x∧y≤y _ _)) (∧-monotonic y≤x⇨y refl)

⇨ʳ-covariant : ∀ {x} → (x ⇨_) Preserves _≤_ ⟶ _≤_
⇨ʳ-covariant {x} {y} {z} y≤z = transpose-⇨ (trans ⇨-eval y≤z)

⇨ˡ-contravariant : ∀ {x} → (_⇨ x) Preserves (flip _≤_) ⟶ _≤_
⇨ˡ-contravariant {x} {y} {z} z≤y = transpose-⇨ (trans (∧-monotonic refl z≤y) ⇨-eval)

⇨-relax : _⇨_ Preserves₂ (flip _≤_) ⟶ _≤_ ⟶ _≤_
⇨-relax {x} {y} {u} {v} y≤x u≤v = begin
  x ⇨ u ≤⟨ ⇨ʳ-covariant u≤v ⟩
  x ⇨ v ≤⟨ ⇨ˡ-contravariant y≤x ⟩
  y ⇨ v ∎

⇨-cong : _⇨_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
⇨-cong x≈y u≈v = antisym (⇨-relax (reflexive $ ≈-sym x≈y) (reflexive u≈v))
                         (⇨-relax (reflexive x≈y) (reflexive $ ≈-sym u≈v))

⇨-applyˡ : ∀ {w x y} → w ≤ x → (x ⇨ y) ∧ w ≤ y
⇨-applyˡ = transpose-∧ ∘ ⇨ˡ-contravariant

⇨-applyʳ : ∀ {w x y} → w ≤ x → w ∧ (x ⇨ y) ≤ y
⇨-applyʳ w≤x = trans (reflexive (∧-comm _ _)) (⇨-applyˡ w≤x)

⇨-curry : ∀ {x y z} → x ∧ y ⇨ z ≈ x ⇨ y ⇨ z
⇨-curry = antisym (transpose-⇨ $ transpose-⇨ $ trans (reflexive $ ∧-assoc _ _ _) ⇨-eval)
                  (transpose-⇨ $ trans (reflexive $ ≈-sym $ ∧-assoc _ _ _)
                                       (transpose-∧ $ ⇨-applyˡ refl))

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

------------------------------------------------------------------------
-- Heyting algebras can define pseudo-complement

infix 8 ¬_

¬_ : Op₁ Carrier
¬ x = x ⇨ ⊥

x≤¬¬x : ∀ x → x ≤ ¬ ¬ x
x≤¬¬x x = transpose-⇨ (trans (reflexive (∧-comm _ _)) ⇨-eval)

------------------------------------------------------------------------
-- De-Morgan laws

de-morgan₁ : ∀ x y → ¬ (x ∨ y) ≈ ¬ x ∧ ¬ y
de-morgan₁ x y = ⇨-distribˡ-∨-∧ _ _ _

de-morgan₂-≤ : ∀ x y → ¬ (x ∧ y) ≤ ¬ ¬ (¬ x ∨ ¬ y)
de-morgan₂-≤ x y = transpose-⇨ $ begin
  ¬ (x ∧ y) ∧ ¬ (¬ x ∨ ¬ y)     ≈⟨ ∧-cong ⇨-curry (de-morgan₁ _ _) ⟩
  (x ⇨ ¬ y) ∧ ¬ ¬ x ∧ ¬ ¬ y     ≈⟨ ∧-cong ≈-refl (∧-comm _ _) ⟩
  (x ⇨ ¬ y) ∧ ¬ ¬ y ∧ ¬ ¬ x     ≈⟨ ≈-sym $ ∧-assoc _ _ _ ⟩
  ((x ⇨ ¬ y) ∧ ¬ ¬ y) ∧ ¬ ¬ x   ≤⟨ ⇨-applyʳ $ transpose-⇨ $
    begin
      ((x ⇨ ¬ y) ∧ ¬ ¬ y) ∧ x   ≈⟨ ∧-cong (∧-comm _ _) ≈-refl ⟩
      ((¬ ¬ y) ∧ (x ⇨ ¬ y)) ∧ x ≈⟨ ∧-assoc _ _ _ ⟩
      (¬ ¬ y) ∧ (x ⇨ ¬ y) ∧ x   ≤⟨ ∧-monotonic refl ⇨-eval ⟩
      ¬ ¬ y ∧ ¬ y               ≤⟨ ⇨-eval ⟩
      ⊥                         ∎ ⟩
  ⊥                             ∎

de-morgan₂-≥ : ∀ x y → ¬ ¬ (¬ x ∨ ¬ y) ≤ ¬ (x ∧ y)
de-morgan₂-≥ x y = transpose-⇨ $ ⇨-applyˡ $ transpose-⇨ $ begin
  (x ∧ y) ∧ (¬ x ∨ ¬ y)         ≈⟨ ∧-distribˡ-∨ _ _ _ ⟩
  (x ∧ y) ∧ ¬ x ∨ (x ∧ y) ∧ ¬ y ≤⟨ ∨-monotonic (⇨-applyʳ (x∧y≤x _ _))
                                               (⇨-applyʳ (x∧y≤y _ _)) ⟩
  ⊥ ∨ ⊥                         ≈⟨ ∨-idempotent _ ⟩
  ⊥                             ∎

de-morgan₂ : ∀ x y → ¬ (x ∧ y) ≈ ¬ ¬ (¬ x ∨ ¬ y)
de-morgan₂ x y = antisym (de-morgan₂-≤ x y) (de-morgan₂-≥ x y)

weak-lem : ∀ {x} → ¬ ¬ (¬ x ∨ x) ≈ ⊤
weak-lem {x} = begin⟨ setoid ⟩
  ¬ ¬ (¬ x ∨ x)   ≈≈⟨ ⇨-cong (de-morgan₁ _ _) ≈-refl ⟩
  ¬ (¬ ¬ x ∧ ¬ x) ≈≈⟨ ⇨-cong ⇨-app ≈-refl ⟩
  ⊥ ∧ (x ⇨ ⊥) ⇨ ⊥ ≈≈⟨ ⇨-cong (⊥-∧-zeroˡ _) ≈-refl ⟩
  ⊥ ⇨ ⊥           ≈≈⟨ ⇨-unit ⟩
  ⊤               ▯
