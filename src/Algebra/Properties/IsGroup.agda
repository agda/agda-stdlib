------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Structures.IsGroup using (IsGroup)

module Algebra.Properties.IsGroup
  {a ℓ} {A} {_≈_} {_∙_} {ε} {_⁻¹}
  (isGroup : IsGroup {a = a} {ℓ = ℓ} {A = A} _≈_ _∙_ ε _⁻¹)
  where

open import Data.Product.Base using (_,_)
open import Function.Base using (_$_)
open import Function.Definitions using (Injective)

open IsGroup isGroup
open import Algebra.Consequences.Setoid setoid
open import Algebra.Definitions _≈_
import Algebra.Properties.IsLoop as LoopProperties
import Algebra.Properties.IsQuasigroup as QuasigroupProperties
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Groups are quasi-groups

open QuasigroupProperties isQuasigroup public
  using (x≈z//y; y≈x\\z)
  renaming (cancelˡ to ∙-cancelˡ; cancelʳ to ∙-cancelʳ; cancel to ∙-cancel)

------------------------------------------------------------------------
-- Groups are loops

open LoopProperties isLoop public
  using (identityˡ-unique; identityʳ-unique; identity-unique)

------------------------------------------------------------------------
-- Other properties

inverseˡ-unique : ∀ x y → (x ∙ y) ≈ ε → x ≈ (y ⁻¹)
inverseˡ-unique x y eq = trans (x≈z//y x y ε eq) (identityˡ _)

inverseʳ-unique : ∀ x y → (x ∙ y) ≈ ε → y ≈ (x ⁻¹)
inverseʳ-unique x y eq = trans (y≈x\\z x y ε eq) (identityʳ _)

ε⁻¹≈ε : (ε ⁻¹) ≈ ε
ε⁻¹≈ε = sym $ inverseˡ-unique _ _ (identityˡ ε)

⁻¹-selfInverse : SelfInverse _⁻¹
⁻¹-selfInverse {x} {y} eq = sym $ inverseˡ-unique x y $ begin
  x ∙ y    ≈⟨ ∙-congˡ eq ⟨
  x ∙ (x ⁻¹) ≈⟨ inverseʳ x  ⟩
  ε        ∎

⁻¹-involutive : Involutive _⁻¹
⁻¹-involutive = selfInverse⇒involutive ⁻¹-selfInverse

x∙y⁻¹≈ε⇒x≈y : ∀ x y → (x ∙ (y ⁻¹)) ≈ ε → x ≈ y
x∙y⁻¹≈ε⇒x≈y x y x∙y⁻¹≈ε = begin
  x         ≈⟨ inverseˡ-unique x (y ⁻¹) x∙y⁻¹≈ε ⟩
  (y ⁻¹) ⁻¹   ≈⟨ ⁻¹-involutive y ⟩
  y         ∎

x≈y⇒x∙y⁻¹≈ε : ∀ {x y} → x ≈ y → (x ∙ (y ⁻¹)) ≈ ε
x≈y⇒x∙y⁻¹≈ε {x} {y} x≈y = begin
  x ∙ (y ⁻¹) ≈⟨ ∙-congʳ x≈y ⟩
  y ∙ (y ⁻¹) ≈⟨ inverseʳ y ⟩
  ε        ∎

⁻¹-injective : Injective _≈_ _≈_ _⁻¹
⁻¹-injective = selfInverse⇒injective ⁻¹-selfInverse

⁻¹-anti-homo-∙ : ∀ x y → ((x ∙ y) ⁻¹) ≈ ((y ⁻¹) ∙ (x ⁻¹))
⁻¹-anti-homo-∙ x y = ∙-cancelˡ _ _ _ $ begin
  (x ∙ y) ∙ ((x ∙ y) ⁻¹)    ≈⟨ inverseʳ _ ⟩
  ε                     ≈⟨ inverseʳ _ ⟨
  x ∙ (x ⁻¹)              ≈⟨ ∙-congʳ (//-rightDividesʳ y x) ⟨
  ((x ∙ y) ∙ (y ⁻¹)) ∙ (x ⁻¹) ≈⟨ assoc (x ∙ y) (y ⁻¹) (x ⁻¹) ⟩
  (x ∙ y) ∙ ((y ⁻¹) ∙ (x ⁻¹)) ∎

⁻¹-anti-homo-// : ∀ x y → ((x // y) ⁻¹) ≈ (y // x)
⁻¹-anti-homo-// x y = begin
  (x // y) ⁻¹      ≡⟨⟩
  (x ∙ (y ⁻¹)) ⁻¹    ≈⟨ ⁻¹-anti-homo-∙ x (y ⁻¹) ⟩
  ((y ⁻¹) ⁻¹) ∙ (x ⁻¹) ≈⟨ ∙-congʳ (⁻¹-involutive y) ⟩
  y ∙ (x ⁻¹)         ≡⟨⟩
  y // x ∎

⁻¹-anti-homo-\\ : ∀ x y → ((x \\ y) ⁻¹) ≈ (y \\ x)
⁻¹-anti-homo-\\ x y = begin
  (x \\ y) ⁻¹      ≡⟨⟩
  ((x ⁻¹) ∙ y) ⁻¹    ≈⟨ ⁻¹-anti-homo-∙ (x ⁻¹) y ⟩
  (y ⁻¹) ∙ ((x ⁻¹) ⁻¹) ≈⟨ ∙-congˡ (⁻¹-involutive x) ⟩
  (y ⁻¹) ∙ x         ≡⟨⟩
  y \\ x ∎

\\≗flip-//⇒comm : (∀ x y → (x \\ y) ≈ (y // x)) → Commutative _∙_
\\≗flip-//⇒comm \\≗//ᵒ x y = begin
  x ∙ y                ≈⟨ ∙-congˡ (//-rightDividesˡ x y) ⟨
  x ∙ ((y // x) ∙ x)   ≈⟨ ∙-congˡ (∙-congʳ (\\≗//ᵒ x y)) ⟨
  x ∙ ((x \\ y) ∙ x)   ≈⟨ assoc x (x \\ y) x ⟨
  (x ∙ (x \\ y)) ∙ x     ≈⟨ ∙-congʳ (\\-leftDividesˡ x y) ⟩
  y ∙ x                ∎

comm⇒\\≗flip-// : Commutative _∙_ → ∀ x y → (x \\ y) ≈ (y // x)
comm⇒\\≗flip-// comm x y = begin
  x \\ y    ≡⟨⟩
  (x ⁻¹) ∙ y  ≈⟨ comm _ _ ⟩
  y ∙ (x ⁻¹)  ≡⟨⟩
  y // x    ∎
