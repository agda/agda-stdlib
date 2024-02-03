------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles

module Algebra.Properties.Group {g₁ g₂} (G : Group g₁ g₂) where

open Group G
open import Algebra.Definitions _≈_
import Algebra.Properties.Loop as LoopProperties
import Algebra.Properties.Quasigroup as QuasigroupProperties
open import Algebra.Structures _≈_ using (IsLoop; IsQuasigroup)
open import Relation.Binary.Reasoning.Setoid setoid
open import Function.Base using (_$_)
open import Data.Product.Base using (_,_; proj₂)

\\-cong₂ : Congruent₂ _\\_
\\-cong₂ x≈y u≈v = ∙-cong (⁻¹-cong x≈y) u≈v

//-cong₂ : Congruent₂ _//_
//-cong₂ x≈y u≈v = ∙-cong x≈y (⁻¹-cong u≈v)

leftDividesˡ : ∀ x y → x ∙ (x \\ y) ≈ y
leftDividesˡ x y = begin
  x  ∙ (x \\ y)  ≈⟨ assoc x (x ⁻¹) y ⟨
  x ∙ x ⁻¹ ∙ y   ≈⟨ ∙-congʳ (inverseʳ x) ⟩
  ε ∙ y          ≈⟨ identityˡ y ⟩
  y              ∎

leftDividesʳ : ∀ x y → x \\ x ∙ y ≈ y
leftDividesʳ x y = begin
  x \\ x ∙ y     ≈⟨ assoc (x ⁻¹) x y ⟨
  x ⁻¹ ∙ x ∙ y   ≈⟨ ∙-congʳ (inverseˡ x) ⟩
  ε ∙ y          ≈⟨ identityˡ y ⟩
  y              ∎

rightDividesˡ : ∀ x y → (y // x) ∙ x ≈ y
rightDividesˡ x y = begin
  (y // x) ∙ x    ≈⟨ assoc y (x ⁻¹) x ⟩
  y ∙ (x ⁻¹ ∙ x)  ≈⟨ ∙-congˡ (inverseˡ x) ⟩
  y ∙ ε           ≈⟨ identityʳ y ⟩
  y               ∎

rightDividesʳ : ∀ x y → y ∙ x // x ≈ y
rightDividesʳ x y = begin
  y ∙ x // x    ≈⟨ assoc y x (x ⁻¹) ⟩
  y ∙ (x // x)  ≈⟨ ∙-congˡ (inverseʳ x) ⟩
  y ∙ ε         ≈⟨ identityʳ y ⟩
  y             ∎

isQuasigroup : IsQuasigroup _∙_ _\\_ _//_
isQuasigroup = record
  { isMagma = isMagma
  ; \\-cong = \\-cong₂
  ; //-cong = //-cong₂
  ; leftDivides = leftDividesˡ , leftDividesʳ
  ; rightDivides = rightDividesˡ , rightDividesʳ
  }

quasigroup : Quasigroup _ _
quasigroup = record { isQuasigroup = isQuasigroup }

open QuasigroupProperties quasigroup public
  using ()
  renaming (cancelˡ to ∙-cancelˡ; cancelʳ to ∙-cancelʳ; cancel to ∙-cancel)

isLoop : IsLoop _∙_ _\\_ _//_ ε
isLoop = record { isQuasigroup = isQuasigroup ; identity = identity }

loop : Loop _ _
loop = record { isLoop = isLoop }

open LoopProperties loop public
  using (identityˡ-unique; identityʳ-unique; identity-unique)

ε⁻¹≈ε : ε ⁻¹ ≈ ε
ε⁻¹≈ε = begin
  ε ⁻¹      ≈⟨ identityʳ (ε ⁻¹) ⟨
  ε ⁻¹ ∙ ε  ≈⟨ inverseˡ ε ⟩
  ε         ∎

⁻¹-involutive : ∀ x → x ⁻¹ ⁻¹ ≈ x
⁻¹-involutive x = begin
  x ⁻¹ ⁻¹              ≈⟨ identityʳ _ ⟨
  x ⁻¹ ⁻¹ ∙ ε          ≈⟨ ∙-congˡ $ inverseˡ _ ⟨
  x ⁻¹ ⁻¹ ∙ (x ⁻¹ ∙ x) ≈⟨ leftDividesʳ (x ⁻¹) x ⟩
  x                    ∎

⁻¹-injective : ∀ {x y} → x ⁻¹ ≈ y ⁻¹ → x ≈ y
⁻¹-injective {x} {y} eq = ∙-cancelʳ _ _ _ $ begin
  x ∙ x ⁻¹ ≈⟨ inverseʳ x ⟩
  ε        ≈⟨ inverseʳ y ⟨
  y ∙ y ⁻¹ ≈⟨ ∙-congˡ eq ⟨
  y ∙ x ⁻¹ ∎

⁻¹-anti-homo-∙ : ∀ x y → (x ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x ⁻¹
⁻¹-anti-homo-∙ x y = ∙-cancelˡ _ _ _ $ begin
  x ∙ y ∙ (x ∙ y) ⁻¹    ≈⟨ inverseʳ _ ⟩
  ε                     ≈⟨ inverseʳ _ ⟨
  x ∙ x ⁻¹              ≈⟨ ∙-congʳ (rightDividesʳ y x) ⟨
  (x ∙ y) ∙ y ⁻¹ ∙ x ⁻¹ ≈⟨ assoc (x ∙ y) (y ⁻¹) (x ⁻¹) ⟩
  x ∙ y ∙ (y ⁻¹ ∙ x ⁻¹) ∎

inverseˡ-unique : ∀ x y → x ∙ y ≈ ε → x ≈ y ⁻¹
inverseˡ-unique x y eq = begin
  x              ≈⟨ rightDividesʳ y x ⟨
  (x ∙ y) ∙ y ⁻¹ ≈⟨ ∙-congʳ eq ⟩
       ε  ∙ y ⁻¹ ≈⟨ identityˡ (y ⁻¹) ⟩
            y ⁻¹ ∎

inverseʳ-unique : ∀ x y → x ∙ y ≈ ε → y ≈ x ⁻¹
inverseʳ-unique x y eq = begin
  y       ≈⟨ ⁻¹-involutive y ⟨
  y ⁻¹ ⁻¹ ≈⟨ ⁻¹-cong (inverseˡ-unique x y eq) ⟨
  x ⁻¹    ∎

\\≗flip-//⇒comm : (∀ x y → x \\ y ≈ y // x) → Commutative _∙_
\\≗flip-//⇒comm \\≗//ᵒ x y = begin
  x ∙ y                ≈⟨ ∙-congˡ (rightDividesˡ x y) ⟨
  x ∙ ((y // x) ∙ x)   ≈⟨ ∙-congˡ (∙-congʳ (\\≗//ᵒ x y)) ⟨
  x ∙ ((x \\ y) ∙ x)   ≈⟨ assoc x (x \\ y) x ⟨
  x ∙ (x \\ y) ∙ x     ≈⟨ ∙-congʳ (leftDividesˡ x y) ⟩
  y ∙ x                ∎

comm⇒\\≗flip-// : Commutative _∙_ → ∀ x y → x \\ y ≈ y // x
comm⇒\\≗flip-// comm x y = begin
  x \\ y    ≡⟨⟩
  x ⁻¹ ∙ y  ≈⟨ comm _ _ ⟩
  y ∙ x ⁻¹  ≡⟨⟩
  y // x    ∎
