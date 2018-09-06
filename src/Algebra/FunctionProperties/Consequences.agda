------------------------------------------------------------------------
-- The Agda standard library
--
-- Relations between properties of functions, such as associativity and
-- commutativity
------------------------------------------------------------------------

open import Relation.Binary using (Setoid)

module Algebra.FunctionProperties.Consequences
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S
open import Algebra.FunctionProperties _≈_
open import Relation.Binary.EqReasoning S
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)

------------------------------------------------------------------------
-- Existence of identity elements

comm+idˡ⇒idʳ : ∀ {_•_} → Commutative _•_ →
              ∀ {e} → LeftIdentity e _•_ → RightIdentity e _•_
comm+idˡ⇒idʳ {_•_} comm {e} idˡ x = begin
  x • e ≈⟨ comm x e ⟩
  e • x ≈⟨ idˡ x ⟩
  x     ∎

comm+idʳ⇒idˡ : ∀ {_•_} → Commutative _•_ →
              ∀ {e} → RightIdentity e _•_ → LeftIdentity e _•_
comm+idʳ⇒idˡ {_•_} comm {e} idʳ x = begin
  e • x ≈⟨ comm e x ⟩
  x • e ≈⟨ idʳ x ⟩
  x     ∎

------------------------------------------------------------------------
-- Existence of zero elements

comm+zeˡ⇒zeʳ : ∀ {_•_} → Commutative _•_ →
              ∀ {e} → LeftZero e _•_ → RightZero e _•_
comm+zeˡ⇒zeʳ {_•_} comm {e} zeˡ x = begin
  x • e ≈⟨ comm x e ⟩
  e • x ≈⟨ zeˡ x ⟩
  e     ∎

comm+zeʳ⇒zeˡ : ∀ {_•_} → Commutative _•_ →
              ∀ {e} → RightZero e _•_ → LeftZero e _•_
comm+zeʳ⇒zeˡ {_•_} comm {e} zeʳ x = begin
  e • x ≈⟨ comm e x ⟩
  x • e ≈⟨ zeʳ x ⟩
  e     ∎

assoc+distribʳ+idʳ+invʳ⇒zeˡ : ∀ {_+_ _*_ -_ 0#} →
                            Congruent₂ _+_ → Congruent₂ _*_ →
                            Associative _+_ → _*_ DistributesOverʳ _+_ →
                            RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                            LeftZero 0# _*_
assoc+distribʳ+idʳ+invʳ⇒zeˡ {_+_} {_*_} { -_ } {0#}
  +-cong *-cong +-assoc distribʳ idʳ invʳ  x = begin
   0# * x                                ≈⟨ sym (idʳ _) ⟩
   (0# * x) + 0#                         ≈⟨ +-cong refl (sym (invʳ _)) ⟩
   (0# * x) + ((0# * x)  + (-(0# * x)))  ≈⟨ sym (+-assoc _ _ _) ⟩
   ((0# * x) +  (0# * x)) + (-(0# * x))  ≈⟨ +-cong (sym (distribʳ _ _ _)) refl ⟩
   ((0# + 0#) * x) + (-(0# * x))         ≈⟨ +-cong (*-cong (idʳ _) refl) refl ⟩
   (0# * x) + (-(0# * x))                ≈⟨ invʳ _ ⟩
   0#                                    ∎

assoc+distribˡ+idʳ+invʳ⇒zeʳ : ∀ {_+_ _*_ -_ 0#} →
                            Congruent₂ _+_ → Congruent₂ _*_ →
                            Associative _+_ → _*_ DistributesOverˡ _+_ →
                            RightIdentity 0# _+_ → RightInverse 0# -_ _+_ →
                            RightZero 0# _*_
assoc+distribˡ+idʳ+invʳ⇒zeʳ {_+_} {_*_} { -_ } {0#}
  +-cong *-cong +-assoc distribˡ idʳ invʳ  x = begin
    x * 0#                               ≈⟨ sym (idʳ _) ⟩
    (x * 0#) + 0#                        ≈⟨ +-cong refl (sym (invʳ _)) ⟩
    (x * 0#) + ((x * 0#) + (-(x * 0#)))  ≈⟨ sym (+-assoc _ _ _) ⟩
    ((x * 0#) + (x * 0#)) + (-(x * 0#))  ≈⟨ +-cong (sym (distribˡ _ _ _)) refl ⟩
    (x * (0# + 0#)) + (-(x * 0#))        ≈⟨ +-cong (*-cong refl (idʳ _)) refl ⟩
    ((x * 0#) + (-(x * 0#)))             ≈⟨ invʳ _ ⟩
    0#                                   ∎

------------------------------------------------------------------------
-- Existence of inverses

comm+invˡ⇒invʳ : ∀ {e _⁻¹ _•_} → Commutative _•_ →
                LeftInverse e _⁻¹ _•_ → RightInverse e _⁻¹ _•_
comm+invˡ⇒invʳ {e} {_⁻¹} {_•_} comm invˡ x = begin
  x • (x ⁻¹) ≈⟨ comm x (x ⁻¹) ⟩
  (x ⁻¹) • x ≈⟨ invˡ x ⟩
  e          ∎

comm+invʳ⇒invˡ : ∀ {e _⁻¹ _•_} → Commutative _•_ →
                RightInverse e _⁻¹ _•_ → LeftInverse e _⁻¹ _•_
comm+invʳ⇒invˡ {e} {_⁻¹} {_•_} comm invʳ x = begin
  (x ⁻¹) • x ≈⟨ comm (x ⁻¹) x ⟩
  x • (x ⁻¹) ≈⟨ invʳ x ⟩
  e          ∎

------------------------------------------------------------------------
-- Uniqueness of inverses

assoc+id+invʳ⇒invˡ-unique : ∀ {_•_ _⁻¹ ε} →
                           Congruent₂ _•_ → Associative _•_ →
                           Identity ε _•_ → RightInverse ε _⁻¹ _•_ →
                           ∀ x y → (x • y) ≈ ε → x ≈ (y ⁻¹)
assoc+id+invʳ⇒invˡ-unique {_•_} {_⁻¹} {ε} cong assoc id invʳ x y eq =
  begin
    x                ≈⟨ sym (proj₂ id x) ⟩
    x • ε            ≈⟨ cong refl (sym (invʳ y)) ⟩
    x • (y • (y ⁻¹)) ≈⟨ sym (assoc x y (y ⁻¹)) ⟩
    (x • y) • (y ⁻¹) ≈⟨ cong eq refl ⟩
    ε • (y ⁻¹)       ≈⟨ proj₁ id (y ⁻¹) ⟩
    y ⁻¹             ∎

assoc+id+invˡ⇒invʳ-unique : ∀ {_•_ _⁻¹ ε} →
                           Congruent₂ _•_ → Associative _•_ →
                           Identity ε _•_ → LeftInverse ε _⁻¹ _•_ →
                           ∀ x y → (x • y) ≈ ε → y ≈ (x ⁻¹)
assoc+id+invˡ⇒invʳ-unique {_•_} {_⁻¹} {ε} cong assoc id invˡ x y eq =
  begin
    y                ≈⟨ sym (proj₁ id y) ⟩
    ε • y            ≈⟨ cong (sym (invˡ x)) refl ⟩
    ((x ⁻¹) • x) • y ≈⟨ assoc (x ⁻¹) x y ⟩
    (x ⁻¹) • (x • y) ≈⟨ cong refl eq ⟩
    (x ⁻¹) • ε       ≈⟨ proj₂ id (x ⁻¹) ⟩
    x ⁻¹             ∎

------------------------------------------------------------------------
-- Involution of inverses

assoc+id+invʳ⇒invʳ-involutive : ∀ {_•_ _⁻¹ ε} →
                                  Congruent₂ _•_ → Associative _•_ →
                                  Identity ε _•_ → RightInverse ε _⁻¹ _•_ →
                                  Involutive _⁻¹
assoc+id+invʳ⇒invʳ-involutive {_•_} {_⁻¹} {ε} cong assoc id invʳ x =
  sym (assoc+id+invʳ⇒invˡ-unique cong assoc id invʳ x (x ⁻¹) (invʳ _))

assoc+id+invˡ⇒invˡ-involutive : ∀ {_•_ _⁻¹ ε} →
                                  Congruent₂ _•_ → Associative _•_ →
                                  Identity ε _•_ → LeftInverse ε _⁻¹ _•_ →
                                  Involutive _⁻¹
assoc+id+invˡ⇒invˡ-involutive {_•_} {_⁻¹} {ε} cong assoc id invˡ x =
  sym (assoc+id+invˡ⇒invʳ-unique cong assoc id invˡ (x ⁻¹) x (invˡ _))


------------------------------------------------------------------------
-- Distributivity

comm+distrˡ⇒distrʳ : ∀ {_•_ _◦_} → Congruent₂ _◦_ → Commutative _•_ →
                   _•_ DistributesOverˡ _◦_ → _•_ DistributesOverʳ _◦_
comm+distrˡ⇒distrʳ {_•_} {_◦_} cong comm distrˡ x y z = begin
  (y ◦ z) • x       ≈⟨ comm (y ◦ z) x ⟩
  x • (y ◦ z)       ≈⟨ distrˡ x y z ⟩
  (x • y) ◦ (x • z) ≈⟨ cong (comm x y) (comm x z) ⟩
  (y • x) ◦ (z • x) ∎

comm+distrʳ⇒distrˡ : ∀ {_•_ _◦_} → Congruent₂ _◦_ → Commutative _•_ →
                   _•_ DistributesOverʳ _◦_ → _•_ DistributesOverˡ _◦_
comm+distrʳ⇒distrˡ {_•_} {_◦_} cong comm distrˡ x y z = begin
  x • (y ◦ z)       ≈⟨ comm x (y ◦ z) ⟩
  (y ◦ z) • x       ≈⟨ distrˡ x y z ⟩
  (y • x) ◦ (z • x) ≈⟨ cong (comm y x) (comm z x) ⟩
  (x • y) ◦ (x • z) ∎

------------------------------------------------------------------------
-- Cancellativity

comm+cancelˡ⇒cancelʳ : ∀ {_•_} → Commutative _•_ →
                     LeftCancellative _•_ →  RightCancellative _•_
comm+cancelˡ⇒cancelʳ {_•_} comm cancelˡ {x} y z eq = cancelˡ x (begin
  x • y ≈⟨ comm x y ⟩
  y • x ≈⟨ eq ⟩
  z • x ≈⟨ comm z x ⟩
  x • z ∎)

comm+cancelʳ⇒cancelˡ : ∀ {_•_} → Commutative _•_ →
                     RightCancellative _•_ → LeftCancellative _•_
comm+cancelʳ⇒cancelˡ {_•_} comm cancelʳ x {y} {z} eq = cancelʳ y z (begin
  y • x ≈⟨ comm y x ⟩
  x • y ≈⟨ eq ⟩
  x • z ≈⟨ comm x z ⟩
  z • x ∎)

idˡ+invˡ+assoc⇒cancelˡ : ∀ {_•_ _⁻¹ ε} → Congruent₂ _•_ →
                           LeftIdentity ε _•_ →
                           LeftInverse ε _⁻¹ _•_ →
                           Associative _•_ →
                           LeftCancellative _•_
idˡ+invˡ+assoc⇒cancelˡ {_•_} {_⁻¹} {ε} cong idˡ invˡ assoc x {y} {z} eq = begin
  y                ≈⟨ sym (idˡ _) ⟩
  ε • y            ≈⟨ cong (sym (invˡ _)) refl ⟩
  ((x ⁻¹) • x) • y ≈⟨ assoc _ _ _ ⟩
  (x ⁻¹) • (x • y) ≈⟨ cong refl eq ⟩
  (x ⁻¹) • (x • z) ≈⟨ sym (assoc _ _ _) ⟩
  ((x ⁻¹) • x) • z ≈⟨ cong (invˡ _) refl ⟩
  ε • z            ≈⟨ idˡ _ ⟩
  z                ∎

idʳ+invʳ+assoc⇒cancelʳ : ∀ {_•_ _⁻¹ ε} → Congruent₂ _•_ →
                           RightIdentity ε _•_ →
                           RightInverse ε _⁻¹ _•_ →
                           Associative _•_ →
                           RightCancellative _•_
idʳ+invʳ+assoc⇒cancelʳ {_•_} {_⁻¹} {ε} cong idʳ invʳ assoc {x} y z eq = begin
  y                ≈⟨ sym (idʳ _) ⟩
  y • ε            ≈⟨ cong refl (sym (invʳ _)) ⟩
  y • (x • (x ⁻¹)) ≈⟨ sym (assoc _ _ _) ⟩
  (y • x) • (x ⁻¹) ≈⟨ cong eq refl ⟩
  (z • x) • (x ⁻¹) ≈⟨ assoc _ _ _ ⟩
  z • (x • (x ⁻¹)) ≈⟨ cong refl (invʳ _) ⟩
  z • ε            ≈⟨ idʳ _ ⟩
  z                ∎

------------------------------------------------------------------------
-- Selectivity implies idempotence

sel⇒idem : ∀ {_•_} → Selective _•_ → Idempotent _•_
sel⇒idem sel x with sel x x
... | inj₁ x•x≈x = x•x≈x
... | inj₂ x•x≈x = x•x≈x
