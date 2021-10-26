open import Relation.Binary

module Relation.Binary.Apartness where

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (sym to ≡-sym)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import Data.Product using (_×_)


module _ {a ℓ} {A : Set a} (_#_ : Rel A ℓ) where

  _¬#_ : A → A → Set ℓ
  x ¬# y = ¬ (x # y)


  irrefl⇒refl-¬ : Irreflexive _≡_ _#_ → Reflexive _¬#_
  irrefl⇒refl-¬ irr = irr _≡_.refl


  sym⇒sym-¬ : Symmetric _#_ → Symmetric _¬#_
  sym⇒sym-¬ sym# x¬#y y#x = x¬#y (sym# y#x)


  Comparison : Set _
  Comparison = ∀ {x y z} → x # z → (x # y) ⊎ (y # z)


  comp⇒trans-¬ : Comparison → Transitive _¬#_
  comp⇒trans-¬ comp x¬#y y¬#z x#z = [ x¬#y , y¬#z ]′ (comp x#z)


  record IsApartness : Set (a ⊔ ℓ) where
    field
      irrefl : Irreflexive _≡_ _#_
      sym    : Symmetric _#_
      comp   : Comparison


    ¬#-equiv : IsEquivalence _¬#_
    ¬#-equiv = record { refl = irrefl⇒refl-¬ irrefl ; sym = sym⇒sym-¬ sym ; trans = comp⇒trans-¬ comp }
    

  Tight : Set _
  Tight = ∀ {x y} → (x # y) × (y # x) → x ≡ y


module _ {a} {A : Set a} where

  -- _≢_ : A → A → Set _
  -- x ≢ y = ¬ (x ≡ y)

  ≢-irrefl : Irreflexive {A = A} _≡_ _≢_
  ≢-irrefl x≡y x≢y = x≢y x≡y

  ≢-sym : Symmetric {A = A} _≢_
  ≢-sym x≢y y≡x = x≢y (≡-sym y≡x)

  -- I think these require decidability.

  ≢-comp : Comparison {A = A} _≢_
  ≢-comp {x = x} {y = y} {z = z} x≢z = inj₁ {!   !}

  ≢-apart : IsApartness {A = A} _≢_
  ≢-apart = record { irrefl = ≢-irrefl ; sym = ≢-sym ; comp = {!   !} } 