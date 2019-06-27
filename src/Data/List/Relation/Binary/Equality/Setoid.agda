------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise equality over lists parameterised by a setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Binary.Equality.Setoid {a ℓ} (S : Setoid a ℓ) where

open import Data.Fin
open import Data.List.Base
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise)
open import Function using (_∘_)
open import Level
open import Relation.Binary renaming (Rel to Rel₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Unary as U using (Pred)

open Setoid S renaming (Carrier to A)

private
  variable
    p q : Level

------------------------------------------------------------------------
-- Definition of equality
------------------------------------------------------------------------

infix 4 _≋_

_≋_ : Rel₂ (List A) (a ⊔ ℓ)
_≋_ = Pointwise _≈_

open Pointwise public
  using ([]; _∷_)

------------------------------------------------------------------------
-- Relational properties
------------------------------------------------------------------------

≋-refl : Reflexive _≋_
≋-refl = PW.refl refl

≋-reflexive : _≡_ ⇒ _≋_
≋-reflexive P.refl = ≋-refl

≋-sym : Symmetric _≋_
≋-sym = PW.symmetric sym

≋-trans : Transitive _≋_
≋-trans = PW.transitive trans

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = PW.isEquivalence isEquivalence

≋-setoid : Setoid _ _
≋-setoid = PW.setoid S

------------------------------------------------------------------------
-- List Operations
------------------------------------------------------------------------

------------------------------------------------------------------------
-- length

≋-length : ∀ {xs ys} → xs ≋ ys → length xs ≡ length ys
≋-length = PW.Pointwise-length

------------------------------------------------------------------------
-- map

module _ {b ℓ₂} (T : Setoid b ℓ₂) where

  open Setoid T using () renaming (_≈_ to _≈′_)
  private
    _≋′_ = Pointwise _≈′_

  map⁺ : ∀ {f} → f Preserves _≈_ ⟶ _≈′_ →
         ∀ {xs ys} → xs ≋ ys → map f xs ≋′ map f ys
  map⁺ {f} pres xs≋ys = PW.map⁺ f f (PW.map pres xs≋ys)

------------------------------------------------------------------------
-- _++_

++⁺ : ∀ {ws xs ys zs} → ws ≋ xs → ys ≋ zs → ws ++ ys ≋ xs ++ zs
++⁺ = PW.++⁺

++-cancelˡ : ∀ xs {ys zs} → xs ++ ys ≋ xs ++ zs → ys ≋ zs
++-cancelˡ = PW.++-cancelˡ

++-cancelʳ : ∀ {xs} ys zs → ys ++ xs ≋ zs ++ xs → ys ≋ zs
++-cancelʳ = PW.++-cancelʳ

------------------------------------------------------------------------
-- concat

concat⁺ : ∀ {xss yss} → Pointwise _≋_ xss yss → concat xss ≋ concat yss
concat⁺ = PW.concat⁺

------------------------------------------------------------------------
-- tabulate

tabulate⁺ : ∀ {n} {f : Fin n → A} {g : Fin n → A} →
            (∀ i → f i ≈ g i) → tabulate f ≋ tabulate g
tabulate⁺ = PW.tabulate⁺

tabulate⁻ : ∀ {n} {f : Fin n → A} {g : Fin n → A} →
            tabulate f ≋ tabulate g → (∀ i → f i ≈ g i)
tabulate⁻ = PW.tabulate⁻

------------------------------------------------------------------------
-- filter

module _ {P : Pred A p} (P? : U.Decidable P) (resp : P Respects _≈_)
  where

  filter⁺ : ∀ {xs ys} → xs ≋ ys → filter P? xs ≋ filter P? ys
  filter⁺ xs≋ys = PW.filter⁺ P? P? resp (resp ∘ sym) xs≋ys

------------------------------------------------------------------------
-- filter

reverse⁺ : ∀ {xs ys} → xs ≋ ys → reverse xs ≋ reverse ys
reverse⁺ = PW.reverse⁺
