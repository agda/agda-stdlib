------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise equality over lists parameterised by a setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Equality.Setoid {a ℓ} (S : Setoid a ℓ) where
open import Algebra.Core using (Op₂)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; length; map; foldr; _++_; concat;
  tabulate; filter; _ʳ++_; reverse)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise)
open import Data.List.Relation.Unary.Unique.Setoid S using (Unique)
open import Function.Base using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (_⇒_; _Preserves_⟶_) renaming (Rel to Rel₂)
open import Relation.Binary.Definitions using (Transitive; Symmetric; Reflexive; _Respects_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Properties.Setoid S using (≉-resp₂)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Unary as U using (Pred)

open Setoid S renaming (Carrier to A)

private
  variable
    p q : Level
    ws xs xs′ ys ys′ zs : List A
    xss yss : List (List A)

------------------------------------------------------------------------
-- Definition of equality
------------------------------------------------------------------------

infix 4 _≋_

_≋_ : Rel₂ (List A) (a ⊔ ℓ)
_≋_ = Pointwise _≈_

open PW public
  using ([]; _∷_)

------------------------------------------------------------------------
-- Relational properties
------------------------------------------------------------------------

≋-setoid : Setoid _ _
≋-setoid = PW.setoid S

open Setoid ≋-setoid public
  using ()
  renaming ( refl to ≋-refl
           ; reflexive to ≋-reflexive
           ; sym to ≋-sym
           ; trans to ≋-trans
           ; isEquivalence to ≋-isEquivalence)

------------------------------------------------------------------------
-- Relationships to predicates
------------------------------------------------------------------------

open PW public
  using () renaming
  ( Any-resp-Pointwise      to Any-resp-≋
  ; All-resp-Pointwise      to All-resp-≋
  ; AllPairs-resp-Pointwise to AllPairs-resp-≋
  )

Unique-resp-≋ : Unique Respects _≋_
Unique-resp-≋ = AllPairs-resp-≋ ≉-resp₂

------------------------------------------------------------------------
-- List operations
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
-- foldr

foldr⁺ : ∀ {_•_ : Op₂ A} {_◦_ : Op₂ A} →
         (∀ {w x y z} → w ≈ x → y ≈ z → (w • y) ≈ (x ◦ z)) →
         ∀ {xs ys e f} → e ≈ f → xs ≋ ys →
         foldr _•_ e xs ≈ foldr _◦_ f ys
foldr⁺ ∙⇔◦ e≈f xs≋ys = PW.foldr⁺ ∙⇔◦ e≈f xs≋ys

------------------------------------------------------------------------
-- _++_

++⁺ : ws ≋ xs → ys ≋ zs → ws ++ ys ≋ xs ++ zs
++⁺ = PW.++⁺

++⁺ˡ : ∀ xs → ys ≋ zs → xs ++ ys ≋ xs ++ zs
++⁺ˡ xs = PW.++⁺ˡ refl xs

++⁺ʳ : ∀ zs → ws ≋ xs → ws ++ zs ≋ xs ++ zs
++⁺ʳ zs = PW.++⁺ʳ refl zs

++-cancelˡ : ∀ xs {ys zs} → xs ++ ys ≋ xs ++ zs → ys ≋ zs
++-cancelˡ xs = PW.++-cancelˡ xs

++-cancelʳ : ∀ {xs} ys zs → ys ++ xs ≋ zs ++ xs → ys ≋ zs
++-cancelʳ = PW.++-cancelʳ

------------------------------------------------------------------------
-- concat

concat⁺ : Pointwise _≋_ xss yss → concat xss ≋ concat yss
concat⁺ = PW.concat⁺

------------------------------------------------------------------------
-- tabulate

module _ {n} {f g : Fin n → A}
  where

  tabulate⁺ : (∀ i → f i ≈ g i) → tabulate f ≋ tabulate g
  tabulate⁺ = PW.tabulate⁺

  tabulate⁻ : tabulate f ≋ tabulate g → (∀ i → f i ≈ g i)
  tabulate⁻ = PW.tabulate⁻

------------------------------------------------------------------------
-- filter

module _ {P : Pred A p} (P? : U.Decidable P) (resp : P Respects _≈_)
  where

  filter⁺ : xs ≋ ys → filter P? xs ≋ filter P? ys
  filter⁺ xs≋ys = PW.filter⁺ P? P? resp (resp ∘ sym) xs≋ys

------------------------------------------------------------------------
-- reverse

ʳ++⁺ : xs ≋ xs′ → ys ≋ ys′ → xs ʳ++ ys ≋ xs′ ʳ++ ys′
ʳ++⁺ = PW.ʳ++⁺

reverse⁺ : xs ≋ ys → reverse xs ≋ reverse ys
reverse⁺ = PW.reverse⁺
