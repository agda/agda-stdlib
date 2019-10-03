------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Pointwise
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Relation.Binary.Pointwise.Properties where

open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using () renaming (Pointwise to ×-Pointwise)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec.Functional as VF hiding (map)
open import Data.Vec.Functional.Relation.Binary.Pointwise
open import Function
open import Level using (Level)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

private
  variable
    a a′ a″ b b′ b″ r s t ℓ : Level
    A : Set a
    B : Set b
    A′ : Set a′
    B′ : Set b′
    A″ : Set a″
    B″ : Set b″

------------------------------------------------------------------------
-- Relational properties

module _ {R : Rel A ℓ} where

  refl : Reflexive R → ∀ {n} → Reflexive (Pointwise R {n = n})
  refl r i = r

  sym : Symmetric R → ∀ {n} → Symmetric (Pointwise R {n = n})
  sym s xsys i = s (xsys i)

  trans : Transitive R → ∀ {n} → Transitive (Pointwise R {n = n})
  trans t xsys yszs i = t (xsys i) (yszs i)

  decidable : Decidable R → ∀ {n} → Decidable (Pointwise R {n = n})
  decidable r? xs ys = all? λ i → r? (xs i) (ys i)

------------------------------------------------------------------------
-- map

module _ {R : REL A B r} {S : REL A′ B′ s} {f : A → A′} {g : B → B′} where

  map⁺ : (∀ {x y} → R x y → S (f x) (g y)) →
         ∀ {n} {xs : Vector A n} {ys : Vector B n} →
         Pointwise R xs ys → Pointwise S (VF.map f xs) (VF.map g ys)
  map⁺ f rs i = f (rs i)

------------------------------------------------------------------------
-- head

module _ (R : REL A B r) {n} {xs : Vector A (suc n)} {ys} where

  head⁺ : Pointwise R xs ys → R (head xs) (head ys)
  head⁺ rs = rs zero

------------------------------------------------------------------------
-- tail

module _ (R : REL A B r) {n} {xs : Vector A (suc n)} {ys} where

  tail⁺ : Pointwise R xs ys → Pointwise R (tail xs) (tail ys)
  tail⁺ rs = rs ∘ suc

------------------------------------------------------------------------
-- _++_

module _ (R : REL A B r) where

  ++⁺ : ∀ {m n xs ys xs′ ys′} →
        Pointwise R {n = m} xs ys → Pointwise R {n = n} xs′ ys′ →
        Pointwise R (xs ++ xs′) (ys ++ ys′)
  ++⁺ {m} rs rs′ i with splitAt m i
  ... | inj₁ i′ = rs i′
  ... | inj₂ j′ = rs′ j′

  ++⁻ˡ : ∀ {m n} (xs : Vector A m) (ys : Vector B m) {xs′ ys′} →
         Pointwise R (xs ++ xs′) (ys ++ ys′) → Pointwise R xs ys
  ++⁻ˡ {m} {n} _ _ rs i with rs (inject+ n i)
  ... | r rewrite splitAt-inject+ m n i = r

  ++⁻ʳ : ∀ {m n} (xs : Vector A m) (ys : Vector B m) {xs′ ys′} →
         Pointwise R (xs ++ xs′) (ys ++ ys′) → Pointwise R xs′ ys′
  ++⁻ʳ {m} {n} _ _ rs i with rs (raise m i)
  ... | r rewrite splitAt-raise m n i = r

  ++⁻ : ∀ {m n} xs ys {xs′ ys′} →
        Pointwise R (xs ++ xs′) (ys ++ ys′) →
        Pointwise R {n = m} xs ys × Pointwise R {n = n} xs′ ys′
  ++⁻ _ _ rs = ++⁻ˡ _ _ rs , ++⁻ʳ _ _ rs

------------------------------------------------------------------------
-- replicate

module _ {R : REL A B r} {x y n} where

  replicate⁺ : R x y → Pointwise R {n = n} (replicate x) (replicate y)
  replicate⁺ = const

------------------------------------------------------------------------
-- _⊛_

module _ {R : REL A B r} {S : REL A′ B′ s} {n} where

  ⊛⁺ : ∀ {fs : Vector (A → A′) n} {gs : Vector (B → B′) n} →
       Pointwise (λ f g → ∀ {x y} → R x y → S (f x) (g y)) fs gs →
       ∀ {xs ys} → Pointwise R xs ys → Pointwise S (fs ⊛ xs) (gs ⊛ ys)
  ⊛⁺ rss rs i = (rss i) (rs i)

------------------------------------------------------------------------
-- zipWith

module _ {R : REL A B r} {S : REL A′ B′ s} {T : REL A″ B″ t} where

  zipWith⁺ : ∀ {n xs ys xs′ ys′ f f′} →
             (∀ {x y x′ y′} → R x y → S x′ y′ → T (f x x′) (f′ y y′)) →
             Pointwise R xs ys → Pointwise S xs′ ys′ →
             Pointwise T (zipWith f xs xs′) (zipWith f′ {n = n} ys ys′)
  zipWith⁺ t rs ss i = t (rs i) (ss i)

------------------------------------------------------------------------
-- zip

module _ {R : REL A B r} {S : REL A′ B′ s} {n xs ys xs′ ys′} where

  zip⁺ : Pointwise R xs ys → Pointwise S xs′ ys′ →
         Pointwise (λ xx yy → R (proj₁ xx) (proj₁ yy) × S (proj₂ xx) (proj₂ yy))
                   (zip xs xs′) (zip {n = n} ys ys′)
  zip⁺ rs ss i = rs i , ss i

  zip⁻ : Pointwise (λ xx yy → R (proj₁ xx) (proj₁ yy) × S (proj₂ xx) (proj₂ yy))
                   (zip xs xs′) (zip {n = n} ys ys′) →
         Pointwise R xs ys × Pointwise S xs′ ys′
  zip⁻ rss = proj₁ ∘ rss , proj₂ ∘ rss
