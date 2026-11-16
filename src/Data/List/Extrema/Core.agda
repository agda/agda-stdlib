------------------------------------------------------------------------
-- The Agda standard library
--
-- Core lemmas needed to make list argmin/max functions work
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (TotalOrder; Setoid)

module Data.List.Extrema.Core
  {b ℓ₁ ℓ₂} (totalOrder : TotalOrder b ℓ₁ ℓ₂) where

open import Algebra.Construct.LiftedChoice
  using (Lift; sel-≡; preservesᵒ; preservesᵇ ; forcesᵇ)
open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Selective)
import Algebra.Construct.NaturalChoice.Min as Min
  using (_⊓_; x⊓y≈y⇒y≤x; x⊓y≈x⇒x≤y; ⊓-sel; ⊓-isSelectiveMagma)
import Algebra.Construct.NaturalChoice.Max as Max
  using (_⊔_; x⊔y≈y⇒x≤y; x⊔y≈x⇒y≤x; ⊔-sel; ⊔-isSelectiveMagma)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.Definitions using (Trans)


open TotalOrder totalOrder renaming (Carrier to B)
open import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_
  using (_<_; <-≤-trans; ≤-<-trans)

------------------------------------------------------------------------
-- Setup

-- open NonStrictToStrict totalOrder using (_<_; ≤-<-trans; <-≤-trans)

open Max totalOrder
open Min totalOrder

private

  variable
    a : Level
    A : Set a

  <-transʳ : Trans _≤_ _<_ _<_
  <-transʳ = ≤-<-trans trans antisym ≤-respˡ-≈

  <-transˡ : Trans _<_ _≤_ _<_
  <-transˡ = <-≤-trans Eq.sym trans antisym ≤-respʳ-≈

  module _ (f : A → B) where

    lemma₁ : ∀ {x y v} → f x ≤ v → f x ⊓ f y ≈ f y → f y ≤ v
    lemma₁ fx≤v fx⊓fy≈fy = trans (x⊓y≈y⇒y≤x fx⊓fy≈fy) fx≤v

    lemma₂ : ∀ {x y v} → f y ≤ v → f x ⊓ f y ≈ f x → f x ≤ v
    lemma₂ fy≤v fx⊓fy≈fx = trans (x⊓y≈x⇒x≤y fx⊓fy≈fx) fy≤v

    lemma₃ : ∀ {x y v} → f x < v → f x ⊓ f y ≈ f y → f y < v
    lemma₃ fx<v fx⊓fy≈fy = <-transʳ (x⊓y≈y⇒y≤x fx⊓fy≈fy) fx<v

    lemma₄ : ∀ {x y v} → f y < v → f x ⊓ f y ≈ f x → f x < v
    lemma₄ fx<v fx⊓fy≈fy = <-transʳ (x⊓y≈x⇒x≤y fx⊓fy≈fy) fx<v

------------------------------------------------------------------------
-- Definition of lifted max and min

⊓ᴸ : (A → B) → Op₂ A
⊓ᴸ = Lift _≈_ _⊓_ ⊓-sel

⊔ᴸ : (A → B) → Op₂ A
⊔ᴸ = Lift _≈_ _⊔_ ⊔-sel

------------------------------------------------------------------------
-- Properties of ⊓ᴸ

⊓ᴸ-sel : ∀ f → Selective {A = A} _≡_ (⊓ᴸ f)
⊓ᴸ-sel f = sel-≡ ⊓-isSelectiveMagma f

⊓ᴸ-presᵒ-≤v : ∀ f {v} (x y : A) → f x ≤ v ⊎ f y ≤ v → f (⊓ᴸ f x y) ≤ v
⊓ᴸ-presᵒ-≤v f = preservesᵒ ⊓-isSelectiveMagma f (lemma₁ f) (lemma₂ f)

⊓ᴸ-presᵒ-<v : ∀ f {v} (x y : A) → f x < v ⊎ f y < v → f (⊓ᴸ f x y) < v
⊓ᴸ-presᵒ-<v f = preservesᵒ ⊓-isSelectiveMagma f (lemma₃ f) (lemma₄ f)

⊓ᴸ-presᵇ-v≤ : ∀ f {v} {x y : A} → v ≤ f x → v ≤ f y → v ≤ f (⊓ᴸ f x y)
⊓ᴸ-presᵇ-v≤ f {v} = preservesᵇ ⊓-isSelectiveMagma {P = λ x → v ≤ f x} f

⊓ᴸ-presᵇ-v< : ∀ f {v} {x y : A} → v < f x → v < f y → v < f (⊓ᴸ f x y)
⊓ᴸ-presᵇ-v< f {v} = preservesᵇ ⊓-isSelectiveMagma {P = λ x → v < f x} f

⊓ᴸ-forcesᵇ-v≤ : ∀ f {v} (x y : A) → v ≤ f (⊓ᴸ f x y) → v ≤ f x × v ≤ f y
⊓ᴸ-forcesᵇ-v≤ f {v} = forcesᵇ ⊓-isSelectiveMagma f
  (λ v≤fx fx⊓fy≈fx → trans v≤fx (x⊓y≈x⇒x≤y fx⊓fy≈fx))
  (λ v≤fy fx⊓fy≈fy → trans v≤fy (x⊓y≈y⇒y≤x fx⊓fy≈fy))

------------------------------------------------------------------------
-- Properties of ⊔ᴸ

⊔ᴸ-sel : ∀ f → Selective {A = A} _≡_ (⊔ᴸ f)
⊔ᴸ-sel f = sel-≡ ⊔-isSelectiveMagma f

⊔ᴸ-presᵒ-v≤ : ∀ f {v} (x y : A) → v ≤ f x ⊎ v ≤ f y → v ≤ f (⊔ᴸ f x y)
⊔ᴸ-presᵒ-v≤ f {v} = preservesᵒ ⊔-isSelectiveMagma f
  (λ v≤fx fx⊔fy≈fy → trans v≤fx (x⊔y≈y⇒x≤y fx⊔fy≈fy))
  (λ v≤fy fx⊔fy≈fx → trans v≤fy (x⊔y≈x⇒y≤x fx⊔fy≈fx))

⊔ᴸ-presᵒ-v< : ∀ f {v} (x y : A) → v < f x ⊎ v < f y → v < f (⊔ᴸ f x y)
⊔ᴸ-presᵒ-v< f {v} = preservesᵒ ⊔-isSelectiveMagma f
  (λ v<fx fx⊔fy≈fy → <-transˡ v<fx (x⊔y≈y⇒x≤y fx⊔fy≈fy))
  (λ v<fy fx⊔fy≈fx → <-transˡ v<fy (x⊔y≈x⇒y≤x fx⊔fy≈fx))

⊔ᴸ-presᵇ-≤v : ∀ f {v} {x y : A} → f x ≤ v → f y ≤ v → f (⊔ᴸ f x y) ≤ v
⊔ᴸ-presᵇ-≤v f {v} = preservesᵇ ⊔-isSelectiveMagma {P = λ x → f x ≤ v} f

⊔ᴸ-presᵇ-<v : ∀ f {v} {x y : A} → f x < v → f y < v → f (⊔ᴸ f x y) < v
⊔ᴸ-presᵇ-<v f {v} = preservesᵇ ⊔-isSelectiveMagma {P = λ x → f x < v} f

⊔ᴸ-forcesᵇ-≤v : ∀ f {v} (x y : A) → f (⊔ᴸ f x y) ≤ v → f x ≤ v × f y ≤ v
⊔ᴸ-forcesᵇ-≤v f {v} = forcesᵇ ⊔-isSelectiveMagma f
  (λ fx≤v fx⊔fy≈fx → trans (x⊔y≈x⇒y≤x fx⊔fy≈fx) fx≤v)
  (λ fy≤v fx⊔fy≈fy → trans (x⊔y≈y⇒x≤y fx⊔fy≈fy) fy≤v)
