------------------------------------------------------------------------
-- The Agda standard library
--
-- Finding the maximum/minimum values in a list
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (TotalOrder; Setoid)

module Data.List.Extrema
  {b ℓ₁ ℓ₂} (totalOrder : TotalOrder b ℓ₁ ℓ₂) where

open import Data.List.Base using (List; foldr)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.All
  using (All; []; _∷_; lookup; map; tabulate)
open import Data.List.Membership.Propositional using (_∈_; lose)
open import Data.List.Membership.Propositional.Properties
  using (foldr-selective)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_; _⊇_)
open import Data.List.Properties as List
  using (foldr-preservesᵒ; foldr-preservesᵇ; foldr-forcesᵇ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (id; flip; _on_; _∘_)
open import Level using (Level)
open import Relation.Unary using (Pred)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; sym; subst) renaming (refl to ≡-refl)

------------------------------------------------------------------------
-- Setup

open TotalOrder totalOrder renaming (Carrier to B)
open NonStrictToStrict _≈_ _≤_ using (_<_)
open import Data.List.Extrema.Core totalOrder
  renaming (⊓ᴸ to ⊓-lift; ⊔ᴸ to ⊔-lift)

private
  variable
    a p : Level
    A : Set a

------------------------------------------------------------------------
-- Functions

argmin : (A → B) → A → List A → A
argmin f = foldr (⊓-lift f)

argmax : (A → B) → A → List A → A
argmax f = foldr (⊔-lift f)

min : B → List B → B
min = argmin id

max : B → List B → B
max = argmax id

------------------------------------------------------------------------
-- Properties of argmin

module _ {f : A → B} where

  f[argmin]≤v⁺ : ∀ {v} ⊤ xs → (f ⊤ ≤ v) ⊎ (Any (λ x → f x ≤ v) xs) →
                f (argmin f ⊤ xs) ≤ v
  f[argmin]≤v⁺ = foldr-preservesᵒ (⊓ᴸ-presᵒ-≤v f)

  f[argmin]<v⁺ : ∀ {v} ⊤ xs → (f ⊤ < v) ⊎ (Any (λ x → f x < v) xs) →
                f (argmin f ⊤ xs) < v
  f[argmin]<v⁺ = foldr-preservesᵒ (⊓ᴸ-presᵒ-<v f)

  v≤f[argmin]⁺ : ∀ {v ⊤ xs} → v ≤ f ⊤ → All (λ x → v ≤ f x) xs →
                v ≤ f (argmin f ⊤ xs)
  v≤f[argmin]⁺ = foldr-preservesᵇ (⊓ᴸ-presᵇ-v≤ f)

  v<f[argmin]⁺ : ∀ {v ⊤ xs} → v < f ⊤ → All (λ x → v < f x) xs →
                v < f (argmin f ⊤ xs)
  v<f[argmin]⁺ = foldr-preservesᵇ (⊓ᴸ-presᵇ-v< f)

  f[argmin]≤f[⊤] : ∀ ⊤ xs → f (argmin f ⊤ xs) ≤ f ⊤
  f[argmin]≤f[⊤] ⊤ xs = f[argmin]≤v⁺ ⊤ xs (inj₁ refl)

  f[argmin]≤f[xs] : ∀ ⊤ xs → All (λ x → f (argmin f ⊤ xs) ≤ f x) xs
  f[argmin]≤f[xs] ⊤ xs = foldr-forcesᵇ (⊓ᴸ-forcesᵇ-v≤ f) ⊤ xs refl

  f[argmin]≈f[v]⁺ : ∀ {v ⊤ xs} → v ∈ xs → All (λ x → f v ≤ f x) xs → f v ≤ f ⊤ →
                    f (argmin f ⊤ xs) ≈ f v
  f[argmin]≈f[v]⁺ v∈xs fv≤fxs fv≤f⊤ = antisym
    (f[argmin]≤v⁺ _ _ (inj₂ (lose v∈xs refl)))
    (v≤f[argmin]⁺ fv≤f⊤ fv≤fxs)

argmin[xs]≤argmin[ys]⁺ : ∀ {f g : A → B} ⊤₁ {⊤₂} xs {ys : List A} →
                        (f ⊤₁ ≤ g ⊤₂) ⊎ Any (λ x → f x ≤ g ⊤₂) xs →
                        All (λ y → (f ⊤₁ ≤ g y) ⊎ Any (λ x → f x ≤ g y) xs) ys →
                        f (argmin f ⊤₁ xs) ≤ g (argmin g ⊤₂ ys)
argmin[xs]≤argmin[ys]⁺ ⊤₁ xs xs≤⊤₂ xs≤ys =
  v≤f[argmin]⁺ (f[argmin]≤v⁺ ⊤₁ _ xs≤⊤₂) (map (f[argmin]≤v⁺ ⊤₁ xs) xs≤ys)

argmin[xs]<argmin[ys]⁺ : ∀ {f g : A → B} ⊤₁ {⊤₂} xs {ys : List A} →
                        (f ⊤₁ < g ⊤₂) ⊎ Any (λ x → f x < g ⊤₂) xs →
                        All (λ y → (f ⊤₁ < g y) ⊎ Any (λ x → f x < g y) xs) ys →
                        f (argmin f ⊤₁ xs) < g (argmin g ⊤₂ ys)
argmin[xs]<argmin[ys]⁺ ⊤₁ xs xs<⊤₂ xs<ys =
  v<f[argmin]⁺ (f[argmin]<v⁺ ⊤₁ _ xs<⊤₂) (map (f[argmin]<v⁺ ⊤₁ xs) xs<ys)

argmin-sel : ∀ (f : A → B) ⊤ xs → (argmin f ⊤ xs ≡ ⊤) ⊎ (argmin f ⊤ xs ∈ xs)
argmin-sel f = foldr-selective (⊓ᴸ-sel f)

argmin-all : ∀ (f : A → B) {⊤ xs} {P : Pred A p} →
             P ⊤ → All P xs → P (argmin f ⊤ xs)
argmin-all f {⊤} {xs} {P = P}  p⊤ pxs with argmin-sel f ⊤ xs
... | inj₁ argmin≡⊤  = subst P (sym argmin≡⊤) p⊤
... | inj₂ argmin∈xs = lookup pxs argmin∈xs

------------------------------------------------------------------------
-- Properties of argmax

module _ {f : A → B} where

  v≤f[argmax]⁺ : ∀ {v} ⊥ xs → (v ≤ f ⊥) ⊎ (Any (λ x → v ≤ f x) xs) →
                v ≤ f (argmax f ⊥ xs)
  v≤f[argmax]⁺ = foldr-preservesᵒ (⊔ᴸ-presᵒ-v≤ f)

  v<f[argmax]⁺ : ∀ {v} ⊥ xs → (v < f ⊥) ⊎ (Any (λ x → v < f x) xs) →
                v < f (argmax f ⊥ xs)
  v<f[argmax]⁺ = foldr-preservesᵒ (⊔ᴸ-presᵒ-v< f)

  f[argmax]≤v⁺ : ∀ {v ⊥ xs} → f ⊥ ≤ v → All (λ x → f x ≤ v) xs →
                f (argmax f ⊥ xs) ≤ v
  f[argmax]≤v⁺ = foldr-preservesᵇ (⊔ᴸ-presᵇ-≤v f)

  f[argmax]<v⁺ : ∀ {v ⊥ xs} → f ⊥ < v → All (λ x → f x < v) xs →
                f (argmax f ⊥ xs) < v
  f[argmax]<v⁺ = foldr-preservesᵇ (⊔ᴸ-presᵇ-<v f)

  f[⊥]≤f[argmax] : ∀ ⊥ xs → f ⊥ ≤ f (argmax f ⊥ xs)
  f[⊥]≤f[argmax] ⊥ xs = v≤f[argmax]⁺ ⊥ xs (inj₁ refl)

  f[xs]≤f[argmax] : ∀ ⊥ xs → All (λ x → f x ≤ f (argmax f ⊥ xs)) xs
  f[xs]≤f[argmax] ⊥ xs = foldr-forcesᵇ (⊔ᴸ-forcesᵇ-≤v f) ⊥ xs refl

  f[argmax]≈f[v]⁺ : ∀ {v ⊥ xs} → v ∈ xs → All (λ x → f x ≤ f v) xs → f ⊥ ≤ f v →
                    f (argmax f ⊥ xs) ≈ f v
  f[argmax]≈f[v]⁺ v∈xs fxs≤fv f⊥≤fv = antisym
    (f[argmax]≤v⁺ f⊥≤fv fxs≤fv)
    (v≤f[argmax]⁺ _ _ (inj₂ (lose v∈xs refl)))

argmax[xs]≤argmax[ys]⁺ : ∀ {f g : A → B} {⊥₁} ⊥₂ {xs : List A} ys →
                         (f ⊥₁ ≤ g ⊥₂) ⊎ Any (λ y → f ⊥₁ ≤ g y) ys →
                         All (λ x → (f x ≤ g ⊥₂) ⊎ Any (λ y → f x ≤ g y) ys) xs →
                         f (argmax f ⊥₁ xs) ≤ g (argmax g ⊥₂ ys)
argmax[xs]≤argmax[ys]⁺ ⊥₂ ys ⊥₁≤ys xs≤ys =
  f[argmax]≤v⁺ (v≤f[argmax]⁺ ⊥₂ _ ⊥₁≤ys) (map (v≤f[argmax]⁺ ⊥₂ ys) xs≤ys)

argmax[xs]<argmax[ys]⁺ : ∀ {f g : A → B} {⊥₁} ⊥₂ {xs : List A} ys →
                         (f ⊥₁ < g ⊥₂) ⊎ Any (λ y → f ⊥₁ < g y) ys →
                         All (λ x → (f x < g ⊥₂) ⊎ Any (λ y → f x < g y) ys) xs →
                         f (argmax f ⊥₁ xs) < g (argmax g ⊥₂ ys)
argmax[xs]<argmax[ys]⁺ ⊥₂ ys ⊥₁<ys xs<ys =
  f[argmax]<v⁺ (v<f[argmax]⁺ ⊥₂ _ ⊥₁<ys) (map (v<f[argmax]⁺ ⊥₂ ys) xs<ys)

argmax-sel : ∀ (f : A → B) ⊥ xs → (argmax f ⊥ xs ≡ ⊥) ⊎ (argmax f ⊥ xs ∈ xs)
argmax-sel f = foldr-selective (⊔ᴸ-sel f)

argmax-all : ∀ (f : A → B) {P : Pred A p} {⊥ xs} →
             P ⊥ → All P xs → P (argmax f ⊥ xs)
argmax-all f {P = P} {⊥} {xs} p⊥ pxs with argmax-sel f ⊥ xs
... | inj₁ argmax≡⊥  = subst P (sym argmax≡⊥) p⊥
... | inj₂ argmax∈xs = lookup pxs argmax∈xs

------------------------------------------------------------------------
-- Properties of min

min≤v⁺ : ∀ {v} ⊤ xs → ⊤ ≤ v ⊎ Any (_≤ v) xs → min ⊤ xs ≤ v
min≤v⁺ = f[argmin]≤v⁺

min<v⁺ : ∀ {v} ⊤ xs → ⊤ < v ⊎ Any (_< v) xs → min ⊤ xs < v
min<v⁺ = f[argmin]<v⁺

v≤min⁺ : ∀ {v ⊤ xs} → v ≤ ⊤ → All (v ≤_) xs → v ≤ min ⊤ xs
v≤min⁺ = v≤f[argmin]⁺

v<min⁺ : ∀ {v ⊤ xs} → v < ⊤ → All (v <_) xs → v < min ⊤ xs
v<min⁺ = v<f[argmin]⁺

min≤⊤ : ∀ ⊤ xs → min ⊤ xs ≤ ⊤
min≤⊤ = f[argmin]≤f[⊤]

min≤xs : ∀ ⊥ xs → All (min ⊥ xs ≤_) xs
min≤xs = f[argmin]≤f[xs]

min≈v⁺ : ∀ {v ⊤ xs} → v ∈ xs → All (v ≤_) xs → v ≤ ⊤ → min ⊤ xs ≈ v
min≈v⁺ = f[argmin]≈f[v]⁺

min[xs]≤min[ys]⁺ : ∀ ⊤₁ {⊤₂} xs {ys} → (⊤₁ ≤ ⊤₂) ⊎ Any (_≤ ⊤₂) xs →
                   All (λ y → (⊤₁ ≤ y) ⊎ Any (λ x → x ≤ y) xs) ys →
                   min ⊤₁ xs ≤ min ⊤₂ ys
min[xs]≤min[ys]⁺ = argmin[xs]≤argmin[ys]⁺

min[xs]<min[ys]⁺ : ∀ ⊤₁ {⊤₂} xs {ys} → (⊤₁ < ⊤₂) ⊎ Any (_< ⊤₂) xs →
                   All (λ y → (⊤₁ < y) ⊎ Any (λ x → x < y) xs) ys →
                   min ⊤₁ xs < min ⊤₂ ys
min[xs]<min[ys]⁺ = argmin[xs]<argmin[ys]⁺

min-mono-⊆ : ∀ {⊥₁ ⊥₂ xs ys} → ⊥₁ ≤ ⊥₂ → xs ⊇ ys → min ⊥₁ xs ≤ min ⊥₂ ys
min-mono-⊆ ⊥₁≤⊥₂ ys⊆xs = min[xs]≤min[ys]⁺ _ _ (inj₁ ⊥₁≤⊥₂)
  (tabulate (inj₂ ∘ Any.map (λ {≡-refl → refl}) ∘ ys⊆xs))

------------------------------------------------------------------------
-- Properties of max

max≤v⁺ : ∀ {v ⊥ xs} → ⊥ ≤ v → All (_≤ v) xs → max ⊥ xs ≤ v
max≤v⁺ = f[argmax]≤v⁺

max<v⁺ : ∀ {v ⊥ xs} → ⊥ < v → All (_< v) xs → max ⊥ xs < v
max<v⁺ = f[argmax]<v⁺

v≤max⁺ : ∀ {v} ⊥ xs → v ≤ ⊥ ⊎ Any (v ≤_) xs → v ≤ max ⊥ xs
v≤max⁺ = v≤f[argmax]⁺

v<max⁺ : ∀ {v} ⊥ xs → v < ⊥ ⊎ Any (v <_) xs → v < max ⊥ xs
v<max⁺ = v<f[argmax]⁺

⊥≤max : ∀ ⊥ xs → ⊥ ≤ max ⊥ xs
⊥≤max = f[⊥]≤f[argmax]

xs≤max : ∀ ⊥ xs → All (_≤ max ⊥ xs) xs
xs≤max = f[xs]≤f[argmax]

max≈v⁺ : ∀ {v ⊤ xs} → v ∈ xs → All (_≤ v) xs → ⊤ ≤ v → max ⊤ xs ≈ v
max≈v⁺ = f[argmax]≈f[v]⁺

max[xs]≤max[ys]⁺ : ∀ {⊥₁} ⊥₂ {xs} ys → ⊥₁ ≤ ⊥₂ ⊎ Any (⊥₁ ≤_) ys →
                   All (λ x → x ≤ ⊥₂ ⊎ Any (x ≤_) ys) xs →
                   max ⊥₁ xs ≤ max ⊥₂ ys
max[xs]≤max[ys]⁺ = argmax[xs]≤argmax[ys]⁺

max[xs]<max[ys]⁺ : ∀ {⊥₁} ⊥₂ {xs} ys → ⊥₁ < ⊥₂ ⊎ Any (⊥₁ <_) ys →
                   All (λ x → x < ⊥₂ ⊎ Any (x <_) ys) xs →
                   max ⊥₁ xs < max ⊥₂ ys
max[xs]<max[ys]⁺ = argmax[xs]<argmax[ys]⁺

max-mono-⊆ : ∀ {⊥₁ ⊥₂ xs ys} → ⊥₁ ≤ ⊥₂ → xs ⊆ ys → max ⊥₁ xs ≤ max ⊥₂ ys
max-mono-⊆ ⊥₁≤⊥₂ xs⊆ys = max[xs]≤max[ys]⁺ _ _ (inj₁ ⊥₁≤⊥₂)
  (tabulate (inj₂ ∘ Any.map (λ {≡-refl → refl}) ∘ xs⊆ys))
