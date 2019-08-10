-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the setoid sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; _⇒_; _Preserves_⟶_)

module Data.List.Relation.Binary.Sublist.Setoid.Properties
  {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base hiding (_∷ʳ_)
import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
import Data.List.Relation.Binary.Sublist.Setoid as SetoidSublist
import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
  as HeteroProperties
import Data.List.Membership.Setoid as SetoidMembership
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Nat using (_≤_; _≥_; z≤n; s≤s)
import Data.Nat.Properties as ℕₚ
import Data.Maybe.Relation.Unary.All as Maybe
open import Function.Core
open import Function.Bijection   using (_⤖_)
open import Function.Equivalence using (_⇔_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; Decidable; Irrelevant)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬?)

open Setoid S using (_≈_) renaming (Carrier to A)
open SetoidEquality S using (_≋_; ≋-refl)
open SetoidSublist S hiding (map)
open SetoidMembership S using (_∈_)

------------------------------------------------------------------------
-- Injectivity of constructors
------------------------------------------------------------------------

module _ {xs ys : List A} where

  ∷-injectiveˡ : ∀ {x y} {px qx : x ≈ y} {pxs qxs : xs ⊆ ys} →
                 ((x ∷ xs) ⊆ (y ∷ ys) ∋ px ∷ pxs) ≡ (qx ∷ qxs) → px ≡ qx
  ∷-injectiveˡ refl = refl

  ∷-injectiveʳ : ∀ {x y} {px qx : x ≈ y} {pxs qxs : xs ⊆ ys} →
                 ((x ∷ xs) ⊆ (y ∷ ys) ∋ px ∷ pxs) ≡ (qx ∷ qxs) → pxs ≡ qxs
  ∷-injectiveʳ refl = refl

  ∷ʳ-injective : ∀ {y} {pxs qxs : xs ⊆ ys} → y ∷ʳ pxs ≡ y ∷ʳ qxs → pxs ≡ qxs
  ∷ʳ-injective refl = refl

------------------------------------------------------------------------
-- Various functions' outputs are sublists
------------------------------------------------------------------------

tail-⊆ : ∀ xs → Maybe.All (_⊆ xs) (tail xs)
tail-⊆ xs = HeteroProperties.tail-Sublist ⊆-refl

take-⊆ : ∀ n xs → take n xs ⊆ xs
take-⊆ n xs = HeteroProperties.take-Sublist n ⊆-refl

drop-⊆ : ∀ n xs → drop n xs ⊆ xs
drop-⊆ n xs = HeteroProperties.drop-Sublist n ⊆-refl

module _ {p} {P : Pred A p} (P? : Decidable P) where

  takeWhile-⊆ : ∀ xs → takeWhile P? xs ⊆ xs
  takeWhile-⊆ xs = HeteroProperties.takeWhile-Sublist P? ⊆-refl

  dropWhile-⊆ : ∀ xs → dropWhile P? xs ⊆ xs
  dropWhile-⊆ xs = HeteroProperties.dropWhile-Sublist P? ⊆-refl

  filter-⊆ : ∀ xs → filter P? xs ⊆ xs
  filter-⊆ xs = HeteroProperties.filter-Sublist P? ⊆-refl

module _ {p} {P : Pred A p} (P? : Decidable P) where

  takeWhile⊆filter : ∀ xs → takeWhile P? xs ⊆ filter P? xs
  takeWhile⊆filter xs = HeteroProperties.takeWhile-filter P? {xs} ≋-refl

  filter⊆dropWhile : ∀ xs → filter P? xs ⊆ dropWhile (¬? ∘ P?) xs
  filter⊆dropWhile xs = HeteroProperties.filter-dropWhile P? {xs} ≋-refl

------------------------------------------------------------------------
-- Various list functions are increasing wrt _⊆_
------------------------------------------------------------------------
-- We write f⁺ for the proof that `xs ⊆ ys → f xs ⊆ f ys`
-- and f⁻ for the one that `f xs ⊆ f ys → xs ⊆ ys`.

module _ {as bs : List A} where

  ∷ˡ⁻ : ∀ {a} → a ∷ as ⊆ bs → as ⊆ bs
  ∷ˡ⁻ = HeteroProperties.∷ˡ⁻

  ∷ʳ⁻ : ∀ {a b} → ¬ (a ≈ b) → a ∷ as ⊆ b ∷ bs → a ∷ as ⊆ bs
  ∷ʳ⁻ = HeteroProperties.∷ʳ⁻

  ∷⁻ : ∀ {a b} → a ∷ as ⊆ b ∷ bs → as ⊆ bs
  ∷⁻ = HeteroProperties.∷⁻

------------------------------------------------------------------------
-- map

module _ {b ℓ} (R : Setoid b ℓ) where

  open Setoid R using () renaming (Carrier to B; _≈_ to _≈′_)
  open SetoidSublist R using () renaming (_⊆_ to _⊆′_)

  map⁺ : ∀ {as bs} {f : A → B} → f Preserves _≈_ ⟶ _≈′_ →
         as ⊆ bs → map f as ⊆′ map f bs
  map⁺ {f = f} f-resp as⊆bs =
    HeteroProperties.map⁺ f f (SetoidSublist.map S f-resp as⊆bs)

------------------------------------------------------------------------
-- _++_

module _ {as bs : List A} where

  ++⁺ˡ : ∀ cs → as ⊆ bs → as ⊆ cs ++ bs
  ++⁺ˡ = HeteroProperties.++ˡ

  ++⁺ʳ : ∀ cs → as ⊆ bs → as ⊆ bs ++ cs
  ++⁺ʳ = HeteroProperties.++ʳ

  ++⁺ : ∀ {cs ds} → as ⊆ bs → cs ⊆ ds → as ++ cs ⊆ bs ++ ds
  ++⁺ = HeteroProperties.++⁺

  ++⁻ : ∀ {cs ds} → length as ≡ length bs → as ++ cs ⊆ bs ++ ds → cs ⊆ ds
  ++⁻ = HeteroProperties.++⁻

------------------------------------------------------------------------
-- take

module _  where

  take⁺ : ∀ {m n} {xs} → m ≤ n → take m xs ⊆ take n xs
  take⁺ m≤n = HeteroProperties.take⁺ m≤n ≋-refl

------------------------------------------------------------------------
-- drop

module _ {m n} {xs ys : List A} where

  drop⁺ : m ≥ n → xs ⊆ ys → drop m xs ⊆ drop n ys
  drop⁺ = HeteroProperties.drop⁺

module _ {m n} {xs : List A} where

  drop⁺-≥ : m ≥ n → drop m xs ⊆ drop n xs
  drop⁺-≥ m≥n = drop⁺ m≥n ⊆-refl

module _ {xs ys : List A} where

  drop⁺-⊆ : ∀ n → xs ⊆ ys → drop n xs ⊆ drop n ys
  drop⁺-⊆ n xs⊆ys = drop⁺ {n} ℕₚ.≤-refl xs⊆ys

------------------------------------------------------------------------
-- takeWhile / dropWhile

module _ {p q} {P : Pred A p} {Q : Pred A q}
         (P? : Decidable P) (Q? : Decidable Q) where

  takeWhile⁺ : ∀ {xs} → (∀ {a b} → a ≈ b → P a → Q b) →
               takeWhile P? xs ⊆ takeWhile Q? xs
  takeWhile⁺ {xs} P⇒Q = HeteroProperties.⊆-takeWhile-Sublist P? Q? {xs} P⇒Q ≋-refl

  dropWhile⁺ : ∀ {xs} → (∀ {a b} → a ≈ b → Q b → P a) →
               dropWhile P? xs ⊆ dropWhile Q? xs
  dropWhile⁺ {xs} P⇒Q = HeteroProperties.⊇-dropWhile-Sublist P? Q? {xs} P⇒Q ≋-refl

------------------------------------------------------------------------
-- filter

module _ {p q} {P : Pred A p} {Q : Pred A q}
         (P? : Decidable P) (Q? : Decidable Q) where

  filter⁺ : ∀ {as bs} → (∀ {a b} → a ≈ b → P a → Q b) →
            as ⊆ bs → filter P? as ⊆ filter Q? bs
  filter⁺ = HeteroProperties.⊆-filter-Sublist P? Q?

------------------------------------------------------------------------
-- reverse

module _ {as bs : List A} where

  reverseAcc⁺ : ∀ {cs ds} → as ⊆ bs → cs ⊆ ds →
                reverseAcc cs as ⊆ reverseAcc ds bs
  reverseAcc⁺ = HeteroProperties.reverseAcc⁺

  reverse⁺ : as ⊆ bs → reverse as ⊆ reverse bs
  reverse⁺ = HeteroProperties.reverse⁺

  reverse⁻ : reverse as ⊆ reverse bs → as ⊆ bs
  reverse⁻ = HeteroProperties.reverse⁻

------------------------------------------------------------------------
-- Inversion lemmas
------------------------------------------------------------------------

module _ {a as b bs} where

  ∷⁻¹ : a ≈ b → as ⊆ bs ⇔ a ∷ as ⊆ b ∷ bs
  ∷⁻¹ = HeteroProperties.∷⁻¹

  ∷ʳ⁻¹ : ¬ (a ≈ b) → a ∷ as ⊆ bs ⇔ a ∷ as ⊆ b ∷ bs
  ∷ʳ⁻¹ = HeteroProperties.∷ʳ⁻¹

------------------------------------------------------------------------
-- Other
------------------------------------------------------------------------

module _ where

  length-mono-≤ : ∀ {as bs} → as ⊆ bs → length as ≤ length bs
  length-mono-≤ = HeteroProperties.length-mono-≤

------------------------------------------------------------------------
-- Conversion to and from list equality

  to-≋ : ∀ {as bs} → length as ≡ length bs → as ⊆ bs → as ≋ bs
  to-≋ = HeteroProperties.toPointwise

------------------------------------------------------------------------
-- Irrelevant special case

  []⊆-irrelevant : Irrelevant ([] ⊆_)
  []⊆-irrelevant = HeteroProperties.Sublist-[]-irrelevant

------------------------------------------------------------------------
-- (to/from)∈ is a bijection

module _ {x xs} where

  to∈-injective : ∀ {p q : [ x ] ⊆ xs} → to∈ p ≡ to∈ q → p ≡ q
  to∈-injective = HeteroProperties.toAny-injective

  from∈-injective : ∀ {p q : x ∈ xs} → from∈ p ≡ from∈ q → p ≡ q
  from∈-injective = HeteroProperties.fromAny-injective

  to∈∘from∈≗id : ∀ (p : x ∈ xs) → to∈ (from∈ p) ≡ p
  to∈∘from∈≗id = HeteroProperties.toAny∘fromAny≗id

  [x]⊆xs⤖x∈xs : ([ x ] ⊆ xs) ⤖ (x ∈ xs)
  [x]⊆xs⤖x∈xs = HeteroProperties.Sublist-[x]-bijection
