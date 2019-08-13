-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the setoid sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; _⇒_; _Preserves_⟶_)

module Data.List.Relation.Binary.Sublist.Setoid.Properties
  {c ℓ} (S : Setoid c ℓ) where

open import Level

open import Data.List.Base hiding (_∷ʳ_)
import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
import Data.List.Relation.Binary.Sublist.Setoid as SetoidSublist
import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
  as HeteroProperties
import Data.List.Membership.Setoid as SetoidMembership
open import Data.List.Relation.Unary.Any using (Any)

import Data.Maybe.Relation.Unary.All as Maybe
open import Data.Nat using (_≤_; _≥_; z≤n; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _,_; proj₂)

open import Function.Core
open import Function.Bijection   using (_⤖_)
open import Function.Equivalence using (_⇔_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Unary using (Pred; Decidable; Irrelevant)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬?)

open Setoid S using (_≈_; trans) renaming (Carrier to A; refl to ≈-refl)
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

module _ {m n} {xs} where

  take⁺ : m ≤ n → take m xs ⊆ take n xs
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

------------------------------------------------------------------------
-- Properties of Disjoint and DisjointUnion

-- Irreflexivity

Disjoint-irrefl : ∀{xs ys} {τ : xs ⊆ ys} → Disjoint τ τ → xs ≋ []
Disjoint-irrefl [] = ≋-refl
Disjoint-irrefl (y ∷ₙ d) = Disjoint-irrefl d

-- Symmetry

DisjointUnion-symmetric : ∀ {xs ys xys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} {τ : xys ⊆ zs} →
  DisjointUnion τ₁ τ₂ τ → DisjointUnion τ₂ τ₁ τ
DisjointUnion-symmetric []         = []
DisjointUnion-symmetric (y   ∷ₙ d) = y ∷ₙ DisjointUnion-symmetric d
DisjointUnion-symmetric (x≈y ∷ₗ d) = x≈y ∷ᵣ DisjointUnion-symmetric d
DisjointUnion-symmetric (x≈y ∷ᵣ d) = x≈y ∷ₗ DisjointUnion-symmetric d

Disjoint-sym : ∀ {xs ys zs : List A} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
  Disjoint τ₁ τ₂ → Disjoint τ₂ τ₁
Disjoint-sym []         = []
Disjoint-sym (y   ∷ₙ d) = y ∷ₙ Disjoint-sym d
Disjoint-sym (x≈y ∷ₗ d) = x≈y ∷ᵣ Disjoint-sym d
Disjoint-sym (x≈y ∷ᵣ d) = x≈y ∷ₗ Disjoint-sym d

-- Monotonicity

Disjoint-monotoneˡ : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
  Disjoint τ₁ τ₂ → ∀ {ws} (σ : ws ⊆ xs) →
  Disjoint (⊆-trans σ τ₁) τ₂
-- In σ: keep.
Disjoint-monotoneˡ (x≈y ∷ₗ d) (x′≈x ∷ σ) = trans x′≈x x≈y ∷ₗ Disjoint-monotoneˡ d σ
-- Not in σ: drop.
Disjoint-monotoneˡ (x≈y ∷ₗ d) (y ∷ʳ σ)   = _ ∷ₙ Disjoint-monotoneˡ d σ
-- Not affected by σ since not coming from τ₁:
Disjoint-monotoneˡ (x≈y ∷ᵣ d) σ          = x≈y ∷ᵣ Disjoint-monotoneˡ d σ
Disjoint-monotoneˡ (y   ∷ₙ d) σ          = y ∷ₙ Disjoint-monotoneˡ d σ
Disjoint-monotoneˡ []         []         = []

Disjoint-monotoneʳ : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
  Disjoint τ₁ τ₂ → ∀ {ws} (σ : ws ⊆ ys) →
  Disjoint τ₁ (⊆-trans σ τ₂)
Disjoint-monotoneʳ d σ = Disjoint-sym (Disjoint-monotoneˡ (Disjoint-sym d) σ)

-- Empty sublist

DisjointUnion-[]ˡ : ∀{xs ys} {ε : [] ⊆ ys} {τ : xs ⊆ ys} → DisjointUnion ε τ τ
DisjointUnion-[]ˡ {ε = []}     {τ = []} = []
DisjointUnion-[]ˡ {ε = y ∷ʳ ε} {τ = y  ∷ʳ τ} = y   ∷ₙ DisjointUnion-[]ˡ
DisjointUnion-[]ˡ {ε = y ∷ʳ ε} {τ = x≈y ∷ τ} = x≈y ∷ᵣ DisjointUnion-[]ˡ

DisjointUnion-[]ʳ : ∀{xs ys} {ε : [] ⊆ ys} {τ : xs ⊆ ys} → DisjointUnion τ ε τ
DisjointUnion-[]ʳ {ε = []}     {τ = []} = []
DisjointUnion-[]ʳ {ε = y ∷ʳ ε} {τ = y  ∷ʳ τ} = y   ∷ₙ DisjointUnion-[]ʳ
DisjointUnion-[]ʳ {ε = y ∷ʳ ε} {τ = x≈y ∷ τ} = x≈y ∷ₗ DisjointUnion-[]ʳ


record DisjointUnion³
  {xs ys zs ts} (τ₁  : xs  ⊆ ts) (τ₂  : ys  ⊆ ts) (τ₃  : zs  ⊆ ts)
  {xys xzs yzs} (τ₁₂ : xys ⊆ ts) (τ₁₃ : xzs ⊆ ts) (τ₂₃ : yzs ⊆ ts) : Set (c ⊔ ℓ) where
  field
    {union³} : List A
    sub³  : union³ ⊆ ts
    join₁ : DisjointUnion τ₁ τ₂₃ sub³
    join₂ : DisjointUnion τ₂ τ₁₃ sub³
    join₃ : DisjointUnion τ₃ τ₁₂ sub³

_∷ʳ-DisjointUnion³_ :
  ∀ {xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts} →
  ∀ {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
  ∀ y →
  DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃ →
  DisjointUnion³ (y ∷ʳ τ₁) (y ∷ʳ τ₂) (y ∷ʳ τ₃) (y ∷ʳ τ₁₂) (y ∷ʳ τ₁₃) (y ∷ʳ τ₂₃)
y ∷ʳ-DisjointUnion³ record{ sub³ = σ ; join₁ = d₁ ; join₂ = d₂ ; join₃ = d₃ } = record
  { sub³  = y ∷ʳ σ
  ; join₁ = y ∷ₙ d₁
  ; join₂ = y ∷ₙ d₂
  ; join₃ = y ∷ₙ d₃
  }

_∷₁-DisjointUnion³_ :
  ∀ {xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts} →
  ∀ {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
  ∀ {x y} (x≈y : x ≈ y) →
  DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃ →
  DisjointUnion³ (x≈y ∷ τ₁) (y ∷ʳ τ₂) (y ∷ʳ τ₃) (x≈y ∷ τ₁₂) (x≈y ∷ τ₁₃) (y ∷ʳ τ₂₃)
x≈y ∷₁-DisjointUnion³ record{ sub³ = σ ; join₁ = d₁ ; join₂ = d₂ ; join₃ = d₃ } = record
  { sub³  = x≈y ∷ σ
  ; join₁ = x≈y ∷ₗ d₁
  ; join₂ = x≈y ∷ᵣ d₂
  ; join₃ = x≈y ∷ᵣ d₃
  }

_∷₂-DisjointUnion³_ :
  ∀ {xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts} →
  ∀ {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
  ∀ {x y} (x≈y : x ≈ y) →
  DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃ →
  DisjointUnion³ (y ∷ʳ τ₁) (x≈y ∷ τ₂) (y ∷ʳ τ₃) (x≈y ∷ τ₁₂) (y ∷ʳ τ₁₃) (x≈y ∷ τ₂₃)
x≈y ∷₂-DisjointUnion³ record{ sub³ = σ ; join₁ = d₁ ; join₂ = d₂ ; join₃ = d₃ } = record
  { sub³  = x≈y ∷ σ
  ; join₁ = x≈y ∷ᵣ d₁
  ; join₂ = x≈y ∷ₗ d₂
  ; join₃ = x≈y ∷ᵣ d₃
  }

_∷₃-DisjointUnion³_ :
  ∀ {xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts} →
  ∀ {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
  ∀ {x y} (x≈y : x ≈ y) →
  DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃ →
  DisjointUnion³ (y ∷ʳ τ₁) (y ∷ʳ τ₂) (x≈y ∷ τ₃) (y ∷ʳ τ₁₂) (x≈y ∷ τ₁₃) (x≈y ∷ τ₂₃)
x≈y ∷₃-DisjointUnion³ record{ sub³ = σ ; join₁ = d₁ ; join₂ = d₂ ; join₃ = d₃ } = record
  { sub³  = x≈y ∷ σ
  ; join₁ = x≈y ∷ᵣ d₁
  ; join₂ = x≈y ∷ᵣ d₂
  ; join₃ = x≈y ∷ₗ d₃
  }

disjointUnion³ : ∀{xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts}
  {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
  DisjointUnion τ₁ τ₂ τ₁₂ →
  DisjointUnion τ₁ τ₃ τ₁₃ →
  DisjointUnion τ₂ τ₃ τ₂₃ →
  DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃
disjointUnion³ [] [] [] = record { sub³ = [] ; join₁ = [] ; join₂ = [] ; join₃ = [] }
disjointUnion³ (y   ∷ₙ d₁₂) (.y  ∷ₙ d₁₃) (.y   ∷ₙ d₂₃) = y ∷ʳ-DisjointUnion³ disjointUnion³ d₁₂ d₁₃ d₂₃
disjointUnion³ (y   ∷ₙ d₁₂) (x≈y ∷ᵣ d₁₃) (.x≈y ∷ᵣ d₂₃) = x≈y ∷₃-DisjointUnion³ disjointUnion³ d₁₂ d₁₃ d₂₃
disjointUnion³ (x≈y ∷ᵣ d₁₂) (y   ∷ₙ d₁₃) (.x≈y ∷ₗ d₂₃) = x≈y ∷₂-DisjointUnion³ disjointUnion³ d₁₂ d₁₃ d₂₃
disjointUnion³ (x≈y ∷ₗ d₁₂) (.x≈y ∷ₗ d₁₃) (y    ∷ₙ d₂₃) = x≈y ∷₁-DisjointUnion³ disjointUnion³ d₁₂ d₁₃ d₂₃
disjointUnion³ (x≈y ∷ᵣ d₁₂) (x≈y′ ∷ᵣ d₁₃) ()

disjoint⇒disjoint-to-union : ∀{xs ys zs yzs ts} {τ : xs ⊆ ts} {σ₁ : ys ⊆ ts} {σ₂ : zs ⊆ ts} {σ : yzs ⊆ ts} →
  DisjointUnion σ₁ σ₂ σ → Disjoint τ σ₁ → Disjoint τ σ₂ → Disjoint τ σ
disjoint⇒disjoint-to-union u d₁ d₂ = let
     _ , _ , u₁ = Disjoint→DisjointUnion d₁
     _ , _ , u₂ = Disjoint→DisjointUnion d₂
  in DisjointUnion→Disjoint ( DisjointUnion³.join₁ (disjointUnion³ u₁ u₂ u) )


-- -- Needs proof-irrelevant setoid (K)
-- DisjointUnion-from∈-∷ˡ⁻ : ∀ {y : A} {xs ys : List A} (y∈ys : y ∈ ys) (τ : (y ∷ xs) ⊆ ys) → DisjointUnion (from∈ y∈ys) (∷ˡ⁻ τ) τ
-- DisjointUnion-from∈-∷ˡ⁻ (Any.here x≈y) (y ∷ʳ τ) = {!x≈y ∷ₗ ?!}
-- DisjointUnion-from∈-∷ˡ⁻ (Any.here x≈y) (x≈y' ∷ τ) = {!x≈y' ∷ₗ ?!}
-- DisjointUnion-from∈-∷ˡ⁻ (Any.there y∈ys) (y ∷ʳ τ) = {!!}
-- DisjointUnion-from∈-∷ˡ⁻ (Any.there y∈ys) (x ∷ τ) = {!!}

-- -}
-- -}
-- -}
