------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the setoid sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_; _Preserves_⟶_)
open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Sublist.Setoid.Properties
  {c ℓ} (S : Setoid c ℓ) where

open import Data.List.Base hiding (_∷ʳ_; lookup)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.All
  using (All; []; _∷_; tabulateₛ)
import Data.Maybe.Relation.Unary.All as Maybe
open import Data.Nat.Base using (ℕ; _≤_; _≥_)
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (∃; _,_; proj₂)
open import Function.Base
open import Function.Bundles using (_⇔_; _⤖_)
open import Level
open import Relation.Binary.Definitions
  using (_Respects_) renaming (Decidable to Decidable₂)
import Relation.Binary.Properties.Setoid as SetoidProperties
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; refl; sym; cong; cong₂)
import Relation.Binary.Reasoning.Preorder as ≲-Reasoning
open import Relation.Binary.Reasoning.Syntax
open import Relation.Binary.Structures using (IsDecTotalOrder)
open import Relation.Unary using (Pred; Decidable; Universal; Irrelevant)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (¬?; yes; no)

import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
import Data.List.Relation.Binary.Sublist.Setoid as SetoidSublist
import Data.List.Relation.Binary.Sublist.Heterogeneous
  as Hetero
import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
  as HeteroProperties
import Data.List.Membership.Setoid as SetoidMembership

open Setoid S using (_≈_; trans)
  renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym)
open SetoidEquality S using (_≋_; ≋-refl; ≋-reflexive; ≋-setoid)
open SetoidSublist S hiding (map)
open SetoidProperties S using (≈-preorder)


private
  variable
    p q r s t : Level
    a b x y : A
    as bs cs ds xs ys : List A
    xss yss : List (List A)
    P : Pred A p
    Q : Pred A q
    m n : ℕ


------------------------------------------------------------------------
-- Injectivity of constructors
------------------------------------------------------------------------

module _ where

  ∷-injectiveˡ : ∀ {px qx : x ≈ y} {pxs qxs : xs ⊆ ys} →
                 ((x ∷ xs) ⊆ (y ∷ ys) ∋ px ∷ pxs) ≡ (qx ∷ qxs) → px ≡ qx
  ∷-injectiveˡ refl = refl

  ∷-injectiveʳ : ∀ {px qx : x ≈ y} {pxs qxs : xs ⊆ ys} →
                 ((x ∷ xs) ⊆ (y ∷ ys) ∋ px ∷ pxs) ≡ (qx ∷ qxs) → pxs ≡ qxs
  ∷-injectiveʳ refl = refl

  ∷ʳ-injective : ∀ {pxs qxs : xs ⊆ ys} → y ∷ʳ pxs ≡ y ∷ʳ qxs → pxs ≡ qxs
  ∷ʳ-injective refl = refl

------------------------------------------------------------------------
-- Categorical properties
------------------------------------------------------------------------

module _ (trans-reflˡ : ∀ {x y} (p : x ≈ y) → trans ≈-refl p ≡ p) where

  ⊆-trans-idˡ : (pxs : xs ⊆ ys) → ⊆-trans ⊆-refl pxs ≡ pxs
  ⊆-trans-idˡ [] = refl
  ⊆-trans-idˡ (y ∷ʳ pxs) = cong (y ∷ʳ_) (⊆-trans-idˡ pxs)
  ⊆-trans-idˡ (x ∷ pxs) = cong₂ _∷_ (trans-reflˡ x) (⊆-trans-idˡ pxs)

module _ (trans-reflʳ : ∀ {x y} (p : x ≈ y) → trans p ≈-refl ≡ p) where

  ⊆-trans-idʳ : (pxs : xs ⊆ ys) → ⊆-trans pxs ⊆-refl ≡ pxs
  ⊆-trans-idʳ [] = refl
  ⊆-trans-idʳ (y ∷ʳ pxs) = cong (y ∷ʳ_) (⊆-trans-idʳ pxs)
  ⊆-trans-idʳ (x ∷ pxs) = cong₂ _∷_ (trans-reflʳ x) (⊆-trans-idʳ pxs)

module _ (≈-assoc : ∀ {w x y z} (p : w ≈ x) (q : x ≈ y) (r : y ≈ z) →
                    trans p (trans q r) ≡ trans (trans p q) r) where

  ⊆-trans-assoc : (ps : as ⊆ bs) (qs : bs ⊆ cs) (rs : cs ⊆ ds) →
            ⊆-trans ps (⊆-trans qs rs) ≡ ⊆-trans (⊆-trans ps qs) rs
  ⊆-trans-assoc ps qs (_ ∷ʳ rs) = cong (_ ∷ʳ_) (⊆-trans-assoc ps qs rs)
  ⊆-trans-assoc ps (_ ∷ʳ qs) (_ ∷ rs) = cong (_ ∷ʳ_) (⊆-trans-assoc ps qs rs)
  ⊆-trans-assoc (_ ∷ʳ ps) (_ ∷ qs) (_ ∷ rs) = cong (_ ∷ʳ_) (⊆-trans-assoc ps qs rs)
  ⊆-trans-assoc (p ∷ ps) (q ∷ qs) (r ∷ rs) = cong₂ _∷_ (≈-assoc p q r) (⊆-trans-assoc ps qs rs)
  ⊆-trans-assoc [] [] [] = refl


------------------------------------------------------------------------
-- Relationships to other predicates

module _ {P : Pred A p} (resp : P Respects _≈_) where

-- All P is a contravariant functor from _⊆_ to Set.

  All-resp-⊆ : (All P) Respects _⊇_
  All-resp-⊆ []        []       = []
  All-resp-⊆ (_  ∷ʳ p) (x ∷ xs) = All-resp-⊆ p xs
  All-resp-⊆ (x≈y ∷ p) (x ∷ xs) = resp (≈-sym x≈y) x ∷ All-resp-⊆ p xs

-- Any P is a covariant functor from _⊆_ to Set.

  Any-resp-⊆ : (Any P) Respects _⊆_
  Any-resp-⊆ = lookup resp

------------------------------------------------------------------------
-- Reasoning over sublists
------------------------------------------------------------------------

module ⊆-Reasoning = HeteroProperties.⊆-Reasoning ≈-preorder

------------------------------------------------------------------------
-- Various functions' outputs are sublists
------------------------------------------------------------------------

tail-⊆ : ∀ xs → Maybe.All (_⊆ xs) (tail xs)
tail-⊆ xs = HeteroProperties.tail-Sublist ⊆-refl

take-⊆ : ∀ n xs → take n xs ⊆ xs
take-⊆ n xs = HeteroProperties.take-Sublist n ⊆-refl

drop-⊆ : ∀ n xs → drop n xs ⊆ xs
drop-⊆ n xs = HeteroProperties.drop-Sublist n ⊆-refl

module _ (P? : Decidable P) where

  takeWhile-⊆ : ∀ xs → takeWhile P? xs ⊆ xs
  takeWhile-⊆ xs = HeteroProperties.takeWhile-Sublist P? ⊆-refl

  dropWhile-⊆ : ∀ xs → dropWhile P? xs ⊆ xs
  dropWhile-⊆ xs = HeteroProperties.dropWhile-Sublist P? ⊆-refl

  filter-⊆ : ∀ xs → filter P? xs ⊆ xs
  filter-⊆ xs = HeteroProperties.filter-Sublist P? ⊆-refl

module _ (P? : Decidable P) where

  takeWhile⊆filter : ∀ xs → takeWhile P? xs ⊆ filter P? xs
  takeWhile⊆filter xs = HeteroProperties.takeWhile-filter P? {xs} ≋-refl

  filter⊆dropWhile : ∀ xs → filter P? xs ⊆ dropWhile (¬? ∘ P?) xs
  filter⊆dropWhile xs = HeteroProperties.filter-dropWhile P? {xs} ≋-refl

------------------------------------------------------------------------
-- Various list functions are increasing wrt _⊆_
------------------------------------------------------------------------
-- We write f⁺ for the proof that `xs ⊆ ys → f xs ⊆ f ys`
-- and f⁻ for the one that `f xs ⊆ f ys → xs ⊆ ys`.

module _ where

  ∷ˡ⁻ : a ∷ as ⊆ bs → as ⊆ bs
  ∷ˡ⁻ = HeteroProperties.∷ˡ⁻

  ∷ʳ⁻ : ¬ (a ≈ b) → a ∷ as ⊆ b ∷ bs → a ∷ as ⊆ bs
  ∷ʳ⁻ = HeteroProperties.∷ʳ⁻

  ∷⁻ : a ∷ as ⊆ b ∷ bs → as ⊆ bs
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

module _ where

  ++⁺ˡ : ∀ cs → as ⊆ bs → as ⊆ cs ++ bs
  ++⁺ˡ = HeteroProperties.++ˡ

  ++⁺ʳ : ∀ cs → as ⊆ bs → as ⊆ bs ++ cs
  ++⁺ʳ = HeteroProperties.++ʳ

  ++⁺ : as ⊆ bs → cs ⊆ ds → as ++ cs ⊆ bs ++ ds
  ++⁺ = HeteroProperties.++⁺

  ++⁻ : length as ≡ length bs → as ++ cs ⊆ bs ++ ds → cs ⊆ ds
  ++⁻ = HeteroProperties.++⁻

------------------------------------------------------------------------
-- concat

module _ where

  concat⁺ : Hetero.Sublist _⊆_ xss yss →
            concat xss ⊆ concat yss
  concat⁺ = HeteroProperties.concat⁺

  open SetoidMembership ≋-setoid using (_∈_)
  open SetoidSublist ≋-setoid
    using ()
    renaming (map to map-≋; from∈ to from∈-≋)

  xs∈xss⇒xs⊆concat[xss] : xs ∈ xss → xs ⊆ concat xss
  xs∈xss⇒xs⊆concat[xss] {xs = xs} {xss = xss} xs∈xss = begin
    xs ≈⟨ ≋-reflexive (++-identityʳ xs) ⟨
    xs ++ [] ⊆⟨ concat⁺ (map-≋ ⊆-reflexive (from∈-≋ xs∈xss)) ⟩
    concat xss ∎
    where open ⊆-Reasoning

  all⊆concat : (xss : List (List A)) → All (_⊆ concat xss) xss
  all⊆concat _ = tabulateₛ ≋-setoid xs∈xss⇒xs⊆concat[xss]

------------------------------------------------------------------------
-- take

module _ where

  take⁺ : m ≤ n → take m xs ⊆ take n xs
  take⁺ m≤n = HeteroProperties.take⁺ m≤n ≋-refl

------------------------------------------------------------------------
-- drop

module _ where

  drop⁺ : m ≥ n → xs ⊆ ys → drop m xs ⊆ drop n ys
  drop⁺ = HeteroProperties.drop⁺

module _ where

  drop⁺-≥ : m ≥ n → drop m xs ⊆ drop n xs
  drop⁺-≥ m≥n = drop⁺ m≥n ⊆-refl

module _ where

  drop⁺-⊆ : ∀ n → xs ⊆ ys → drop n xs ⊆ drop n ys
  drop⁺-⊆ n xs⊆ys = drop⁺ {n} ℕ.≤-refl xs⊆ys

------------------------------------------------------------------------
-- takeWhile / dropWhile

module _ (P? : Decidable P) (Q? : Decidable Q) where

  takeWhile⁺ : ∀ {xs} → (∀ {a b} → a ≈ b → P a → Q b) →
               takeWhile P? xs ⊆ takeWhile Q? xs
  takeWhile⁺ {xs} P⇒Q = HeteroProperties.⊆-takeWhile-Sublist P? Q? {xs} P⇒Q ≋-refl

  dropWhile⁺ : ∀ {xs} → (∀ {a b} → a ≈ b → Q b → P a) →
               dropWhile P? xs ⊆ dropWhile Q? xs
  dropWhile⁺ {xs} P⇒Q = HeteroProperties.⊇-dropWhile-Sublist P? Q? {xs} P⇒Q ≋-refl

------------------------------------------------------------------------
-- filter

module _ (P? : Decidable P) (Q? : Decidable Q) where

  filter⁺ : (∀ {a b} → a ≈ b → P a → Q b) →
            as ⊆ bs → filter P? as ⊆ filter Q? bs
  filter⁺ = HeteroProperties.⊆-filter-Sublist P? Q?

------------------------------------------------------------------------
-- reverse

module _ where

  reverseAcc⁺ : as ⊆ bs → cs ⊆ ds →
                reverseAcc cs as ⊆ reverseAcc ds bs
  reverseAcc⁺ = HeteroProperties.reverseAcc⁺

  ʳ++⁺ : as ⊆ bs → cs ⊆ ds →
         as ʳ++ cs ⊆ bs ʳ++ ds
  ʳ++⁺ = reverseAcc⁺

  reverse⁺ : as ⊆ bs → reverse as ⊆ reverse bs
  reverse⁺ = HeteroProperties.reverse⁺

  reverse⁻ : reverse as ⊆ reverse bs → as ⊆ bs
  reverse⁻ = HeteroProperties.reverse⁻

------------------------------------------------------------------------
-- merge

module _ {ℓ′} {_≤_ : Rel A ℓ′} (_≤?_ : Decidable₂ _≤_) where

  ⊆-mergeˡ : ∀ xs ys → xs ⊆ merge _≤?_ xs ys
  ⊆-mergeˡ []       ys = minimum ys
  ⊆-mergeˡ (x ∷ xs) [] = ⊆-refl
  ⊆-mergeˡ (x ∷ xs) (y ∷ ys)
   with x ≤? y  | ⊆-mergeˡ xs (y ∷ ys)
                      | ⊆-mergeˡ (x ∷ xs) ys
  ... | yes x≤y | rec | _   = ≈-refl ∷ rec
  ... | no  x≰y | _   | rec = y ∷ʳ rec

  ⊆-mergeʳ : ∀ xs ys → ys ⊆ merge _≤?_ xs ys
  ⊆-mergeʳ [] ys =  ⊆-refl
  ⊆-mergeʳ (x ∷ xs) [] = minimum (merge _≤?_ (x ∷ xs) [])
  ⊆-mergeʳ (x ∷ xs) (y ∷ ys)
   with x ≤? y  | ⊆-mergeʳ xs (y ∷ ys)
                      | ⊆-mergeʳ (x ∷ xs) ys
  ... | yes x≤y | rec | _   = x ∷ʳ rec
  ... | no  x≰y | _   | rec = ≈-refl ∷ rec

------------------------------------------------------------------------
-- Inversion lemmas
------------------------------------------------------------------------

module _ where

  ∷⁻¹ : a ≈ b → as ⊆ bs ⇔ a ∷ as ⊆ b ∷ bs
  ∷⁻¹ = HeteroProperties.∷⁻¹

  ∷ʳ⁻¹ : ¬ (a ≈ b) → a ∷ as ⊆ bs ⇔ a ∷ as ⊆ b ∷ bs
  ∷ʳ⁻¹ = HeteroProperties.∷ʳ⁻¹

------------------------------------------------------------------------
-- Other
------------------------------------------------------------------------

module _ where

  length-mono-≤ : as ⊆ bs → length as ≤ length bs
  length-mono-≤ = HeteroProperties.length-mono-≤

------------------------------------------------------------------------
-- Conversion to and from list equality

  to-≋ : length as ≡ length bs → as ⊆ bs → as ≋ bs
  to-≋ = HeteroProperties.toPointwise

------------------------------------------------------------------------
-- Empty special case

  []⊆-universal : Universal ([] ⊆_)
  []⊆-universal = HeteroProperties.Sublist-[]-universal

  []⊆-irrelevant : Irrelevant ([] ⊆_)
  []⊆-irrelevant = HeteroProperties.Sublist-[]-irrelevant

------------------------------------------------------------------------
-- (to/from)∈ is a bijection

module _ where

  open SetoidMembership S using (_∈_)

  to∈-injective : ∀ {p q : [ x ] ⊆ xs} → to∈ p ≡ to∈ q → p ≡ q
  to∈-injective = HeteroProperties.toAny-injective

  from∈-injective : ∀ {p q : x ∈ xs} → from∈ p ≡ from∈ q → p ≡ q
  from∈-injective = HeteroProperties.fromAny-injective

  to∈∘from∈≗id : ∀ (p : x ∈ xs) → to∈ (from∈ p) ≡ p
  to∈∘from∈≗id = HeteroProperties.toAny∘fromAny≗id

  [x]⊆xs⤖x∈xs : ([ x ] ⊆ xs) ⤖ (x ∈ xs)
  [x]⊆xs⤖x∈xs = HeteroProperties.Sublist-[x]-bijection

------------------------------------------------------------------------
-- Properties of Disjoint(ness) and DisjointUnion

open HeteroProperties.Disjointness {R = _≈_} public
open HeteroProperties.DisjointnessMonotonicity {R = _≈_} {S = _≈_} {T = _≈_} trans public

-- Shrinking one of two disjoint lists preserves disjointness.

-- We would have liked to define  shrinkDisjointˡ σ = shrinkDisjoint σ ⊆-refl
-- but alas, this is only possible for groupoids, not setoids in general.

shrinkDisjointˡ : ∀ {xs ys zs us} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} (σ : us ⊆ xs) →
    Disjoint τ₁ τ₂ →
    Disjoint (⊆-trans σ τ₁) τ₂
-- Not affected by σ:
shrinkDisjointˡ σ          (y   ∷ₙ d) = y             ∷ₙ shrinkDisjointˡ σ d
shrinkDisjointˡ σ          (y≈z ∷ᵣ d) = y≈z           ∷ᵣ shrinkDisjointˡ σ d
-- In σ: keep x.
shrinkDisjointˡ (u≈x ∷ σ)  (x≈z ∷ₗ d) = trans u≈x x≈z ∷ₗ shrinkDisjointˡ σ d
-- Not in σ: drop x.
shrinkDisjointˡ (x  ∷ʳ σ)  (x≈z ∷ₗ d) = _             ∷ₙ shrinkDisjointˡ σ d
shrinkDisjointˡ []         []         = []

shrinkDisjointʳ : ∀ {xs ys zs vs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} (σ : vs ⊆ ys) →
  Disjoint τ₁ τ₂ →
  Disjoint τ₁ (⊆-trans σ τ₂)
-- Not affected by σ:
shrinkDisjointʳ σ          (y   ∷ₙ d) = y             ∷ₙ shrinkDisjointʳ σ d
shrinkDisjointʳ σ          (x≈z ∷ₗ d) = x≈z           ∷ₗ shrinkDisjointʳ σ d
-- In σ: keep y.
shrinkDisjointʳ (v≈y ∷ σ)  (y≈z ∷ᵣ d) = trans v≈y y≈z ∷ᵣ shrinkDisjointʳ σ d
-- Not in σ: drop y.
shrinkDisjointʳ (y  ∷ʳ σ)  (y≈z ∷ᵣ d) = _             ∷ₙ shrinkDisjointʳ σ d
shrinkDisjointʳ []         []         = []
