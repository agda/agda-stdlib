------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers: properties of sum and product
--
-- Issue #2553: this is a compatibility stub module,
-- ahead of a more thorough breaking set of changes.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.ListAction.Properties where

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.List.Base using (List; []; _∷_; _++_; map; foldl)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Properties as Listₚ
import Data.List.Membership.Propositional.Properties as ∈ₚ
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭⇒↭ₛ)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties
  using (foldr-commMonoid)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (here; there)

open import Data.Nat.Base as ℕ using (ℕ; _+_; _*_; _^_; NonZero; _≤_; _≥_)
open import Data.Nat.Divisibility using (_∣_; m∣m*n; ∣n⇒∣m*n)
open import Data.Nat.ListAction using (sum; product; minimum; maximum)
open import Data.Nat.Properties as ℕₚ
  using (+-assoc; *-assoc; *-identityˡ; m*n≢0; m≤m*n; m≤n⇒m≤o*n
        ; +-0-commutativeMonoid; *-1-commutativeMonoid
        ; *-zeroˡ; *-zeroʳ; *-distribˡ-+; *-distribʳ-+
        ; ^-zeroˡ; ^-distribʳ-*; m*n≡0⇒m≡0∨n≡0)

open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Function.Base using (_∘′_)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    m n : ℕ
    ms ns : List ℕ


------------------------------------------------------------------------
-- Properties

-- sum

sum-++ : ∀ ms ns → sum (ms ++ ns) ≡ sum ms + sum ns
sum-++ []       ns = refl
sum-++ (m ∷ ms) ns = begin
  m + sum (ms ++ ns)     ≡⟨ cong (m +_) (sum-++ ms ns) ⟩
  m + (sum ms + sum ns)  ≡⟨ +-assoc m _ _ ⟨
  (m + sum ms) + sum ns  ∎
  where open ≡-Reasoning

*-distribˡ-sum : ∀ m ns → m * sum ns ≡ sum (map (m *_) ns)
*-distribˡ-sum m [] = *-zeroʳ m
*-distribˡ-sum m (n ∷ ns) = trans (*-distribˡ-+ m n (sum ns)) (cong (m * n +_) (*-distribˡ-sum m ns))

*-distribʳ-sum : ∀ m ns → sum ns * m ≡ sum (map (_* m) ns)
*-distribʳ-sum m [] = *-zeroˡ m
*-distribʳ-sum m (n ∷ ns) = trans (*-distribʳ-+ m n (sum ns)) (cong (n * m +_) (*-distribʳ-sum m ns))

sum-↭ : sum Preserves _↭_ ⟶ _≡_
sum-↭ p = foldr-commMonoid ℕ-+-0.setoid ℕ-+-0.isCommutativeMonoid (↭⇒↭ₛ p)
  where module ℕ-+-0 = CommutativeMonoid +-0-commutativeMonoid


-- product

product-++ : ∀ ms ns → product (ms ++ ns) ≡ product ms * product ns
product-++ []       ns = sym (*-identityˡ _)
product-++ (m ∷ ms) ns = begin
  m * product (ms ++ ns)         ≡⟨ cong (m *_) (product-++ ms ns) ⟩
  m * (product ms * product ns)  ≡⟨ *-assoc m _ _ ⟨
  (m * product ms) * product ns  ∎
  where open ≡-Reasoning

∈⇒∣product : n ∈ ns → n ∣ product ns
∈⇒∣product {ns = n ∷ ns} (here  refl) = m∣m*n (product ns)
∈⇒∣product {ns = m ∷ ns} (there n∈ns) = ∣n⇒∣m*n m (∈⇒∣product n∈ns)

product-locate : ∀ ns → product ns ≡ 0 → 0 ∈ ns
product-locate (n ∷ ns) =
  [ here ∘′ sym , there ∘′ product-locate ns ]′ ∘′ m*n≡0⇒m≡0∨n≡0 n


product≢0 : All NonZero ns → NonZero (product ns)
product≢0 []           = _
product≢0 (n≢0 ∷ ns≢0) = m*n≢0 _ _ {{n≢0}} {{product≢0 ns≢0}}

∈⇒≤product : All NonZero ns → n ∈ ns → n ≤ product ns
∈⇒≤product (n≢0 ∷ ns≢0) (here refl)  = m≤m*n _ _ {{product≢0 ns≢0}}
∈⇒≤product (n≢0 ∷ ns≢0) (there n∈ns) = m≤n⇒m≤o*n _ {{n≢0}} (∈⇒≤product ns≢0 n∈ns)

^-distribʳ-product : ∀ m ns → product ns ^ m ≡ product (map (_^ m) ns)
^-distribʳ-product m [] = ^-zeroˡ m
^-distribʳ-product m (n ∷ ns) = trans (^-distribʳ-* m n (product ns)) (cong (n ^ m *_) (^-distribʳ-product m ns))

product-↭ : product Preserves _↭_ ⟶ _≡_
product-↭ p = foldr-commMonoid ℕ-*-1.setoid ℕ-*-1.isCommutativeMonoid (↭⇒↭ₛ p)
  where module ℕ-*-1 = CommutativeMonoid *-1-commutativeMonoid


-- minimum

minimum-spec : ∀ n ms → minimum n ms ≡ foldl ℕ._⊓_ n ms
minimum-spec = Listₚ.foldl-cong (λ m n → sym (ℕₚ.⊓≡⊓′ m n))

minimum-selective : ∀ n ms → minimum n ms ∈ n ∷ ms
minimum-selective n ms =
  [ here ∘′ trans (minimum-spec n ms)
  , there ∘′ subst (_∈ _) (sym (minimum-spec n ms))
  ]′ (∈ₚ.foldl-selective ℕₚ.⊓-sel n ms)

minimum-≤ : ∀ n ms {k} → k ∈ (n ∷ ms) → minimum n ms ≤ k
minimum-≤ n []           (here refl) = ℕₚ.≤-refl
minimum-≤ n mms@(m ∷ ms) (here refl) = let open ℕₚ.≤-Reasoning in begin
  minimum n mms         ≡⟨⟩
  minimum (n ℕ.⊓′ m) ms ≤⟨ minimum-≤ (n ℕ.⊓′ m) ms (here refl) ⟩
  n ℕ.⊓′ m              ≡⟨ ℕₚ.⊓≡⊓′ n m ⟨
  n ℕ.⊓ m               ≤⟨ ℕₚ.m⊓n≤m n m ⟩
  n                     ∎
minimum-≤ n mms@(m ∷ ms) (there (here refl)) = let open ℕₚ.≤-Reasoning in begin
  minimum n mms         ≡⟨⟩
  minimum (n ℕ.⊓′ m) ms ≤⟨ minimum-≤ (n ℕ.⊓′ m) ms (here refl) ⟩
  n ℕ.⊓′ m              ≡⟨ ℕₚ.⊓≡⊓′ n m ⟨
  n ℕ.⊓ m               ≤⟨ ℕₚ.m⊓n≤n n m ⟩
  m                     ∎
minimum-≤ n mms@(m ∷ ms) (there (there k∈)) = let open ℕₚ.≤-Reasoning in begin
  minimum n mms         ≡⟨⟩
  minimum (n ℕ.⊓′ m) ms ≤⟨ minimum-≤ (n ℕ.⊓′ m) ms (there k∈) ⟩
  _                     ∎


-- maximum

maximum-spec : ∀ n ms → maximum n ms ≡ foldl ℕ._⊔_ n ms
maximum-spec = Listₚ.foldl-cong (λ m n → sym (ℕₚ.⊔≡⊔′ m n))

maximum-selective : ∀ n ms → maximum n ms ∈ n ∷ ms
maximum-selective n ms =
  [ here ∘′ trans (maximum-spec n ms)
  , there ∘′ subst (_∈ _) (sym (maximum-spec n ms))
  ]′ (∈ₚ.foldl-selective ℕₚ.⊔-sel n ms)

maximum-≥ : ∀ n ms {k} → k ∈ (n ∷ ms) → maximum n ms ≥ k
maximum-≥ n []           (here refl) = ℕₚ.≤-refl
maximum-≥ n mms@(m ∷ ms) (here refl) = let open ℕₚ.≤-Reasoning in begin
  n                     ≤⟨ ℕₚ.m≤m⊔n n m ⟩
  n ℕ.⊔ m               ≡⟨ ℕₚ.⊔≡⊔′ n m ⟩
  n ℕ.⊔′ m              ≤⟨ maximum-≥ (n ℕ.⊔′ m) ms (here refl) ⟩
  maximum (n ℕ.⊔′ m) ms ≡⟨⟩
  maximum n mms         ∎
maximum-≥ n mms@(m ∷ ms) (there (here refl)) = let open ℕₚ.≤-Reasoning in begin
  m                     ≤⟨ ℕₚ.m≤n⊔m n m ⟩
  n ℕ.⊔ m               ≡⟨ ℕₚ.⊔≡⊔′ n m ⟩
  n ℕ.⊔′ m              ≤⟨ maximum-≥ (n ℕ.⊔′ m) ms (here refl) ⟩
  maximum (n ℕ.⊔′ m) ms ≡⟨⟩
  maximum n mms         ∎
maximum-≥ n mms@(m ∷ ms) (there (there k∈)) = let open ℕₚ.≤-Reasoning in begin
  _                     ≤⟨ maximum-≥ (n ℕ.⊔′ m) ms (there k∈) ⟩
  maximum n mms         ≡⟨⟩
  maximum (n ℕ.⊔′ m) ms ∎
