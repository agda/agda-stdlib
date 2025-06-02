------------------------------------------------------------------------
-- The Agda standard library
--
-- Sorted lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Sorted.TotalOrder.Properties where

open import Data.List.Base
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Linked as Linked
  using (Linked; []; [-]; _∷_; _∷′_; head′; tail)
import Data.List.Relation.Unary.Linked.Properties as Linked
import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Relation.Binary.Sublist.Setoid as Sublist
import Data.List.Relation.Binary.Sublist.Setoid.Properties as SublistProperties
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
import Data.List.Relation.Binary.Permutation.Setoid.Properties as PermutationProperties
import Data.List.Relation.Binary.Pointwise as Pointwise
open import Data.List.Relation.Unary.Sorted.TotalOrder as Sorted hiding (head)

open import Data.Fin.Base as Fin hiding (_<_; _≤_)
import Data.Fin.Properties as Fin
open import Data.Fin.Induction
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Relation.Binary.Connected using (Connected; just)
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s; zero; suc)
import Data.Nat.Properties as ℕ
open import Function.Base using (_∘_; const)
open import Function.Definitions using (Injective)
open import Function.Bundles using (_↣_; mk↣; Inverse)
open import Level using (0ℓ)

open import Level using (Level)
open import Relation.Binary.Core using (_Preserves_⟶_; Rel)
open import Relation.Binary.Bundles using (TotalOrder; DecTotalOrder; Preorder)
import Relation.Binary.Properties.TotalOrder as TotalOrderProperties
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (contradiction)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private
  variable
    a b p ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

------------------------------------------------------------------------
-- Relationship to other predicates
------------------------------------------------------------------------

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  AllPairs⇒Sorted : ∀ {xs} → AllPairs _≤_ xs → Sorted O xs
  AllPairs⇒Sorted = Linked.AllPairs⇒Linked

  Sorted⇒AllPairs : ∀ {xs} → Sorted O xs → AllPairs _≤_ xs
  Sorted⇒AllPairs = Linked.Linked⇒AllPairs trans

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ (O₁ : TotalOrder a ℓ₁ ℓ₂) (O₂ : TotalOrder a ℓ₁ ℓ₂) where
  private
    module O₁ = TotalOrder O₁
    module O₂ = TotalOrder O₂

  map⁺ : ∀ {f xs} → f Preserves O₁._≤_ ⟶ O₂._≤_ →
         Sorted O₁ xs → Sorted O₂ (map f xs)
  map⁺ pres xs↗ = Linked.map⁺ (Linked.map pres xs↗)

  map⁻ : ∀ {f xs} → (∀ {x y} → f x O₂.≤ f y → x O₁.≤ y) →
         Sorted O₂ (map f xs) → Sorted O₁ xs
  map⁻ pres fxs↗ = Linked.map pres (Linked.map⁻ fxs↗)

------------------------------------------------------------------------
-- _++_

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  ++⁺ : ∀ {xs ys} → Sorted O xs → Connected _≤_ (last xs) (head ys) →
        Sorted O ys → Sorted O (xs ++ ys)
  ++⁺ = Linked.++⁺

------------------------------------------------------------------------
-- applyUpTo

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  applyUpTo⁺₁ : ∀ f n → (∀ {i} → suc i ℕ.< n → f i ≤ f (suc i)) →
                Sorted O (applyUpTo f n)
  applyUpTo⁺₁ = Linked.applyUpTo⁺₁

  applyUpTo⁺₂ : ∀ f n → (∀ i → f i ≤ f (suc i)) →
                Sorted O (applyUpTo f n)
  applyUpTo⁺₂ = Linked.applyUpTo⁺₂

------------------------------------------------------------------------
-- applyDownFrom

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  applyDownFrom⁺₁ : ∀ f n → (∀ {i} → suc i ℕ.< n → f (suc i) ≤ f i) →
                    Sorted O (applyDownFrom f n)
  applyDownFrom⁺₁ = Linked.applyDownFrom⁺₁

  applyDownFrom⁺₂ : ∀ f n → (∀ i → f (suc i) ≤ f i) →
                    Sorted O (applyDownFrom f n)
  applyDownFrom⁺₂ = Linked.applyDownFrom⁺₂


------------------------------------------------------------------------
-- merge

module _ (DO : DecTotalOrder a ℓ₁ ℓ₂) where
  open DecTotalOrder DO using (_≤_; _≤?_) renaming (totalOrder to O)
  open TotalOrderProperties O using (≰⇒≥)

  private
    merge-con : ∀ {v xs ys} →
                Connected _≤_ (just v) (head xs) →
                Connected _≤_ (just v) (head ys) →
                Connected _≤_ (just v) (head (merge _≤?_ xs ys))
    merge-con {xs = []}              cxs cys = cys
    merge-con {xs = x ∷ xs} {[]}     cxs cys = cxs
    merge-con {xs = x ∷ xs} {y ∷ ys} cxs cys with x ≤? y
    ... | yes x≤y = cxs
    ... | no  x≰y = cys

  merge⁺ : ∀ {xs ys} → Sorted O xs → Sorted O ys → Sorted O (merge _≤?_ xs ys)
  merge⁺ {[]}              rxs rys = rys
  merge⁺ {x ∷ xs} {[]}     rxs rys = rxs
  merge⁺ {x ∷ xs} {y ∷ ys} rxs rys
   with x ≤? y  | merge⁺ (Linked.tail rxs) rys
                      | merge⁺ rxs (Linked.tail rys)
  ... | yes x≤y | rec | _   = merge-con (head′ rxs)      (just x≤y)  ∷′ rec
  ... | no  x≰y | _   | rec = merge-con (just (≰⇒≥ x≰y)) (head′ rys) ∷′ rec

  -- Reexport ⊆-mergeˡʳ

  S = Preorder.Eq.setoid (DecTotalOrder.preorder DO)
  open Sublist S using (_⊆_)
  module SP = SublistProperties S

  ⊆-mergeˡ : ∀ xs ys → xs ⊆ merge _≤?_ xs ys
  ⊆-mergeˡ = SP.⊆-mergeˡ _≤?_

  ⊆-mergeʳ : ∀ xs ys → ys ⊆ merge _≤?_ xs ys
  ⊆-mergeʳ = SP.⊆-mergeʳ _≤?_

------------------------------------------------------------------------
-- filter

module _ (O : TotalOrder a ℓ₁ ℓ₂) {P : Pred _ p} (P? : Decidable P) where
  open TotalOrder O

  filter⁺ : ∀ {xs} → Sorted O xs → Sorted O (filter P? xs)
  filter⁺ = Linked.filter⁺ P? trans

------------------------------------------------------------------------
-- lookup

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O

  lookup-mono-≤ : ∀ {xs} → Sorted O xs →
                  ∀ {i j} → i Fin.≤ j → lookup xs i ≤ lookup xs j
  lookup-mono-≤ {x ∷ xs} xs↗ {zero}  {zero}  z≤n       = refl
  lookup-mono-≤ {x ∷ xs} xs↗ {zero}  {suc j} z≤n       = Linked.lookup trans xs↗ (just refl) (suc j)
  lookup-mono-≤ {x ∷ xs} xs↗ {suc i} {suc j} (s≤s i≤j) = lookup-mono-≤ (Sorted.tail O {y = x} xs↗) i≤j

------------------------------------------------------------------------
-- Relationship to binary relations
------------------------------------------------------------------------

module _ (O : TotalOrder a ℓ₁ ℓ₂) where
  open TotalOrder O renaming (Carrier to A)
  open Equality Eq.setoid
  open module Perm = Permutation Eq.setoid hiding (refl; trans)
  open PermutationProperties Eq.setoid
  open PosetReasoning poset

  -- Proof that any two sorted lists that are a permutation of each
  -- other are pointwise equal
  private
    module _ {x y xs′ ys′} (xs↭ys : x ∷ xs′ ↭ y ∷ ys′) where
      xs ys : List _
      xs = x ∷ xs′
      ys = y ∷ ys′

      indices : ∀ {xs ys} → xs ↭ ys → Fin (length xs) → Fin (length ys)
      indices xs↭ys = Inverse.to (Permutation.toFin xs↭ys)

      indices-injective : ∀ {xs ys} (xs↭ys : xs ↭ ys) → Injective _≡_ _≡_ (indices xs↭ys)
      indices-injective = {!Inverse.injective ? !}

      lower : ∀ {m n} (i : Fin m) → .(toℕ i ℕ.< n) → Fin n
      lower {suc _} {suc n} zero    leq = zero
      lower {suc _} {suc n} (suc i) leq = suc (lower i (ℕ.≤-pred leq))

      lower-injective : ∀ {m n} (i j : Fin m)
                        (i<n : toℕ i ℕ.< n) (j<n : toℕ j ℕ.< n)  →
                        lower i i<n ≡ lower j j<n → i ≡ j
      lower-injective {suc _} {suc n} zero    zero    i<n       j<n       eq = P.refl
      lower-injective {suc _} {suc n} (suc i) (suc j) (s≤s i<n) (s≤s j<n) eq =
        P.cong suc (lower-injective i j i<n j<n (Fin.suc-injective eq))

      π : Fin _ → Fin _
      π = indices xs↭ys

      π-contractingIn[_-_] : Fin (length xs) → Fin (length ys) → Set
      π-contractingIn[ i - j ] = ∀ {k} → i Fin.< k → toℕ k ℕ.≤ toℕ j → π k Fin.< j

      π-contractingIn-≡ : ∀ {i j} → toℕ i ≡ toℕ j → π-contractingIn[ i - j ]
      π-contractingIn-≡ i≡j j<k k≤i = contradiction (ℕ.<-≤-trans j<k k≤i) (ℕ.<-irrefl i≡j)

      π-contractingIn-pred : ∀ {i j} → π-contractingIn[ i - j ] →
                             j Fin.≰ π i → zero {length xs} Fin.< i →
                             π-contractingIn[ pred i - j ]
      π-contractingIn-pred i@{suc _} {j} contr j≰πᵢ _ {k} i∸1≤k k≤j with i Fin.≟ k
      ... | yes P.refl = ℕ.≰⇒> j≰πᵢ
      ... | no  i≢k    = contr (ℕ.≤∧≢⇒< i≤k (i≢k ∘ Fin.toℕ-injective)) k≤j
        where i≤k = P.subst (ℕ._≤ toℕ k) (Fin.toℕ-inject₁ i) i∸1≤k

      π-contractingIn-injection : ∀ {j} → π-contractingIn[ zero - j ] →
                                  j Fin.≰ π zero → Fin′ (suc j) ↣ Fin′ j
      π-contractingIn-injection {j} π-contracting j≰π₀ = mk↣ f-injective
        where
        j<∣xs∣ : toℕ j ℕ.< length xs
        j<∣xs∣ = P.subst (toℕ j ℕ.<_) (P.sym (xs↭ys⇒|xs|≡|ys| xs↭ys)) (Fin.toℕ<n j)

        k≤j⇒πₖ<j : (k : Fin′ (suc j)) → π (Fin.inject≤ k j<∣xs∣) Fin.< j
        k≤j⇒πₖ<j zero    = ℕ.≰⇒> j≰π₀
        k≤j⇒πₖ<j (suc k) = π-contracting (s≤s z≤n) k≤j
          where k≤j = P.subst (ℕ._≤ toℕ j) (P.sym (Fin.toℕ-inject≤ (suc k) j<∣xs∣)) (Fin.toℕ<n k)

        f : Fin′ (suc j) → Fin′ j
        f k = lower (π (Fin.inject≤ k j<∣xs∣)) (k≤j⇒πₖ<j k)

        f-injective : ∀ {k l} → f k ≡ f l → k ≡ l
        f-injective {k} {l} = Fin.inject≤-injective _ _ k l
          ∘ indices-injective xs↭ys
          ∘ lower-injective _ _ (k≤j⇒πₖ<j k) (k≤j⇒πₖ<j l)

      ↗↭↗⇒≤ : Sorted O xs → Sorted O ys →
              ∀ {i} → Acc Fin._<_ i →
              ∀ {j} → π-contractingIn[ i - j ] →
              ∀ {v} → lookup xs i ≤ v → lookup ys j ≤ v
      ↗↭↗⇒≤ xs↗ ys↗ {i} (acc rec) {j} π-contr {v} xsᵢ≤v with j Fin.≤? π i | i Fin.≟ zero
      ...   | yes j≤πᵢ | _          = begin
        lookup ys j      ≤⟨  {!!} ⟩ --lookup-mono-≤ O ys↗ {i = π i} {j = j} j≤πᵢ ⟩
        lookup ys (π i)  ≈˘⟨ indices-lookup xs↭ys i ⟩
        lookup xs i      ≤⟨  xsᵢ≤v ⟩
        v                ∎
      ...   | no  j≰πᵢ | yes P.refl = contradiction (π-contractingIn-injection π-contr j≰πᵢ) {!!} --(Fin.pigeonhole′ ℕ.≤-refl)
      ...   | no  j≰πᵢ | no  i≢0    = {!!}
{-
↗↭↗⇒≤ xs↗ ys↗ (rec (pred i) (ℕ.≤-reflexive ?)) -- (Fin.suc-pred i≢0)))
        (π-contractingIn-pred π-contr j≰πᵢ ?) --(Fin.i≢0⇒i>0 i≢0))
        (trans ? ?) --(lookup-mono-≤ O xs↗ (Fin.pred≤ i)) xsᵢ≤v)
        -}
{-
  ↗↭↗⇒≋ : ∀ {xs ys} → Sorted O xs → Sorted O ys → xs ↭ ys → xs ≋ ys
  ↗↭↗⇒≋ {[]}    {[]}    _   _   _     = []
  ↗↭↗⇒≋ {[]}    {_ ∷ _} _   _   []↭ys = contradiction []↭ys ¬[]↭x∷xs
  ↗↭↗⇒≋ {_ ∷ _} {[]}    _   _   xs↭[] = contradiction xs↭[] ¬x∷xs↭[]
  ↗↭↗⇒≋ {_ ∷ _} {_ ∷ _} xs↗ ys↗ xs↭ys = lookup⁻ (xs↭ys⇒|xs|≡|ys| xs↭ys) (λ i≡j → antisym
    (↗↭↗⇒≤ (↭-sym xs↭ys) ys↗ xs↗ (<-wellFounded _) (π-contractingIn-≡ (↭-sym xs↭ys) (P.sym i≡j)) refl)
    (↗↭↗⇒≤        xs↭ys  xs↗ ys↗ (<-wellFounded _) (π-contractingIn-≡        xs↭ys         i≡j)  refl))
-}
