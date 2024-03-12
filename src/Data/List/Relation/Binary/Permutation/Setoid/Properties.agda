------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutations using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Permutation.Setoid.Properties
  {a ℓ} (S : Setoid a ℓ)
  where

open import Algebra
open import Data.Bool.Base using (true; false)
open import Data.List.Base
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.Unique.Setoid as Unique
import Data.List.Membership.Setoid as Membership
import Data.List.Properties as List
open import Data.Nat hiding (_⊔_)
open import Data.Product.Base using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Function.Base using (_∘_; _⟨_⟩_; flip)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core
  using (Rel; _⇒_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Definitions as B hiding (Decidable)
open import Relation.Binary.Properties.Setoid S using (≉-resp₂)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_ ; refl; sym; cong; cong₂; subst; _≢_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Nullary.Decidable using (yes; no; does)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; Decidable)

import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
import Data.List.Relation.Binary.Permutation.Homogeneous as Properties

open Setoid S
  using (_≈_)
  renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open Permutation S
open Membership S
open Unique S using (Unique)
open module ≋ = Equality S
  using (_≋_; []; _∷_; ≋-refl; ≋-sym; ≋-trans)

private
  variable
    b p r : Level
    xs ys zs : List A
    x y z v w : A
    P : Pred A p
    R : Rel A r

------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

All-resp-↭ : P Respects _≈_ → (All P) Respects _↭_
All-resp-↭ = Properties.All-resp-↭

Any-resp-↭ : P Respects _≈_ → (Any P) Respects _↭_
Any-resp-↭ = Properties.Any-resp-↭

AllPairs-resp-↭ : Symmetric R → R Respects₂ _≈_ → (AllPairs R) Respects _↭_
AllPairs-resp-↭ = Properties.AllPairs-resp-↭

∈-resp-↭ : (x ∈_) Respects _↭_
∈-resp-↭ = Any-resp-↭ (flip ≈-trans)

Unique-resp-↭ : Unique Respects _↭_
Unique-resp-↭ = AllPairs-resp-↭ (_∘ ≈-sym) ≉-resp₂

------------------------------------------------------------------------
-- Relationships to other relations
------------------------------------------------------------------------

≋⇒↭ : _≋_ ⇒ _↭_
≋⇒↭ = ↭-pointwise

↭-respʳ-≋ : _↭_ Respectsʳ _≋_
↭-respʳ-≋ = Properties.↭-respʳ-≋ ≈-trans

↭-respˡ-≋ : _↭_ Respectsˡ _≋_
↭-respˡ-≋ = Properties.↭-respˡ-≋ ≈-sym ≈-trans

↭-transˡ-≋ : LeftTrans _≋_ _↭_
↭-transˡ-≋ = Properties.↭-transˡ-≋ ≈-trans

↭-transʳ-≋ : RightTrans _↭_ _≋_
↭-transʳ-≋ = Properties.↭-transʳ-≋ ≈-trans

module _ (≈-sym-involutive : ∀ {x y} → (p : x ≈ y) → ≈-sym (≈-sym p) ≡ p)
         where

  ↭-sym-involutive : (p : xs ↭ ys) → ↭-sym (↭-sym p) ≡ p
  ↭-sym-involutive = Properties.↭-sym-involutive′ ≈-sym-involutive

------------------------------------------------------------------------
-- Properties of steps (legacy)
------------------------------------------------------------------------

0<steps : (xs↭ys : xs ↭ ys) → 0 < steps xs↭ys
0<steps = Properties.0<steps

steps-respˡ : (ys≋xs : ys ≋ xs) (ys↭zs : ys ↭ zs) →
              steps (↭-respˡ-≋ ys≋xs ys↭zs) ≡ steps ys↭zs
steps-respˡ = Properties.steps-respˡ ≈-sym ≈-trans

steps-respʳ : (xs≋ys : xs ≋ ys) (zs↭xs : zs ↭ xs) →
              steps (↭-respʳ-≋ xs≋ys zs↭xs) ≡ steps zs↭xs
steps-respʳ = Properties.steps-respʳ ≈-trans

------------------------------------------------------------------------
-- Properties of list functions
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Permutations of empty and singleton lists

↭-[]-invˡ : [] ↭ xs → xs ≡ []
↭-[]-invˡ = Properties.↭-[]-invˡ

↭-[]-invʳ : xs ↭ [] → xs ≡ []
↭-[]-invʳ = Properties.↭-[]-invʳ

¬x∷xs↭[] : ¬ ((x ∷ xs) ↭ [])
¬x∷xs↭[] = Properties.¬x∷xs↭[]

↭-singleton⁻¹ : xs ↭ [ x ] → ∃ λ y → xs ≡ [ y ] × y ≈ x
↭-singleton⁻¹ = Properties.↭-singleton⁻¹ ≈-trans

------------------------------------------------------------------------
-- length

↭-length : xs ↭ ys → length xs ≡ length ys
↭-length = Properties.↭-length

------------------------------------------------------------------------
-- map

module _ (T : Setoid b r) where

  open Setoid T using () renaming (_≈_ to _≈′_)
  open Permutation T using () renaming (_↭_ to _↭′_)

  map⁺ : ∀ {f} → f Preserves _≈_ ⟶ _≈′_ →
         xs ↭ ys → map f xs ↭′ map f ys
  map⁺ pres = Properties.map⁺ pres


------------------------------------------------------------------------
-- _++_

shift : v ≈ w → ∀ xs ys → xs ++ [ v ] ++ ys ↭ w ∷ xs ++ ys
shift v≈w xs ys = Properties.shift ≈-refl ≈-sym ≈-trans v≈w xs {ys}

↭-shift : ∀ xs {ys} → xs ++ [ v ] ++ ys ↭ v ∷ xs ++ ys
↭-shift xs {ys} = shift ≈-refl xs ys

++⁺ʳ : ∀  zs → xs ↭ ys → xs ++ zs ↭ ys ++ zs
++⁺ʳ = Properties.++⁺ʳ ≈-refl

++⁺ˡ : ∀ xs {ys zs} → ys ↭ zs → xs ++ ys ↭ xs ++ zs
++⁺ˡ []       ys↭zs = ys↭zs
++⁺ˡ (x ∷ xs) ys↭zs = ↭-prep x (++⁺ˡ xs ys↭zs)

++⁺ : _++_ Preserves₂ _↭_ ⟶ _↭_ ⟶ _↭_
++⁺ ws↭xs ys↭zs = ↭-trans (++⁺ʳ _ ws↭xs) (++⁺ˡ _ ys↭zs)

-- Algebraic properties

++-identityˡ : LeftIdentity _↭_ [] _++_
++-identityˡ xs = ↭-refl

++-identityʳ : RightIdentity _↭_ [] _++_
++-identityʳ xs = ↭-reflexive (List.++-identityʳ xs)

++-identity : Identity _↭_ [] _++_
++-identity = ++-identityˡ , ++-identityʳ

++-assoc : Associative _↭_ _++_
++-assoc xs ys zs = ↭-reflexive (List.++-assoc xs ys zs)

++-comm : Commutative _↭_ _++_
++-comm []       ys = ↭-sym (++-identityʳ ys)
++-comm (x ∷ xs) ys = begin
  x ∷ xs ++ ys   <⟨ ++-comm xs ys ⟩
  x ∷ ys ++ xs   ↭⟨ ↭-shift ys ⟨
  ys ++ (x ∷ xs) ∎
  where open PermutationReasoning

-- Structures

++-isMagma : IsMagma _↭_ _++_
++-isMagma = record
  { isEquivalence = ↭-isEquivalence
  ; ∙-cong        = ++⁺
  }

++-isSemigroup : IsSemigroup _↭_ _++_
++-isSemigroup = record
  { isMagma = ++-isMagma
  ; assoc   = ++-assoc
  }

++-isMonoid : IsMonoid _↭_ _++_ []
++-isMonoid = record
  { isSemigroup = ++-isSemigroup
  ; identity    = ++-identity
  }

++-isCommutativeMonoid : IsCommutativeMonoid _↭_ _++_ []
++-isCommutativeMonoid = record
  { isMonoid = ++-isMonoid
  ; comm     = ++-comm
  }

-- Bundles

++-magma : Magma a (a ⊔ ℓ)
++-magma = record
  { isMagma = ++-isMagma
  }

++-semigroup : Semigroup a (a ⊔ ℓ)
++-semigroup = record
  { isSemigroup = ++-isSemigroup
  }

++-monoid : Monoid a (a ⊔ ℓ)
++-monoid = record
  { isMonoid = ++-isMonoid
  }

++-commutativeMonoid : CommutativeMonoid a (a ⊔ ℓ)
++-commutativeMonoid = record
  { isCommutativeMonoid = ++-isCommutativeMonoid
  }

-- Some other useful lemmas

zoom : ∀ h {t xs ys} → xs ↭ ys → h ++ xs ++ t ↭ h ++ ys ++ t
zoom h {t} = ++⁺ˡ h ∘ ++⁺ʳ t

inject : ∀ v {ws xs ys zs} → ws ↭ ys → xs ↭ zs →
         ws ++ [ v ] ++ xs ↭ ys ++ [ v ] ++ zs
inject v ws↭ys xs↭zs = ↭-trans (++⁺ˡ _ (↭-prep _ xs↭zs)) (++⁺ʳ _ ws↭ys)

shifts : ∀ xs ys {zs} → xs ++ ys ++ zs ↭ ys ++ xs ++ zs
shifts xs ys {zs} = begin
   xs ++ ys  ++ zs ↭⟨ ++-assoc xs ys zs ⟨
  (xs ++ ys) ++ zs ↭⟨ ++⁺ʳ zs (++-comm xs ys) ⟩
  (ys ++ xs) ++ zs ↭⟨ ++-assoc ys xs zs ⟩
   ys ++ xs  ++ zs ∎
  where open PermutationReasoning

dropMiddleElement-≋ : ∀ {x} ws xs {ys} {zs} →
           ws ++ [ x ] ++ ys ≋ xs ++ [ x ] ++ zs →
           ws ++ ys ↭ xs ++ zs
dropMiddleElement-≋ = Properties.dropMiddleElement-≋ ≈-refl ≈-sym ≈-trans

dropMiddleElement : ∀ {v} ws xs {ys zs} →
                    ws ++ [ v ] ++ ys ↭ xs ++ [ v ] ++ zs →
                    ws ++ ys ↭ xs ++ zs
dropMiddleElement = Properties.dropMiddleElement ≈-refl ≈-sym ≈-trans

dropMiddle : ∀ {vs} ws xs {ys zs} →
             ws ++ vs ++ ys ↭ xs ++ vs ++ zs →
             ws ++ ys ↭ xs ++ zs
dropMiddle {[]}     ws xs p = p
dropMiddle {v ∷ vs} ws xs p = dropMiddle ws xs (dropMiddleElement ws xs p)

split-↭ : ∀ v as bs {xs} → xs ↭ as ++ [ v ] ++ bs →
          ∃₂ λ ps qs → xs ≋ ps ++ [ v ] ++ qs × ps ++ qs ↭ as ++ bs
split-↭ v as bs p = Properties.split-↭ ≈-refl ≈-trans v as bs p

split : ∀ v as bs {xs} → xs ↭ as ++ [ v ] ++ bs → ∃₂ λ ps qs → xs ≋ ps ++ [ v ] ++ qs
split v as bs p with ps , qs , eq , _ ← split-↭ v as bs p = ps , qs , eq


------------------------------------------------------------------------
-- _∷_

drop-∷ : x ∷ xs ↭ x ∷ ys → xs ↭ ys
drop-∷ = dropMiddleElement [] []

------------------------------------------------------------------------
-- filter

module _ (P? : Decidable P) (P≈ : P Respects _≈_) where

  filter⁺ : xs ↭ ys → filter P? xs ↭ filter P? ys
  filter⁺ = Properties.filter⁺ ≈-sym P? P≈

------------------------------------------------------------------------
-- partition

module _ (P? : Decidable P) where

  partition-↭ : ∀ xs → let ys , zs = partition P? xs in xs ↭ ys ++ zs
  partition-↭ []       = ↭-refl
  partition-↭ (x ∷ xs) with does (P? x)
  ... | true  = ↭-prep x (partition-↭ xs)
  ... | false = ↭-trans (↭-prep x (partition-↭ xs)) (↭-sym (↭-shift _))

------------------------------------------------------------------------
-- _∷ʳ_

∷↭∷ʳ : ∀ x xs → x ∷ xs ↭ xs ∷ʳ x
∷↭∷ʳ x xs = ↭-sym (begin
  xs ++ [ x ]   ↭⟨ ↭-shift xs ⟩
  x ∷ xs ++ []  ≡⟨ List.++-identityʳ _ ⟩
  x ∷ xs        ∎)
  where open PermutationReasoning

------------------------------------------------------------------------
-- ʳ++

++↭ʳ++ : ∀ xs ys → xs ++ ys ↭ xs ʳ++ ys
++↭ʳ++ []       ys = ↭-refl
++↭ʳ++ (x ∷ xs) ys = ↭-trans (↭-sym (↭-shift xs)) (++↭ʳ++ xs (x ∷ ys))

------------------------------------------------------------------------
-- reverse

↭-reverse : ∀ xs → reverse xs ↭ xs
↭-reverse [] = ↭-refl
↭-reverse (x ∷ xs) = begin
  reverse (x ∷ xs) ≡⟨ List.unfold-reverse x xs ⟩
  reverse xs ∷ʳ x  ↭⟨ ∷↭∷ʳ x (reverse xs) ⟨
  x ∷ reverse xs   <⟨ ↭-reverse xs ⟩
  x ∷ xs           ∎
  where open PermutationReasoning

------------------------------------------------------------------------
-- merge

module _ (R? : B.Decidable R) where

  merge-↭ : ∀ xs ys → merge R? xs ys ↭ xs ++ ys
  merge-↭ []            []            = ↭-refl
  merge-↭ []            y∷ys@(_ ∷ _)  = ↭-refl
  merge-↭ x∷xs@(_ ∷ _)  []            = ↭-sym (++-identityʳ x∷xs)
  merge-↭ x∷xs@(x ∷ xs) y∷ys@(y ∷ ys)
    with does (R? x y) | merge-↭ xs y∷ys | merge-↭ x∷xs ys
  ... | true  | rec | _   = ↭-prep x rec
  ... | false | _   | rec = begin
    y ∷ merge R? x∷xs ys <⟨ rec ⟩
    y ∷ x∷xs ++ ys       ↭⟨ ↭-shift x∷xs ⟨
    x∷xs ++ y∷ys         ≡⟨ List.++-assoc [ x ] xs y∷ys ⟨
    x∷xs ++ y∷ys         ∎
    where open PermutationReasoning

------------------------------------------------------------------------
-- foldr of Commutative Monoid

module _ {_∙_ : Op₂ A} {ε : A}
         (isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε) where

  private
    commutativeMonoid : CommutativeMonoid _ _
    commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  foldr-commMonoid : xs ↭ ys → foldr _∙_ ε xs ≈ foldr _∙_ ε ys
  foldr-commMonoid = Properties.foldr-commMonoid commutativeMonoid
