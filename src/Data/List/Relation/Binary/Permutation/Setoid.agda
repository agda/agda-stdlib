------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Permutation.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open import Data.List.Base using (List; _∷_)
import Data.List.Relation.Binary.Permutation.Homogeneous as Homogeneous
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Function.Base using (_∘′_)
open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; LeftTrans; RightTrans)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Reasoning.Syntax
open import Relation.Binary.Structures using (IsEquivalence)

open module ≈ = Setoid S using (_≈_) renaming (Carrier to A)
open ≋ S using (_≋_; _∷_; ≋-refl; ≋-sym; ≋-trans)

------------------------------------------------------------------------
-- Definition, based on `Homogeneous`

open Homogeneous public
  using (refl; prep; swap; trans)

infix 3 _↭_

_↭_ : Rel (List A) (a ⊔ ℓ)
_↭_ = Homogeneous.Permutation _≈_

steps = Homogeneous.steps {R = _≈_}

------------------------------------------------------------------------
-- Constructor aliases

-- Constructor alias

↭-reflexive-≋ : _≋_ ⇒ _↭_
↭-reflexive-≋ = refl

↭-trans : Transitive _↭_
↭-trans = trans

-- These provide aliases for `swap` and `prep` when the elements being
-- swapped or prepended are propositionally equal

↭-prep : ∀ x {xs ys} → xs ↭ ys → x ∷ xs ↭ x ∷ ys
↭-prep x xs↭ys = prep ≈.refl xs↭ys

↭-swap : ∀ x y {xs ys} → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
↭-swap x y xs↭ys = swap ≈.refl ≈.refl xs↭ys

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = ↭-reflexive-≋ ≋-refl

↭-refl : Reflexive _↭_
↭-refl = ↭-reflexive refl

↭-sym : Symmetric _↭_
↭-sym = Homogeneous.sym ≈.sym

-- As with the existing proofs `↭-respʳ-≋` and `↭-respˡ-≋` in `Setoid.Properties`
-- (which appeal to symmetry of the underlying equality, and its effect on the
-- proofs of symmetry for both pointwise equality and permutation) to the effect
-- that _↭_ respects _≋_ on the left and right, such arguments can be both
-- streamlined, and used to define a 'smart' constructor `↭-trans′` for transitivity.
--
-- The arguments below show how proofs of permutation can have all transitive
-- compositions with instances of `refl` pushed to the leaves of derivations,
-- thereby addressing the inefficiencies analysed in issue #1113
--
-- Conjecture: these transformations are `steps` invariant, but that is moot,
-- given their use here, and in `Setoid.Properties.↭-split` (without requiring
-- WF-induction on `steps`) to enable a new, sharper, analysis of lists `xs`
-- such that `xs ↭ ys ++ [ x ] ++ zs` in terms of `x`, `ys`, and `zs`.

↭-transˡ-≋ : LeftTrans _≋_ _↭_
↭-transˡ-≋ xs≋ys               (refl ys≋zs)
  = refl (≋-trans xs≋ys ys≋zs)
↭-transˡ-≋ (x≈y ∷ xs≋ys)       (prep y≈z ys↭zs)
  = prep (≈.trans x≈y y≈z) (↭-transˡ-≋ xs≋ys ys↭zs)
↭-transˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ ys↭zs)
  = swap (≈.trans x≈y eq₁) (≈.trans w≈z eq₂) (↭-transˡ-≋ xs≋ys ys↭zs)
↭-transˡ-≋ xs≋ys               (trans ys↭ws ws↭zs)
  = trans (↭-transˡ-≋ xs≋ys ys↭ws) ws↭zs

↭-transʳ-≋ : RightTrans _↭_ _≋_
↭-transʳ-≋ (refl xs≋ys)         ys≋zs
  = refl (≋-trans xs≋ys ys≋zs)
↭-transʳ-≋ (prep x≈y xs↭ys)     (y≈z ∷ ys≋zs)
  = prep (≈.trans x≈y y≈z) (↭-transʳ-≋ xs↭ys ys≋zs)
↭-transʳ-≋ (swap eq₁ eq₂ xs↭ys) (x≈w ∷ y≈z ∷ ys≋zs)
  = swap (≈.trans eq₁ y≈z) (≈.trans eq₂ x≈w) (↭-transʳ-≋ xs↭ys ys≋zs)
↭-transʳ-≋ (trans xs↭ws ws↭ys)  ys≋zs
  = trans xs↭ws (↭-transʳ-≋ ws↭ys ys≋zs)

↭-trans′ : Transitive _↭_
↭-trans′ (refl xs≋ys) ys↭zs = ↭-transˡ-≋ xs≋ys ys↭zs
↭-trans′ xs↭ys (refl ys≋zs) = ↭-transʳ-≋ xs↭ys ys≋zs
↭-trans′ xs↭ys ys↭zs        = trans xs↭ys ys↭zs

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = record
    { refl  = ↭-refl
    ; sym   = ↭-sym
    ; trans = ↭-trans
    }

↭-setoid : Setoid _ _
↭-setoid = record { isEquivalence = ↭-isEquivalence }

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs

module PermutationReasoning where

  private module Base = ≈-Reasoning ↭-setoid

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)
    renaming (≈-go to ↭-go)

  open ↭-syntax _IsRelatedTo_ _IsRelatedTo_ ↭-go ↭-sym public
  open ≋-syntax _IsRelatedTo_ _IsRelatedTo_ (↭-go ∘′ ↭-reflexive-≋) ≋-sym public

  -- Some extra combinators that allow us to skip certain elements

  infixr 2 step-swap step-prep

  -- Skip reasoning on the first element
  step-prep : ∀ x xs {ys zs : List A} → (x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ xs) IsRelatedTo zs
  step-prep x xs rel xs↭ys = ↭-go (↭-prep x xs↭ys) rel

  -- Skip reasoning about the first two elements
  step-swap : ∀ x y xs {ys zs : List A} → (y ∷ x ∷ ys) IsRelatedTo zs →
              xs ↭ ys → (x ∷ y ∷ xs) IsRelatedTo zs
  step-swap x y xs rel xs↭ys = ↭-go (↭-swap x y xs↭ys) rel

  syntax step-prep x xs y↭z x↭y = x ∷ xs <⟨ x↭y ⟩ y↭z
  syntax step-swap x y xs y↭z x↭y = x ∷ y ∷ xs <<⟨ x↭y ⟩ y↭z
