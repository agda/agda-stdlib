------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties of the `Homogeneous` definition of permutation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel; _⇒_; _Preserves_⟶_)

module Data.List.Relation.Binary.Permutation.Homogeneous.Properties.Core
  {a r} {A : Set a} {R : Rel A r} where

open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; []; _∷_)
open import Data.Product.Base using (_,_; _×_; ∃; ∃₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; LeftTrans; RightTrans)
open import Relation.Binary.Structures using (IsEquivalence)

open import Data.List.Relation.Binary.Permutation.Homogeneous public
  using (Permutation; refl; prep; swap; trans)

private
  variable
    xs ys zs : List A
    x y z v w : A

  _++[_]++_ = λ xs (z : A) ys → xs ++ [ z ] ++ ys

_≋_ _↭_ : Rel (List A) _
_≋_ = Pointwise R
_↭_ = Permutation R


------------------------------------------------------------------------
-- Properties of _↭_ depending on suitable assumptions on R

-- Constructor alias

↭-pointwise : _≋_ ⇒ _↭_
↭-pointwise = refl

------------------------------------------------------------------------
-- Reflexivity and its consequences

module Reflexivity (R-refl : Reflexive R) where

  ≋-refl : Reflexive _≋_
  ≋-refl = Pointwise.refl R-refl

  ↭-refl : Reflexive _↭_
  ↭-refl = ↭-pointwise ≋-refl

  ↭-prep : ∀ {x} {xs ys} → xs ↭ ys → (x ∷ xs) ↭ (x ∷ ys)
  ↭-prep xs↭ys = prep R-refl xs↭ys

  ↭-swap : ∀ x y {xs ys} → xs ↭ ys → (x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys)
  ↭-swap _ _ xs↭ys = swap R-refl R-refl xs↭ys

  ↭-shift : ∀ {v w} → R v w → ∀ xs {ys zs} → ys ↭ zs →
            (xs ++ v ∷ ys) ↭ (w ∷ xs ++ zs)
  ↭-shift {v} {w} v≈w []       rel = prep v≈w rel
  ↭-shift {v} {w} v≈w (x ∷ xs) rel
    = trans (↭-prep (↭-shift v≈w xs rel)) (↭-swap x w ↭-refl)

  shift : ∀ {v w} → R v w → ∀ xs {ys} → (xs ++[ v ]++ ys) ↭ (w ∷ xs ++ ys)
  shift v≈w xs = ↭-shift v≈w xs ↭-refl

  shift≈ : ∀ x xs {ys} → (xs ++[ x ]++ ys) ↭ (x ∷ xs ++ ys)
  shift≈ x xs = shift R-refl xs

------------------------------------------------------------------------
-- Symmetry and its consequences

module Symmetry (R-sym : Symmetric R) where

  ≋-sym : Symmetric _≋_
  ≋-sym = Pointwise.symmetric R-sym

  ↭-sym : Symmetric _↭_
  ↭-sym (refl xs∼ys)           = refl (≋-sym xs∼ys)
  ↭-sym (prep x∼x′ xs↭ys)      = prep (R-sym x∼x′) (↭-sym xs↭ys)
  ↭-sym (swap x∼x′ y∼y′ xs↭ys) = swap (R-sym y∼y′) (R-sym x∼x′) (↭-sym xs↭ys)
  ↭-sym (trans xs↭ys ys↭zs)    = trans (↭-sym ys↭zs) (↭-sym xs↭ys)

------------------------------------------------------------------------
-- Transitivity and its consequences

-- A smart version of trans that pushes `refl`s to the leaves (see #1113).

module LRTransitivity
       (↭-transˡ-≋ : LeftTrans _≋_ _↭_)
       (↭-transʳ-≋ : RightTrans _↭_ _≋_)

  where

  ↭-trans : Transitive _↭_
  ↭-trans (refl xs≋ys) ys↭zs = ↭-transˡ-≋ xs≋ys ys↭zs
  ↭-trans xs↭ys (refl ys≋zs) = ↭-transʳ-≋ xs↭ys ys≋zs
  ↭-trans xs↭ys ys↭zs        = trans xs↭ys ys↭zs

------------------------------------------------------------------------
-- Two important inversion properties of ↭, which *no longer*
-- require `steps` or  well-founded induction... but which
-- follow from ↭-transˡ-≋, ↭-transʳ-≋ and properties of R
------------------------------------------------------------------------

-- first inversion: split on a 'middle' element

  module Split (R-refl : Reflexive R) (R-trans : Transitive R) where

    private
      ≋-trans : Transitive (Pointwise R)
      ≋-trans = Pointwise.transitive R-trans

      open Reflexivity R-refl using (≋-refl; ↭-refl; ↭-prep; ↭-swap)

      helper : ∀ as bs {xs ys} (p : xs ↭ ys) →
               ys ≋ (as ++[ v ]++ bs) →
               ∃₂ λ ps qs → xs ≋ (ps ++[ v ]++ qs)
                          × (ps ++ qs) ↭ (as ++ bs)
      helper as           bs (trans xs↭ys ys↭zs) zs≋as++[v]++ys
        with ps , qs , eq , ↭ ← helper as bs ys↭zs zs≋as++[v]++ys
        with ps′ , qs′ , eq′ , ↭′ ← helper ps qs xs↭ys eq
        = ps′ , qs′ , eq′ , ↭-trans ↭′ ↭
      helper []           _  (refl (x≈v ∷ xs≋vs)) (v≈y ∷ vs≋ys)
        = [] , _ , R-trans x≈v v≈y ∷ ≋-refl , refl (≋-trans xs≋vs vs≋ys)
      helper (a ∷ as)     bs (refl (x≈v ∷ xs≋vs)) (v≈y ∷ vs≋ys)
        = _ ∷ as , bs , R-trans x≈v v≈y ∷ ≋-trans xs≋vs vs≋ys , ↭-refl
      helper []           bs (prep {xs = xs} x≈v xs↭vs) (v≈y ∷ vs≋ys)
        = [] , xs , R-trans x≈v v≈y ∷ ≋-refl , ↭-transʳ-≋ xs↭vs vs≋ys
      helper (a ∷ as)     bs (prep x≈v as↭vs) (v≈y ∷ vs≋ys)
        with ps , qs , eq , ↭ ← helper as bs as↭vs vs≋ys
        = a ∷ ps , qs , R-trans x≈v v≈y ∷ eq , prep R-refl ↭
      helper []           [] (swap _ _ _) (_ ∷ ())
      helper []      (b ∷ _) (swap x≈v y≈w xs↭vs) (w≈z ∷ v≈y ∷ vs≋ys)
        = b ∷ [] , _ , R-trans x≈v v≈y ∷ R-trans y≈w w≈z ∷ ≋-refl
                     , ↭-prep (↭-transʳ-≋ xs↭vs vs≋ys)
      helper (a ∷ [])     bs (swap x≈v y≈w xs↭vs)  (w≈z ∷ v≈y ∷ vs≋ys)
        = []     , a ∷ _ , R-trans x≈v v≈y ∷ R-trans y≈w w≈z ∷ ≋-refl
                         , ↭-prep (↭-transʳ-≋ xs↭vs vs≋ys)
      helper (a ∷ b ∷ as) bs (swap x≈v y≈w as↭vs) (w≈a ∷ v≈b ∷ vs≋ys)
        with ps , qs , eq , ↭ ← helper as bs as↭vs vs≋ys
        = b ∷ a ∷ ps , qs , R-trans x≈v v≈b ∷ R-trans y≈w w≈a ∷ eq
                          , ↭-swap _ _ ↭

    ↭-split : ∀ v as bs {xs} → xs ↭ (as ++[ v ]++ bs) →
              ∃₂ λ ps qs → xs ≋ (ps ++[ v ]++ qs)
                         × (ps ++ qs) ↭ (as ++ bs)
    ↭-split v as bs p = helper as bs p ≋-refl


-- second inversion: using ↭-split, drop the middle element

  module DropMiddle (R-≈ : IsEquivalence R) where

    private
      module ≈ = IsEquivalence R-≈
      open Reflexivity ≈.refl using (shift)
      open Symmetry ≈.sym using (↭-sym)
      open Split ≈.refl ≈.trans

    dropMiddleElement-≋ : ∀ {x} ws xs {ys} {zs} →
                          (ws ++[ x ]++ ys) ≋ (xs ++[ x ]++ zs) →
                          (ws ++ ys) ↭ (xs ++ zs)
    dropMiddleElement-≋ []       []       (_   ∷ eq)
      = ↭-pointwise eq
    dropMiddleElement-≋ []       (x ∷ xs) (w≈v ∷ eq)
      = ↭-transˡ-≋ eq (shift w≈v xs)
    dropMiddleElement-≋ (w ∷ ws) []       (w≈x ∷ eq)
      = ↭-transʳ-≋ (↭-sym (shift (≈.sym w≈x) ws)) eq
    dropMiddleElement-≋ (w ∷ ws) (x ∷ xs) (w≈x ∷ eq)
      = prep w≈x (dropMiddleElement-≋ ws xs eq)

    dropMiddleElement : ∀ {x} ws xs {ys zs} →
                        (ws ++[ x ]++ ys) ↭ (xs ++[ x ]++ zs) →
                        (ws ++ ys) ↭ (xs ++ zs)
    dropMiddleElement {x} ws xs {ys} {zs} p
      with ps , qs , eq , ↭ ← ↭-split x xs zs p
      = ↭-trans (dropMiddleElement-≋ ws ps eq) ↭

    syntax dropMiddleElement-≋ ws xs ws++x∷ys≋xs++x∷zs
      = ws ++≋[ ws++x∷ys≋xs++x∷zs ]++ xs

    syntax dropMiddleElement ws xs ws++x∷ys↭xs++x∷zs
      = ws ++↭[ ws++x∷ys↭xs++x∷zs ]++ xs


------------------------------------------------------------------------
-- Now: Left and Right Transitivity hold outright!

module Transitivity (R-trans : Transitive R) where

  private
    ≋-trans : Transitive _≋_
    ≋-trans = Pointwise.transitive R-trans

  ↭-transˡ-≋ : LeftTrans _≋_ _↭_
  ↭-transˡ-≋ xs≋ys               (refl ys≋zs)
    = refl (≋-trans xs≋ys ys≋zs)
  ↭-transˡ-≋ (x≈y ∷ xs≋ys)       (prep y≈z ys↭zs)
    = prep (R-trans x≈y y≈z) (↭-transˡ-≋ xs≋ys ys↭zs)
  ↭-transˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ ys↭zs)
    = swap (R-trans x≈y eq₁) (R-trans w≈z eq₂) (↭-transˡ-≋ xs≋ys ys↭zs)
  ↭-transˡ-≋ xs≋ys               (trans ys↭ws ws↭zs)
    = trans (↭-transˡ-≋ xs≋ys ys↭ws) ws↭zs

  ↭-transʳ-≋ : RightTrans _↭_ _≋_
  ↭-transʳ-≋ (refl xs≋ys)         ys≋zs
    = refl (≋-trans xs≋ys ys≋zs)
  ↭-transʳ-≋ (prep x≈y xs↭ys)     (y≈z ∷ ys≋zs)
    = prep (R-trans x≈y y≈z) (↭-transʳ-≋ xs↭ys ys≋zs)
  ↭-transʳ-≋ (swap eq₁ eq₂ xs↭ys) (x≈w ∷ y≈z ∷ ys≋zs)
    = swap (R-trans eq₁ y≈z) (R-trans eq₂ x≈w) (↭-transʳ-≋ xs↭ys ys≋zs)
  ↭-transʳ-≋ (trans xs↭ws ws↭ys)  ys≋zs
    = trans xs↭ws (↭-transʳ-≋ ws↭ys ys≋zs)

-- Transitivity proper

  ↭-trans : Transitive _↭_
  ↭-trans = LRTransitivity.↭-trans ↭-transˡ-≋ ↭-transʳ-≋


------------------------------------------------------------------------
-- Permutation is an equivalence (Setoid version)

module _ (R-equiv : IsEquivalence R) where

  private module ≈ = IsEquivalence R-equiv

  isEquivalence : IsEquivalence _↭_
  isEquivalence = record
    { refl  = Reflexivity.↭-refl ≈.refl
    ; sym   = Symmetry.↭-sym ≈.sym
    ; trans = Transitivity.↭-trans ≈.trans
    }

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }
