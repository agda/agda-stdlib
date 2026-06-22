------------------------------------------------------------------------
-- The Agda standard library
--
-- List is Foldable
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Effectful.Foldable where

open import Algebra.Bundles using (Monoid; CommutativeMonoid)
open import Algebra.Bundles.Raw using (RawMonoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism)
open import Data.List.Base as List using (List; []; _∷_; _++_; foldr)
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise)
open import Effect.Foldable using (RawFoldableWithDefaults; RawFoldable)
open import Function.Base using (_∘_; id)
open import Function.Bundles using (Func)
open import Function.Construct.Identity using (function)
open import Function.Definitions using (Congruent)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; cong)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    a c r ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Root implementation

module _ (M : RawMonoid c ℓ) where

  open RawMonoid M

  foldMap : (A → Carrier) → List A → Carrier
  foldMap = List.foldMap _∙_ ε

------------------------------------------------------------------------
-- Basic implementation using supplied defaults

foldableWithDefaults : RawFoldableWithDefaults (List {a})
foldableWithDefaults = record { foldMap = λ M → foldMap M }

------------------------------------------------------------------------
-- Specialised version using optimised implementations

foldable : RawFoldable (List {a})
foldable = record
  { foldMap = λ M → foldMap M
  ; foldr = List.foldr
  ; foldl = List.foldl
  ; toList = id
  }

------------------------------------------------------------------------
-- foldMap gives rise to a Monoid homomorphism

module _ (M : Monoid c ℓ) (f : A → Monoid.Carrier M) where

  open Monoid M

  private
    h = foldMap rawMonoid f

  []-homo : h [] ≈ ε
  []-homo = refl

  ++-homo : ∀ xs {ys} → h (xs ++ ys) ≈ h xs ∙ h ys
  ++-homo []       = sym (identityˡ _)
  ++-homo (x ∷ xs) = trans (∙-congˡ (++-homo xs)) (sym (assoc _ _ _))

  foldMap-morphism : IsMonoidHomomorphism (List.++-[]-rawMonoid A) rawMonoid h
  foldMap-morphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = reflexive ∘ ≡.cong h }
      ; ∙-homo = λ xs _ → ++-homo xs
      }
    ; ε-homo = []-homo
    }

------------------------------------------------------------------------
-- for Commutative Monoids, foldr respects Permutation

module _ (commutativeMonoid : CommutativeMonoid c ℓ) where

  private
    open module CM = CommutativeMonoid commutativeMonoid
      using (_∙_; ε; ∙-cong; ∙-congˡ; ∙-congʳ; assoc; comm)
    open Permutation CM.setoid

    h = foldr _∙_ ε

  foldr-commMonoid : Congruent _↭_ CM._≈_ h
  foldr-commMonoid (refl xs≋ys)        = Pointwise.foldr⁺ ∙-cong CM.refl xs≋ys
  foldr-commMonoid (prep x≈y xs↭ys)    = ∙-cong x≈y (foldr-commMonoid xs↭ys)
  foldr-commMonoid (swap {xs} {ys} {x} {y} {x′} {y′} x≈x′ y≈y′ xs↭ys) = begin
    x ∙ (y ∙ h xs)    ≈⟨ ∙-congˡ (∙-congˡ (foldr-commMonoid xs↭ys)) ⟩
    x ∙ (y ∙ h ys)    ≈⟨ assoc x y (h ys) ⟨
    (x ∙ y) ∙ h ys    ≈⟨ ∙-congʳ (comm x y) ⟩
    (y ∙ x) ∙ h ys    ≈⟨ ∙-congʳ (∙-cong y≈y′ x≈x′) ⟩
    (y′ ∙ x′) ∙ h ys  ≈⟨ assoc y′ x′ (h ys) ⟩
    y′ ∙ (x′ ∙ h ys)  ∎
    where open ≈-Reasoning CM.setoid
  foldr-commMonoid (trans xs↭ys ys↭zs) =
    CM.trans (foldr-commMonoid xs↭ys) (foldr-commMonoid ys↭zs)
