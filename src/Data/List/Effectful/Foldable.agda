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
open import Data.List.Properties using (map-id; foldMap≗foldr∘map)
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise) hiding (module Pointwise)
open import Effect.Foldable using (RawFoldableWithDefaults; RawFoldable)
open import Function.Base using (_∘_; id; _$_)
open import Function.Bundles using (Func)
import Function.Construct.Identity as Identity using (function)
open import Function.Definitions using (Congruent)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
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
-- for Commutative Monoids, foldMap and foldr respect Permutation

module _ (commutativeMonoid : CommutativeMonoid c ℓ) where

  private
    open module CM = CommutativeMonoid commutativeMonoid
      using (_∙_; ε; setoid; ∙-cong; ∙-congˡ; ∙-congʳ; assoc; comm)
    k = foldr _∙_ ε
    _≋_ = Pointwise CM._≈_
    k-cong-≋ : ∀ {ws zs} → ws ≋ zs → k ws CM.≈ k zs
    k-cong-≋ = Pointwise.foldr⁺ ∙-cong CM.refl
  open ≈-Reasoning setoid

-- foldMap

  module _ {S : Setoid c r} (F : Func S setoid) where

    open Permutation S renaming (_↭_ to _↭ₛ_)
    open Pointwise using (map⁺; map)
    private
      open module S = Setoid S
      open module F = Func F
      f = F.to
      h = foldMap CM.rawMonoid f

    foldMap-congruent : Congruent _↭ₛ_ CM._≈_ h

    foldMap-congruent (refl {xs} {ys} xs≋ys) = begin
      h xs              ≡⟨ foldMap≗foldr∘map _∙_ ε f xs ⟩
      k (List.map f xs) ≈⟨ k-cong-≋ (map⁺ f f (map F.cong xs≋ys))  ⟩
      k (List.map f ys) ≡⟨ foldMap≗foldr∘map _∙_ ε f ys ⟨
      h ys              ∎

    foldMap-congruent (prep x≈y xs↭ys)    = ∙-cong (F.cong x≈y) (foldMap-congruent xs↭ys)

    foldMap-congruent (swap {xs} {ys} {x} {y} {x′} {y′} x≈x′ y≈y′ xs↭ys) = begin
      f x ∙ (f y ∙ h xs)    ≈⟨ ∙-congˡ (∙-congˡ (foldMap-congruent xs↭ys)) ⟩
      f x ∙ (f y ∙ h ys)    ≈⟨ assoc (f x) (f y) (h ys) ⟨
      (f x ∙ f y) ∙ h ys    ≈⟨ ∙-congʳ (comm (f x) (f y)) ⟩
      (f y ∙ f x) ∙ h ys    ≈⟨ ∙-congʳ (∙-cong (F.cong y≈y′) (F.cong x≈x′)) ⟩
      (f y′ ∙ f x′) ∙ h ys  ≈⟨ assoc (f y′) (f x′) (h ys)  ⟩
      f y′ ∙ (f x′ ∙ h ys)  ∎

    foldMap-congruent (trans xs↭ys ys↭zs) =
      CM.trans (foldMap-congruent xs↭ys) (foldMap-congruent ys↭zs)

-- foldr

  open Permutation CM.setoid renaming (_↭_ to _↭ₘ_)

  foldr-congruent : Congruent _↭ₘ_ CM._≈_ (foldr _∙_ ε)
  foldr-congruent {x = xs} {y = ys}
    rewrite ≡.sym (map-id xs) | ≡.sym (map-id ys)
    rewrite ≡.sym (foldMap≗foldr∘map _∙_ ε id xs) | ≡.sym (foldMap≗foldr∘map _∙_ ε id ys)
    rewrite map-id xs | map-id ys
    = foldMap-congruent $ Identity.function CM.setoid
