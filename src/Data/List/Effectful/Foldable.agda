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
open import Data.List.Properties using (foldMap≗foldr∘map)
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
-- for Commutative Monoids, foldMap and foldr respect Permutation

module _ (commutativeMonoid : CommutativeMonoid c ℓ) where

  private
    open module CM = CommutativeMonoid commutativeMonoid
      using (_∙_; ε; setoid; ∙-cong; ∙-congˡ; ∙-congʳ; assoc; comm)
  open ≈-Reasoning setoid

  module _ {S : Setoid a r} (F : Func S setoid) where
    
    open Permutation S renaming (_↭_ to _↭ₛ_)
    private
      open module F = Func F
      f = F.to
      h = foldMap CM.rawMonoid f
      

    foldMap-commMonoid : Congruent _↭ₛ_ CM._≈_ h
    foldMap-commMonoid (refl {xs} {ys} xs≋ys)
      rewrite foldMap≗foldr∘map _∙_ ε f xs | foldMap≗foldr∘map _∙_ ε f ys
      = Pointwise.foldr⁺ ∙-cong (CM.refl {x = ε})(Pointwise.map⁺ f f (Pointwise.map F.cong xs≋ys))
    foldMap-commMonoid (prep x≈y xs↭ys)    = ∙-cong (F.cong x≈y) (foldMap-commMonoid xs↭ys)
    foldMap-commMonoid (swap {xs} {ys} {x} {y} {x′} {y′} x≈x′ y≈y′ xs↭ys) = begin
      f x ∙ (f y ∙ h xs)    ≈⟨ ∙-congˡ (∙-congˡ (foldMap-commMonoid xs↭ys)) ⟩
      f x ∙ (f y ∙ h ys)    ≈⟨ assoc (f x) (f y) (h ys) ⟨
      (f x ∙ f y) ∙ h ys    ≈⟨ ∙-congʳ (comm (f x) (f y)) ⟩
      (f y ∙ f x) ∙ h ys    ≈⟨ ∙-congʳ (∙-cong (F.cong y≈y′) (F.cong x≈x′)) ⟩
      (f y′ ∙ f x′) ∙ h ys  ≈⟨ assoc (f y′) (f x′) (h ys)  ⟩
      f y′ ∙ (f x′ ∙ h ys)  ∎
    foldMap-commMonoid (trans xs↭ys ys↭zs) =
      CM.trans (foldMap-commMonoid xs↭ys) (foldMap-commMonoid ys↭zs)

  module _ where

    open Permutation CM.setoid renaming (_↭_ to _↭ₘ_)

    private g = foldr _∙_ ε

    foldr-commMonoid : Congruent _↭ₘ_ CM._≈_ g
{-
    foldr-commMonoid = {!foldMap-commMonoid (function CM.setoid)!}
-}
    foldr-commMonoid (refl xs≋ys)        = Pointwise.foldr⁺ ∙-cong CM.refl xs≋ys
    foldr-commMonoid (prep x≈y xs↭ys)    = ∙-cong x≈y (foldr-commMonoid xs↭ys)
    foldr-commMonoid (swap {xs} {ys} {x} {y} {x′} {y′} x≈x′ y≈y′ xs↭ys) = begin
      x ∙ (y ∙ g xs)    ≈⟨ ∙-congˡ (∙-congˡ (foldr-commMonoid xs↭ys)) ⟩
      x ∙ (y ∙ g ys)    ≈⟨ assoc x y (g ys) ⟨
      (x ∙ y) ∙ g ys    ≈⟨ ∙-congʳ (comm x y) ⟩
      (y ∙ x) ∙ g ys    ≈⟨ ∙-congʳ (∙-cong y≈y′ x≈x′) ⟩
      (y′ ∙ x′) ∙ g ys  ≈⟨ assoc y′ x′ (g ys) ⟩
      y′ ∙ (x′ ∙ g ys)  ∎
    foldr-commMonoid (trans xs↭ys ys↭zs) =
      CM.trans (foldr-commMonoid xs↭ys) (foldr-commMonoid ys↭zs)
