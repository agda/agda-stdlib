------------------------------------------------------------------------
-- The Agda standard library
--
-- Well-founded induction
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Induction.WellFounded where

open import Data.Product
open import Function
open import Induction
open import Level
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Relation.Unary

private
  variable
    a b ℓ ℓ₁ ℓ₂ r : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definitions

-- When using well-founded recursion you can recurse arbitrarily, as
-- long as the arguments become smaller, and "smaller" is
-- well-founded.

WfRec : Rel A r → ∀ {ℓ} → RecStruct A ℓ _
WfRec _<_ P x = ∀ y → y < x → P y

-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).

data Acc {A : Set a} (_<_ : Rel A ℓ) (x : A) : Set (a ⊔ ℓ) where
  acc : (rs : WfRec _<_ (Acc _<_) x) → Acc _<_ x

acc-inverse : ∀ {_<_ : Rel A ℓ} {x : A} (q : Acc _<_ x) →
              (y : A) → y < x → Acc _<_ y
acc-inverse (acc rs) y y<x = rs y y<x

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.

WellFounded : Rel A ℓ → Set _
WellFounded _<_ = ∀ x → Acc _<_ x

Well-founded = WellFounded
{-# WARNING_ON_USAGE Well-founded
"Warning: Well-founded was deprecated in v0.15.
Please use WellFounded instead."
#-}

------------------------------------------------------------------------
-- Basic properties

Acc-resp-≈ : {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} → Symmetric _≈_ →
             _<_ Respectsʳ _≈_ → (Acc _<_) Respects _≈_
Acc-resp-≈ sym respʳ x≈y (acc rec) =
  acc (λ z z<y → rec z (respʳ (sym x≈y) z<y))

------------------------------------------------------------------------
-- Well-founded induction for the subset of accessible elements:

module Some {_<_ : Rel A r} {ℓ} where

  wfRecBuilder : SubsetRecursorBuilder (Acc _<_) (WfRec _<_ {ℓ = ℓ})
  wfRecBuilder P f x (acc rs) = λ y y<x →
    f y (wfRecBuilder P f y (rs y y<x))

  wfRec : SubsetRecursor (Acc _<_) (WfRec _<_)
  wfRec = subsetBuild wfRecBuilder

  unfold-wfRec : (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P) {x : A} (q : Acc _<_ x) →
                 wfRec P f x q ≡ f x (λ y y<x → wfRec P f y (acc-inverse q y y<x))
  unfold-wfRec P f (acc rs) = refl

  wfRec-builder = wfRecBuilder
  {-# WARNING_ON_USAGE wfRec-builder
  "Warning: wfRec-builder was deprecated in v0.15.
\ \Please use wfRecBuilder instead."
  #-}


------------------------------------------------------------------------
-- Well-founded induction for all elements, assuming they are all
-- accessible:

module All {_<_ : Rel A r} (wf : WellFounded _<_) ℓ where

  wfRecBuilder : RecursorBuilder (WfRec _<_ {ℓ = ℓ})
  wfRecBuilder P f x = Some.wfRecBuilder P f x (wf x)

  wfRec : Recursor (WfRec _<_)
  wfRec = build wfRecBuilder

  wfRec-builder = wfRecBuilder
  {-# WARNING_ON_USAGE wfRec-builder
  "Warning: wfRec-builder was deprecated in v0.15.
\ \Please use wfRecBuilder instead."
  #-}

module FixPoint
  {_<_ : Rel A ℓ} (wf : WellFounded _<_)
  (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P)
  (f-ext : (x : A) {IH IH' : WfRec _<_ P x} → (∀ {y} y<x → IH y y<x ≡ IH' y y<x) → f x IH ≡ f x IH')
  where

  some-wfRec-irrelevant : ∀ x → (q q' : Acc _<_ x) → Some.wfRec P f x q ≡ Some.wfRec P f x q'
  some-wfRec-irrelevant = All.wfRec wf _
                                   (λ x → (q q' : Acc _<_ x) → Some.wfRec P f x q ≡ Some.wfRec P f x q')
                                   (λ { x IH (acc rs) (acc rs') → f-ext x (λ y<x → IH _ y<x (rs _ y<x) (rs' _ y<x)) })

  open All wf ℓ
  wfRecBuilder-wfRec : ∀ {x y} y<x → wfRecBuilder P f x y y<x ≡ wfRec P f y
  wfRecBuilder-wfRec {x} {y} y<x with wf x
  ... | acc rs = some-wfRec-irrelevant y (rs y y<x) (wf y)

  unfold-wfRec : ∀ {x} → wfRec P f x ≡ f x (λ y _ → wfRec P f y)
  unfold-wfRec {x} = f-ext x wfRecBuilder-wfRec


------------------------------------------------------------------------
-- It might be useful to establish proofs of Acc or Well-founded using
-- combinators such as the ones below (see, for instance,
-- "Constructing Recursion Operators in Intuitionistic Type Theory" by
-- Lawrence C Paulson).

module Subrelation {_<₁_ : Rel A ℓ₁} {_<₂_ : Rel A ℓ₂}
                   (<₁⇒<₂ : ∀ {x y} → x <₁ y → x <₂ y) where

  accessible : Acc _<₂_ ⊆ Acc _<₁_
  accessible (acc rs) = acc (λ y y<x → accessible (rs y (<₁⇒<₂ y<x)))

  wellFounded : WellFounded _<₂_ → WellFounded _<₁_
  wellFounded wf = λ x → accessible (wf x)

  well-founded = wellFounded
  {-# WARNING_ON_USAGE well-founded
  "Warning: well-founded was deprecated in v0.15.
\ \Please use wellFounded instead."
  #-}

module InverseImage {_<_ : Rel B ℓ} (f : A → B) where

  accessible : ∀ {x} → Acc _<_ (f x) → Acc (_<_ on f) x
  accessible (acc rs) = acc (λ y fy<fx → accessible (rs (f y) fy<fx))

  wellFounded : WellFounded _<_ → WellFounded (_<_ on f)
  wellFounded wf = λ x → accessible (wf (f x))

  well-founded = wellFounded
  {-# WARNING_ON_USAGE well-founded
  "Warning: well-founded was deprecated in v0.15.
\ \Please use wellFounded instead."
  #-}

module TransitiveClosure {A : Set a} (_<_ : Rel A ℓ) where

  infix 4 _<⁺_

  data _<⁺_ : Rel A (a ⊔ ℓ) where
    [_]   : ∀ {x y} (x<y : x < y) → x <⁺ y
    trans : ∀ {x y z} (x<y : x <⁺ y) (y<z : y <⁺ z) → x <⁺ z

  downwardsClosed : ∀ {x y} → Acc _<⁺_ y → x <⁺ y → Acc _<⁺_ x
  downwardsClosed (acc rs) x<y = acc (λ z z<x → rs z (trans z<x x<y))

  mutual

    accessible : ∀ {x} → Acc _<_ x → Acc _<⁺_ x
    accessible acc-x = acc (accessible′ acc-x)

    accessible′ : ∀ {x} → Acc _<_ x → WfRec _<⁺_ (Acc _<⁺_) x
    accessible′ (acc rs) y [ y<x ]         = accessible (rs y y<x)
    accessible′ acc-x    y (trans y<z z<x) =
      downwardsClosed (accessible′ acc-x _ z<x) y<z

  wellFounded : WellFounded _<_ → WellFounded _<⁺_
  wellFounded wf = λ x → accessible (wf x)

  downwards-closed = downwardsClosed
  {-# WARNING_ON_USAGE downwards-closed
  "Warning: downwards-closed was deprecated in v0.15.
\ \Please use downwardsClosed instead."
  #-}
  well-founded     = wellFounded
  {-# WARNING_ON_USAGE well-founded
  "Warning: well-founded was deprecated in v0.15.
\ \Please use wellFounded instead."
  #-}


-- DEPRECATED in v1.3.
-- Please use `×-Lex` from `Data.Product.Relation.Binary.Lex.Strict` instead.
module Lexicographic {A : Set a} {B : A → Set b}
                     (RelA : Rel A ℓ₁)
                     (RelB : ∀ x → Rel (B x) ℓ₂) where

  data _<_ : Rel (Σ A B) (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : RelA   x₁ x₂) → (x₁ , y₁) < (x₂ , y₂)
    right : ∀ {x y₁ y₂}     (y₁<y₂ : RelB x y₁ y₂) → (x  , y₁) < (x  , y₂)

  mutual

    accessible : ∀ {x y} →
                 Acc RelA x → (∀ {x} → WellFounded (RelB x)) →
                 Acc _<_ (x , y)
    accessible accA wfB = acc (accessible′ accA (wfB _) wfB)


    accessible′ :
      ∀ {x y} →
      Acc RelA x → Acc (RelB x) y → (∀ {x} → WellFounded (RelB x)) →
      WfRec _<_ (Acc _<_) (x , y)
    accessible′ (acc rsA) _    wfB ._ (left  x′<x) = accessible (rsA _ x′<x) wfB
    accessible′ accA (acc rsB) wfB ._ (right y′<y) =
      acc (accessible′ accA (rsB _ y′<y) wfB)

  wellFounded : WellFounded RelA → (∀ {x} → WellFounded (RelB x)) →
                WellFounded _<_
  wellFounded wfA wfB p = accessible (wfA (proj₁ p)) wfB

  well-founded = wellFounded

  {-# WARNING_ON_USAGE _<_
  "Warning: _<_ was deprecated in v1.3.
\ \Please use `×-Lex` from `Data.Product.Relation.Binary.Lex.Strict` instead."
  #-}
  {-# WARNING_ON_USAGE accessible
  "Warning: accessible was deprecated in v1.3."
  #-}
  {-# WARNING_ON_USAGE accessible′
  "Warning: accessible′ was deprecated in v1.3."
  #-}
  {-# WARNING_ON_USAGE wellFounded
  "Warning: wellFounded was deprecated in v1.3.
\ \Please use `×-wellFounded` from `Data.Product.Relation.Binary.Lex.Strict` instead."
  #-}
  {-# WARNING_ON_USAGE well-founded
  "Warning: well-founded was deprecated in v0.15.
\ \Please use wellFounded instead."
  #-}



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

module Inverse-image = InverseImage
module Transitive-closure = TransitiveClosure
