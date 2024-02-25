------------------------------------------------------------------------
-- The Agda standard library
--
-- Well-founded induction
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Induction.WellFounded where

open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Function.Base using (_∘_; flip; _on_)
open import Induction
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Symmetric; Asymmetric; Irreflexive; _Respects₂_;
    _Respectsʳ_; _Respects_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Binary.Consequences using (asym⇒irr)
open import Relation.Unary
open import Relation.Nullary.Negation.Core using (¬_)

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
WfRec _<_ P x = ∀ {y} → y < x → P y

-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).

data Acc {A : Set a} (_<_ : Rel A ℓ) (x : A) : Set (a ⊔ ℓ) where
  acc : (rs : WfRec _<_ (Acc _<_) x) → Acc _<_ x

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.

WellFounded : Rel A ℓ → Set _
WellFounded _<_ = ∀ x → Acc _<_ x

------------------------------------------------------------------------
-- Basic properties

acc-inverse : ∀ {_<_ : Rel A ℓ} {x : A} (q : Acc _<_ x) →
              WfRec _<_ (Acc _<_) x
acc-inverse (acc rs) y<x = rs y<x

module _ {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} where

  Acc-resp-flip-≈ : _<_ Respectsʳ (flip _≈_) → (Acc _<_) Respects _≈_
  Acc-resp-flip-≈ respʳ x≈y (acc rec) = acc λ z<y → rec (respʳ x≈y z<y)

  Acc-resp-≈ : Symmetric _≈_ → _<_ Respectsʳ _≈_ → (Acc _<_) Respects _≈_
  Acc-resp-≈ sym respʳ x≈y wf = Acc-resp-flip-≈ (respʳ ∘ sym) x≈y wf

------------------------------------------------------------------------
-- Well-founded induction for the subset of accessible elements:

module Some {_<_ : Rel A r} {ℓ} where

  wfRecBuilder : SubsetRecursorBuilder (Acc _<_) (WfRec _<_ {ℓ = ℓ})
  wfRecBuilder P f x (acc rs) = λ y<x → f _ (wfRecBuilder P f _ (rs y<x))

  wfRec : SubsetRecursor (Acc _<_) (WfRec _<_)
  wfRec = subsetBuild wfRecBuilder

  unfold-wfRec : (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P) {x : A} (q : Acc _<_ x) →
                 wfRec P f x q ≡ f x λ y<x → wfRec P f _ (acc-inverse q y<x)
  unfold-wfRec P f (acc rs) = refl


------------------------------------------------------------------------
-- Well-founded induction for all elements, assuming they are all
-- accessible:

module All {_<_ : Rel A r} (wf : WellFounded _<_) ℓ where

  wfRecBuilder : RecursorBuilder (WfRec _<_ {ℓ = ℓ})
  wfRecBuilder P f x = Some.wfRecBuilder P f x (wf x)

  wfRec : Recursor (WfRec _<_)
  wfRec = build wfRecBuilder

  wfRec-builder = wfRecBuilder

module FixPoint
  {_<_ : Rel A r} (wf : WellFounded _<_)
  (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P)
  (f-ext : (x : A) {IH IH′ : WfRec _<_ P x} →
           (∀ {y} y<x → IH {y} y<x ≡ IH′ y<x) →
           f x IH ≡ f x IH′)
  where

  some-wfrec-Irrelevant : Pred A _
  some-wfrec-Irrelevant x = ∀ q q′ → Some.wfRec P f x q ≡ Some.wfRec P f x q′

  some-wfRec-irrelevant : ∀ x → some-wfrec-Irrelevant x
  some-wfRec-irrelevant = All.wfRec wf _ some-wfrec-Irrelevant
    λ { x IH (acc rs) (acc rs′) → f-ext x λ y<x → IH y<x (rs y<x) (rs′ y<x) }

  open All wf ℓ

  wfRecBuilder-wfRec : ∀ {x y} y<x → wfRecBuilder P f x y<x ≡ wfRec P f y
  wfRecBuilder-wfRec {x} {y} y<x with acc rs ← wf x
   = some-wfRec-irrelevant y (rs y<x) (wf y)

  unfold-wfRec : ∀ {x} → wfRec P f x ≡ f x λ _ → wfRec P f _
  unfold-wfRec {x} = f-ext x wfRecBuilder-wfRec

------------------------------------------------------------------------
-- Well-founded relations are asymmetric and irreflexive.

module _ {_<_ : Rel A r} where
  acc⇒asym : ∀ {x y} → Acc _<_ x → x < y → ¬ (y < x)
  acc⇒asym {x} hx =
    Some.wfRec (λ x → ∀ {y} → x < y → ¬ (y < x)) (λ _ hx x<y y<x → hx y<x y<x x<y) _ hx

  wf⇒asym : WellFounded _<_ → Asymmetric _<_
  wf⇒asym wf = acc⇒asym (wf _)

  wf⇒irrefl : {_≈_ : Rel A ℓ} → _<_ Respects₂ _≈_ →
              Symmetric _≈_ → WellFounded _<_ → Irreflexive _≈_ _<_
  wf⇒irrefl r s wf = asym⇒irr r s (wf⇒asym wf)

------------------------------------------------------------------------
-- It might be useful to establish proofs of Acc or Well-founded using
-- combinators such as the ones below (see, for instance,
-- "Constructing Recursion Operators in Intuitionistic Type Theory" by
-- Lawrence C Paulson).

module Subrelation {_<₁_ : Rel A ℓ₁} {_<₂_ : Rel A ℓ₂}
                   (<₁⇒<₂ : ∀ {x y} → x <₁ y → x <₂ y) where

  accessible : Acc _<₂_ ⊆ Acc _<₁_
  accessible (acc rs) = acc λ y<x → accessible (rs (<₁⇒<₂ y<x))

  wellFounded : WellFounded _<₂_ → WellFounded _<₁_
  wellFounded wf = λ x → accessible (wf x)


-- DEPRECATED in v1.4.
-- Please use proofs in `Relation.Binary.Construct.On` instead.
module InverseImage {_<_ : Rel B ℓ} (f : A → B) where

  accessible : ∀ {x} → Acc _<_ (f x) → Acc (_<_ on f) x
  accessible (acc rs) = acc λ fy<fx → accessible (rs fy<fx)

  wellFounded : WellFounded _<_ → WellFounded (_<_ on f)
  wellFounded wf = λ x → accessible (wf (f x))

  well-founded = wellFounded
  {-# WARNING_ON_USAGE accessible
  "Warning: accessible was deprecated in v1.4.
\ \Please use accessible from `Relation.Binary.Construct.On` instead."
  #-}
  {-# WARNING_ON_USAGE wellFounded
  "Warning: wellFounded was deprecated in v1.4.
\ \Please use wellFounded from `Relation.Binary.Construct.On` instead."
  #-}


-- DEPRECATED in v1.5.
-- Please use `TransClosure` from `Relation.Binary.Construct.Closure.Transitive` instead.
module TransitiveClosure {A : Set a} (_<_ : Rel A ℓ) where

  infix 4 _<⁺_

  data _<⁺_ : Rel A (a ⊔ ℓ) where
    [_]   : ∀ {x y} (x<y : x < y) → x <⁺ y
    trans : ∀ {x y z} (x<y : x <⁺ y) (y<z : y <⁺ z) → x <⁺ z

  downwardsClosed : ∀ {x y} → Acc _<⁺_ y → x <⁺ y → Acc _<⁺_ x
  downwardsClosed (acc rs) x<y = acc λ z<x → rs (trans z<x x<y)

  mutual

    accessible : ∀ {x} → Acc _<_ x → Acc _<⁺_ x
    accessible acc-x = acc (accessible′ acc-x)

    accessible′ : ∀ {x} → Acc _<_ x → WfRec _<⁺_ (Acc _<⁺_) x
    accessible′ (acc rs) [ y<x ]         = accessible (rs y<x)
    accessible′ acc-x    (trans y<z z<x) =
      downwardsClosed (accessible′ acc-x z<x) y<z

  wellFounded : WellFounded _<_ → WellFounded _<⁺_
  wellFounded wf = λ x → accessible (wf x)

  {-# WARNING_ON_USAGE _<⁺_
  "Warning: _<⁺_ was deprecated in v1.5.
\ \Please use TransClosure from Relation.Binary.Construct.Closure.Transitive instead."
  #-}


-- DEPRECATED in v1.3.
-- Please use `×-Lex` from `Data.Product.Relation.Binary.Lex.Strict` instead.
module Lexicographic {A : Set a} {B : A → Set b}
                     (RelA : Rel A ℓ₁)
                     (RelB : ∀ x → Rel (B x) ℓ₂) where

  infix 4 _<_
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
    accessible′ (acc rsA) _    wfB (left  x′<x) = accessible (rsA x′<x) wfB
    accessible′ accA (acc rsB) wfB (right y′<y) =
      acc (accessible′ accA (rsB y′<y) wfB)

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



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

module Inverse-image = InverseImage
module Transitive-closure = TransitiveClosure
