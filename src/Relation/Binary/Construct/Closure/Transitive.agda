------------------------------------------------------------------------
-- The Agda standard library
--
-- Transitive closures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Closure.Transitive where

open import Function.Base
open import Function.Bundles using (_⇔_; mk⇔)
open import Induction.WellFounded
open import Level
open import Relation.Binary.Core using (Rel; _=[_]⇒_; _⇒_)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

private
  variable
    a ℓ ℓ₁ ℓ₂ : Level
    A B : Set a

------------------------------------------------------------------------
-- Definition

infixr 5 _∷_
infix  4 TransClosure

data TransClosure {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  [_] : ∀ {x y} (x∼y : x ∼ y) → TransClosure _∼_ x y
  _∷_ : ∀ {x y z} (x∼y : x ∼ y) (y∼⁺z : TransClosure _∼_ y z) → TransClosure _∼_ x z

syntax TransClosure R x y = x ⟨ R ⟩⁺ y

------------------------------------------------------------------------
-- Operations

module _ {_∼_ : Rel A ℓ} where
  private
    _∼⁺_ = TransClosure _∼_

  infixr 5 _∷ʳ_

  _∷ʳ_ : ∀ {x y z} → (x∼⁺y : x ∼⁺ y) (y∼z : y ∼ z) → x ∼⁺ z
  [ x∼y ]      ∷ʳ y∼z = x∼y ∷ [ y∼z ]
  (x∼y ∷ x∼⁺y) ∷ʳ y∼z = x∼y ∷ (x∼⁺y ∷ʳ y∼z)

  infixr 5 _++_
  _++_ : ∀ {x y z} → x ∼⁺ y → y ∼⁺ z → x ∼⁺ z
  [ x∼y ]      ++ y∼⁺z = x∼y ∷ y∼⁺z
  (x∼y ∷ y∼⁺z) ++ z∼⁺u = x∼y ∷ (y∼⁺z ++ z∼⁺u)

------------------------------------------------------------------------
-- Properties

module _ (_∼_ : Rel A ℓ) where
  private
    _∼⁺_ = TransClosure _∼_
    module ∼⊆∼⁺ = Subrelation {_<₂_ = _∼⁺_} [_]

  reflexive : Reflexive _∼_ → Reflexive _∼⁺_
  reflexive refl = [ refl ]

  symmetric : Symmetric _∼_ → Symmetric _∼⁺_
  symmetric sym [ x∼y ]      = [ sym x∼y ]
  symmetric sym (x∼y ∷ y∼⁺z) = symmetric sym y∼⁺z ∷ʳ sym x∼y

  transitive : Transitive _∼⁺_
  transitive = _++_

  transitive⁻ : Transitive _∼_ → _∼⁺_ ⇒ _∼_
  transitive⁻ trans [ x∼y ]      = x∼y
  transitive⁻ trans (x∼y ∷ x∼⁺y) = trans x∼y (transitive⁻ trans x∼⁺y)

  accessible⁻ : ∀ {x} → Acc _∼⁺_ x → Acc _∼_ x
  accessible⁻ = ∼⊆∼⁺.accessible

  wellFounded⁻ : WellFounded _∼⁺_ → WellFounded _∼_
  wellFounded⁻ = ∼⊆∼⁺.wellFounded

  accessible : ∀ {x} → Acc _∼_ x → Acc _∼⁺_ x
  accessible acc[x] = acc (wf-acc acc[x])
    where
    wf-acc : ∀ {x} → Acc _∼_ x → WfRec _∼⁺_ (Acc _∼⁺_) x
    wf-acc (acc rec) [ y∼x ]   = acc (wf-acc (rec y∼x))
    wf-acc acc[x] (y∼z ∷ z∼⁺x) = acc-inverse (wf-acc acc[x] z∼⁺x) [ y∼z ]

  wellFounded : WellFounded _∼_ → WellFounded _∼⁺_
  wellFounded wf x = accessible (wf x)


------------------------------------------------------------------------
-- Alternative definition of transitive closure

infix 4 Plus

syntax Plus R x y = x [ R ]⁺ y

data Plus {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  [_]     : ∀ {x y} (x∼y : x ∼ y) → x [ _∼_ ]⁺ y
  _∼⁺⟨_⟩_ : ∀ x {y z} (x∼⁺y : x [ _∼_ ]⁺ y) (y∼⁺z : y [ _∼_ ]⁺ z) →
            x [ _∼_ ]⁺ z

module _ {_∼_ : Rel A ℓ} where

 []-injective : ∀ {x y p q} → (x [ _∼_ ]⁺ y ∋ [ p ]) ≡ [ q ] → p ≡ q
 []-injective ≡.refl = ≡.refl

 -- See also ∼⁺⟨⟩-injectiveˡ and ∼⁺⟨⟩-injectiveʳ in
 -- Relation.Binary.Construct.Closure.Transitive.WithK.

-- "Equational" reasoning notation. Example:
--
--   lemma =
--     x  ∼⁺⟨ [ lemma₁ ] ⟩
--     y  ∼⁺⟨ lemma₂ ⟩∎
--     z  ∎

finally : ∀ {_∼_ : Rel A ℓ} x y → x [ _∼_ ]⁺ y → x [ _∼_ ]⁺ y
finally _ _ = id

syntax finally x y x∼⁺y = x ∼⁺⟨ x∼⁺y ⟩∎ y ∎

infixr 2 _∼⁺⟨_⟩_
infix  3 finally

-- Map.

map : {_R₁_ : Rel A ℓ} {_R₂_ : Rel B ℓ₂} {f : A → B} →
      _R₁_ =[ f ]⇒ _R₂_ → Plus _R₁_ =[ f ]⇒ Plus _R₂_
map R₁⇒R₂ [ xRy ]             = [ R₁⇒R₂ xRy ]
map R₁⇒R₂ (x ∼⁺⟨ xR⁺z ⟩ zR⁺y) =
  _ ∼⁺⟨ map R₁⇒R₂ xR⁺z ⟩ map R₁⇒R₂ zR⁺y

-- Plus and TransClosure are equivalent.
equivalent : ∀ {_∼_ : Rel A ℓ} {x y} →
             Plus _∼_ x y ⇔ TransClosure _∼_ x y
equivalent {_∼_ = _∼_} = mk⇔ complete sound
  where
  complete : Plus _∼_ ⇒ TransClosure _∼_
  complete [ x∼y ]             = [ x∼y ]
  complete (x ∼⁺⟨ x∼⁺y ⟩ y∼⁺z) = complete x∼⁺y ++ complete y∼⁺z

  sound : TransClosure _∼_ ⇒ Plus _∼_
  sound [ x∼y ]      = [ x∼y ]
  sound (x∼y ∷ y∼⁺z) = _ ∼⁺⟨ [ x∼y ] ⟩ sound y∼⁺z

------------------------------------------------------------------------
-- Deprecations
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- v1.5

Plus′ = TransClosure
{-# WARNING_ON_USAGE Plus′
"Warning: Plus′ was deprecated in v1.5.
Please use TransClosure instead."
#-}
