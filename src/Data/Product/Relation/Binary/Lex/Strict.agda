------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a strict partial order.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Relation.Binary.Lex.Strict where

open import Data.Product.Base
open import Data.Product.Relation.Binary.Pointwise.NonDependent as Pointwise
  using (Pointwise)
open import Data.Sum.Base using (inj₁; inj₂; _-⊎-_; [_,_])
open import Function.Base using (flip; _on_; _$_; _∘_)
open import Induction.WellFounded using (Acc; acc; WfRec; WellFounded; Acc-resp-flip-≈)
open import Level using (Level)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles
  using (Preorder; StrictPartialOrder; StrictTotalOrder)
open import Relation.Binary.Structures
  using (IsEquivalence; IsPreorder; IsStrictPartialOrder; IsStrictTotalOrder)
open import Relation.Binary.Definitions
  using (Transitive; Symmetric; Irreflexive; Asymmetric; Total; Decidable
        ; Antisymmetric; Trichotomous; _Respects₂_; _Respectsʳ_; _Respectsˡ_
        ; tri<; tri>; tri≈)
open import Relation.Binary.Consequences using (asym⇒irr)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Nullary.Decidable.Core using (yes; no; _⊎?_; _×?_)
open import Relation.Nullary.Negation.Core using (contradiction)

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- A lexicographic ordering over products

×-Lex : (_≈₁_ : Rel A ℓ₁) (_<₁_ : Rel A ℓ₂) (_≤₂_ : Rel B ℓ₃) →
        Rel (A × B) _
×-Lex _≈₁_ _<₁_ _≤₂_ =
  (_<₁_ on proj₁) -⊎- (_≈₁_ on proj₁) -×- (_≤₂_ on proj₂)

------------------------------------------------------------------------
-- Some properties which are preserved by ×-Lex (under certain
-- assumptions).

×-reflexive : (_≈₁_ : Rel A ℓ₁) (_∼₁_ : Rel A ℓ₂)
              {_≈₂_ : Rel B ℓ₃} (_≤₂_ : Rel B ℓ₄) →
              _≈₂_ ⇒ _≤₂_ → (Pointwise _≈₁_ _≈₂_) ⇒ (×-Lex _≈₁_ _∼₁_ _≤₂_)
×-reflexive _ _ _ refl₂ = λ x≈y →
  inj₂ (proj₁ x≈y , refl₂ (proj₂ x≈y))

module _ {_≈₁_ : Rel A ℓ₁} {_<₁_ : Rel A ℓ₂} {_<₂_ : Rel B ℓ₃} where

  private
    _<ₗₑₓ_ = ×-Lex _≈₁_ _<₁_ _<₂_


  ×-transitive : IsEquivalence _≈₁_ → _<₁_ Respects₂ _≈₁_ → Transitive _<₁_ →
                 Transitive _<₂_ → Transitive _<ₗₑₓ_
  ×-transitive eq₁ resp₁ trans₁ trans₂ = trans
    where
    module Eq₁ = IsEquivalence eq₁

    trans : Transitive _<ₗₑₓ_
    trans (inj₁ x₁<y₁) (inj₁ y₁<z₁) = inj₁ (trans₁ x₁<y₁ y₁<z₁)
    trans (inj₁ x₁<y₁) (inj₂ y≈≤z)  =
      inj₁ (proj₁ resp₁ (proj₁ y≈≤z) x₁<y₁)
    trans (inj₂ x≈≤y)  (inj₁ y₁<z₁) =
      inj₁ (proj₂ resp₁ (Eq₁.sym $ proj₁ x≈≤y) y₁<z₁)
    trans (inj₂ x≈≤y)  (inj₂ y≈≤z)  =
      inj₂ ( Eq₁.trans (proj₁ x≈≤y) (proj₁ y≈≤z)
           , trans₂    (proj₂ x≈≤y) (proj₂ y≈≤z))

  ×-asymmetric : Symmetric _≈₁_ → _<₁_ Respects₂ _≈₁_ →
                 Asymmetric _<₁_ → Asymmetric _<₂_ →
                 Asymmetric _<ₗₑₓ_
  ×-asymmetric sym₁ resp₁ asym₁ asym₂ = asym
    where
    irrefl₁ : Irreflexive _≈₁_ _<₁_
    irrefl₁ = asym⇒irr resp₁ sym₁ asym₁

    asym : Asymmetric _<ₗₑₓ_
    asym (inj₁ x₁<y₁) (inj₁ y₁<x₁) = asym₁ x₁<y₁ y₁<x₁
    asym (inj₁ x₁<y₁) (inj₂ y≈<x)  = irrefl₁ (sym₁ $ proj₁ y≈<x) x₁<y₁
    asym (inj₂ x≈<y)  (inj₁ y₁<x₁) = irrefl₁ (sym₁ $ proj₁ x≈<y) y₁<x₁
    asym (inj₂ x≈<y)  (inj₂ y≈<x)  = asym₂ (proj₂ x≈<y) (proj₂ y≈<x)

  ×-total₁ : Total _<₁_ → Total _<ₗₑₓ_
  ×-total₁ total₁ x y with total₁ (proj₁ x) (proj₁ y)
  ... | inj₁ x₁<y₁ = inj₁ (inj₁ x₁<y₁)
  ... | inj₂ x₁>y₁ = inj₂ (inj₁ x₁>y₁)

  ×-total₂ : Symmetric _≈₁_ →
             Trichotomous _≈₁_ _<₁_ → Total _<₂_ →
             Total _<ₗₑₓ_
  ×-total₂ sym tri₁ total₂ x y with tri₁ (proj₁ x) (proj₁ y)
  ... | tri< x₁<y₁ _ _ = inj₁ (inj₁ x₁<y₁)
  ... | tri> _ _ y₁<x₁ = inj₂ (inj₁ y₁<x₁)
  ... | tri≈ _ x₁≈y₁ _ with total₂ (proj₂ x) (proj₂ y)
  ...   | inj₁ x₂≤y₂ = inj₁ (inj₂ (x₁≈y₁     , x₂≤y₂))
  ...   | inj₂ y₂≤x₂ = inj₂ (inj₂ (sym x₁≈y₁ , y₂≤x₂))

  <ₗₑₓ? : Decidable _≈₁_ → Decidable _<₁_ → Decidable _<₂_ →
                Decidable _<ₗₑₓ_
  <ₗₑₓ? _≈₁?_ _<₁?_ _<₂?_ x y =
    proj₁ x <₁? proj₁ y
      ⊎?
    (proj₁ x ≈₁? proj₁ y
       ×?
     proj₂ x <₂? proj₂ y)

module _ {_≈₁_ : Rel A ℓ₁} {_<₁_ : Rel A ℓ₂}
         {_≈₂_ : Rel B ℓ₃} {_<₂_ : Rel B ℓ₄} where

  private
    _≋_    = Pointwise _≈₁_ _≈₂_
    _<ₗₑₓ_ = ×-Lex _≈₁_ _<₁_ _<₂_

  ×-irreflexive : Irreflexive _≈₁_ _<₁_ → Irreflexive _≈₂_ _<₂_ →
                  Irreflexive (Pointwise _≈₁_ _≈₂_) _<ₗₑₓ_
  ×-irreflexive ir₁ ir₂ x≈y (inj₁ x₁<y₁) = ir₁ (proj₁ x≈y) x₁<y₁
  ×-irreflexive ir₁ ir₂ x≈y (inj₂ x≈<y)  = ir₂ (proj₂ x≈y) (proj₂ x≈<y)

  ×-antisymmetric : Symmetric _≈₁_ → Irreflexive _≈₁_ _<₁_ → Asymmetric _<₁_ →
                    Antisymmetric _≈₂_ _<₂_ → Antisymmetric _≋_ _<ₗₑₓ_
  ×-antisymmetric sym₁ irrefl₁ asym₁ antisym₂ = antisym
    where
    antisym : Antisymmetric _≋_ _<ₗₑₓ_
    antisym (inj₁ x₁<y₁) (inj₁ y₁<x₁) =
      contradiction y₁<x₁ (asym₁ x₁<y₁)
    antisym (inj₁ x₁<y₁) (inj₂ y≈≤x)  =
      contradiction x₁<y₁ (irrefl₁ (sym₁ $ proj₁ y≈≤x))
    antisym (inj₂ x≈≤y)  (inj₁ y₁<x₁) =
      contradiction y₁<x₁ (irrefl₁ (sym₁ $ proj₁ x≈≤y))
    antisym (inj₂ x≈≤y)  (inj₂ y≈≤x)  =
      proj₁ x≈≤y , antisym₂ (proj₂ x≈≤y) (proj₂ y≈≤x)

  ×-respectsʳ : Transitive _≈₁_ →
                _<₁_ Respectsʳ _≈₁_ → _<₂_ Respectsʳ _≈₂_ →
                _<ₗₑₓ_ Respectsʳ _≋_
  ×-respectsʳ trans resp₁ resp₂ y≈y' (inj₁ x₁<y₁) = inj₁ (resp₁ (proj₁ y≈y') x₁<y₁)
  ×-respectsʳ trans resp₁ resp₂ y≈y' (inj₂ x≈<y)  = inj₂ (trans (proj₁ x≈<y) (proj₁ y≈y')
                                                       , (resp₂ (proj₂ y≈y') (proj₂ x≈<y)))

  ×-respectsˡ : Symmetric _≈₁_ → Transitive _≈₁_ →
                _<₁_ Respectsˡ _≈₁_ → _<₂_ Respectsˡ _≈₂_ →
                _<ₗₑₓ_ Respectsˡ _≋_
  ×-respectsˡ sym trans resp₁ resp₂ x≈x' (inj₁ x₁<y₁) = inj₁ (resp₁ (proj₁ x≈x') x₁<y₁)
  ×-respectsˡ sym trans resp₁ resp₂ x≈x' (inj₂ x≈<y)  = inj₂ (trans (sym $ proj₁ x≈x') (proj₁ x≈<y)
                                                           , (resp₂ (proj₂ x≈x') (proj₂ x≈<y)))

  ×-respects₂ : IsEquivalence _≈₁_ →
                _<₁_ Respects₂ _≈₁_ → _<₂_ Respects₂ _≈₂_ →
                _<ₗₑₓ_ Respects₂ _≋_
  ×-respects₂ eq₁ resp₁ resp₂ = ×-respectsʳ trans (proj₁ resp₁) (proj₁ resp₂)
                              , ×-respectsˡ sym trans (proj₂ resp₁) (proj₂ resp₂)
    where open IsEquivalence eq₁

  ×-compare : Symmetric _≈₁_ →
              Trichotomous _≈₁_ _<₁_ → Trichotomous _≈₂_ _<₂_ →
              Trichotomous _≋_ _<ₗₑₓ_
  ×-compare sym₁ cmp₁ cmp₂ (x₁ , x₂) (y₁ , y₂) with cmp₁ x₁ y₁
  ... | (tri< x₁<y₁ x₁≉y₁ x₁≯y₁) =
    tri< (inj₁ x₁<y₁)
         (x₁≉y₁ ∘ proj₁)
         [ x₁≯y₁ , x₁≉y₁ ∘ sym₁ ∘ proj₁ ]
  ... | (tri> x₁≮y₁ x₁≉y₁ x₁>y₁) =
    tri> [ x₁≮y₁ , x₁≉y₁ ∘ proj₁ ]
         (x₁≉y₁ ∘ proj₁)
         (inj₁ x₁>y₁)
  ... | (tri≈ x₁≮y₁ x₁≈y₁ x₁≯y₁) with cmp₂ x₂ y₂
  ...   | (tri< x₂<y₂ x₂≉y₂ x₂≯y₂) =
    tri< (inj₂ (x₁≈y₁ , x₂<y₂))
         (x₂≉y₂ ∘ proj₂)
         [ x₁≯y₁ , x₂≯y₂ ∘ proj₂ ]
  ...   | (tri> x₂≮y₂ x₂≉y₂ x₂>y₂) =
    tri> [ x₁≮y₁ , x₂≮y₂ ∘ proj₂ ]
         (x₂≉y₂ ∘ proj₂)
         (inj₂ (sym₁ x₁≈y₁ , x₂>y₂))
  ...   | (tri≈ x₂≮y₂ x₂≈y₂ x₂≯y₂) =
    tri≈ [ x₁≮y₁ , x₂≮y₂ ∘ proj₂ ]
         (x₁≈y₁ , x₂≈y₂)
         [ x₁≯y₁ , x₂≯y₂ ∘ proj₂ ]

module _ {_≈₁_ : Rel A ℓ₁} {_<₁_ : Rel A ℓ₂} {_<₂_ : Rel B ℓ₃} where

  private
    _<ₗₑₓ_ = ×-Lex _≈₁_ _<₁_ _<₂_

  ×-wellFounded' : Transitive _≈₁_ →
                   _<₁_ Respectsʳ _≈₁_ →
                   WellFounded _<₁_ →
                   WellFounded _<₂_ →
                   WellFounded _<ₗₑₓ_
  ×-wellFounded' trans resp wf₁ wf₂ (x , y) = acc (×-acc (wf₁ x) (wf₂ y))
    where
    ×-acc : ∀ {x y} →
            Acc _<₁_ x → Acc _<₂_ y →
            WfRec _<ₗₑₓ_ (Acc _<ₗₑₓ_) (x , y)
    ×-acc (acc rec₁) acc₂ (inj₁ u<x)
      = acc (×-acc (rec₁ u<x) (wf₂ _))
    ×-acc acc₁ (acc rec₂) (inj₂ (u≈x , v<y))
      = Acc-resp-flip-≈
        (×-respectsʳ {_<₁_ = _<₁_} {_<₂_ = _<₂_} trans resp (≡.respʳ _<₂_))
        (u≈x , ≡.refl)
        (acc (×-acc acc₁ (rec₂ v<y)))


module _ {_<₁_ : Rel A ℓ₁} {_<₂_ : Rel B ℓ₂} where

  private
    _<ₗₑₓ_ = ×-Lex _≡_ _<₁_ _<₂_

  ×-wellFounded : WellFounded _<₁_ →
                  WellFounded _<₂_ →
                  WellFounded _<ₗₑₓ_
  ×-wellFounded = ×-wellFounded' ≡.trans (≡.respʳ _<₁_)

------------------------------------------------------------------------
-- Collections of properties which are preserved by ×-Lex.

module _ {_≈₁_ : Rel A ℓ₁} {_<₁_ : Rel A ℓ₂}
         {_≈₂_ : Rel B ℓ₃} {_<₂_ : Rel B ℓ₄} where

  private
    _≋_    = Pointwise _≈₁_ _≈₂_
    _<ₗₑₓ_ = ×-Lex _≈₁_ _<₁_ _<₂_

  ×-isPreorder : IsPreorder _≈₁_ _<₁_ →
                 IsPreorder _≈₂_ _<₂_ →
                 IsPreorder _≋_ _<ₗₑₓ_
  ×-isPreorder pre₁ pre₂ =
    record
      { isEquivalence = Pointwise.×-isEquivalence
                          (isEquivalence pre₁) (isEquivalence pre₂)
      ; reflexive     = ×-reflexive _≈₁_ _<₁_ _<₂_ (reflexive pre₂)
      ; trans         = ×-transitive {_<₂_ = _<₂_}
                          (isEquivalence pre₁) (≲-resp-≈ pre₁)
                          (trans pre₁) (trans pre₂)
      }
    where open IsPreorder

  ×-isStrictPartialOrder : IsStrictPartialOrder _≈₁_ _<₁_ →
                           IsStrictPartialOrder _≈₂_ _<₂_ →
                           IsStrictPartialOrder _≋_ _<ₗₑₓ_
  ×-isStrictPartialOrder spo₁ spo₂ =
    record
      { isEquivalence = Pointwise.×-isEquivalence
                          (isEquivalence spo₁) (isEquivalence spo₂)
      ; irrefl        = ×-irreflexive {_<₁_ = _<₁_} {_<₂_ = _<₂_}
                          (irrefl spo₁) (irrefl spo₂)
      ; trans         = ×-transitive {_<₁_ = _<₁_} {_<₂_ = _<₂_}
                          (isEquivalence spo₁)
                          (<-resp-≈ spo₁) (trans spo₁)
                          (trans spo₂)
      ; <-resp-≈      = ×-respects₂ (isEquivalence spo₁)
                                      (<-resp-≈ spo₁)
                                      (<-resp-≈ spo₂)
      }
    where open IsStrictPartialOrder

  ×-isStrictTotalOrder : IsStrictTotalOrder _≈₁_ _<₁_ →
                         IsStrictTotalOrder _≈₂_ _<₂_ →
                         IsStrictTotalOrder _≋_ _<ₗₑₓ_
  ×-isStrictTotalOrder spo₁ spo₂ =
    record
      { isStrictPartialOrder = ×-isStrictPartialOrder
                                 (isStrictPartialOrder spo₁)
                                 (isStrictPartialOrder spo₂)
      ; compare       = ×-compare (Eq.sym spo₁) (compare spo₁)
                                                (compare spo₂)
      }
    where open IsStrictTotalOrder

------------------------------------------------------------------------
-- "Bundles" can also be combined.

×-preorder : Preorder a ℓ₁ ℓ₂ →
             Preorder b ℓ₃ ℓ₄ →
             Preorder _ _ _
×-preorder p₁ p₂ = record
  { isPreorder = ×-isPreorder (isPreorder p₁) (isPreorder p₂)
  } where open Preorder

×-strictPartialOrder : StrictPartialOrder a ℓ₁ ℓ₂ →
                       StrictPartialOrder b ℓ₃ ℓ₄ →
                       StrictPartialOrder _ _ _
×-strictPartialOrder s₁ s₂ = record
  { isStrictPartialOrder = ×-isStrictPartialOrder
      (isStrictPartialOrder s₁) (isStrictPartialOrder s₂)
  } where open StrictPartialOrder

×-strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂ →
                     StrictTotalOrder b ℓ₃ ℓ₄ →
                     StrictTotalOrder _ _ _
×-strictTotalOrder s₁ s₂ = record
  { isStrictTotalOrder = ×-isStrictTotalOrder
      (isStrictTotalOrder s₁) (isStrictTotalOrder s₂)
  } where open StrictTotalOrder


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.4

×-decidable = <ₗₑₓ?
{-# WARNING_ON_USAGE ×-decidable
"Warning: ×-decidable was deprecated in v2.4.
Please use <ₗₑₓ? instead."
#-}
