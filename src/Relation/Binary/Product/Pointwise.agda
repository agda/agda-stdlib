------------------------------------------------------------------------
-- Pointwise products of binary relations
------------------------------------------------------------------------

module Relation.Binary.Product.Pointwise where

open import Data.Product as Prod
open import Data.Sum
open import Data.Unit using (⊤)
open import Function
open import Function.Equality as F using (_⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalent; _⇔_; module Equivalent)
  renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse as Inv
  using (Inverse; _⇿_; module Inverse)
  renaming (_∘_ to _⟪∘⟫_)
open import Function.LeftInverse
  using (_LeftInverseOf_; _RightInverseOf_)
open import Level
open import Relation.Nullary.Product
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

private
 module Dummy {a₁ a₂ : Set} where

  infixr 2 _×-Rel_

  _×-Rel_ : Rel a₁ zero → Rel a₂ zero → Rel (a₁ × a₂) zero
  ∼₁ ×-Rel ∼₂ = (∼₁ on proj₁) -×- (∼₂ on proj₂)

  -- Some properties which are preserved by ×-Rel (under certain
  -- assumptions).

  _×-reflexive_ : ∀ {≈₁ ∼₁ ≈₂ ∼₂} →
                  ≈₁ ⇒ ∼₁ → ≈₂ ⇒ ∼₂ → (≈₁ ×-Rel ≈₂) ⇒ (∼₁ ×-Rel ∼₂)
  refl₁ ×-reflexive refl₂ = λ x≈y →
    (refl₁ (proj₁ x≈y) , refl₂ (proj₂ x≈y))

  _×-refl_ : ∀ {∼₁ ∼₂} →
             Reflexive ∼₁ → Reflexive ∼₂ → Reflexive (∼₁ ×-Rel ∼₂)
  refl₁ ×-refl refl₂ = (refl₁ , refl₂)

  ×-irreflexive₁ :
    ∀ {≈₁ <₁ ≈₂ <₂} →
    Irreflexive ≈₁ <₁ → Irreflexive (≈₁ ×-Rel ≈₂) (<₁ ×-Rel <₂)
  ×-irreflexive₁ ir = λ x≈y x<y → ir (proj₁ x≈y) (proj₁ x<y)

  ×-irreflexive₂ :
    ∀ {≈₁ <₁ ≈₂ <₂} →
    Irreflexive ≈₂ <₂ → Irreflexive (≈₁ ×-Rel ≈₂) (<₁ ×-Rel <₂)
  ×-irreflexive₂ ir = λ x≈y x<y → ir (proj₂ x≈y) (proj₂ x<y)

  _×-symmetric_ : ∀ {∼₁ ∼₂} →
                  Symmetric ∼₁ → Symmetric ∼₂ → Symmetric (∼₁ ×-Rel ∼₂)
  sym₁ ×-symmetric sym₂ = λ x∼y → sym₁ (proj₁ x∼y) , sym₂ (proj₂ x∼y)

  _×-transitive_ : ∀ {∼₁ ∼₂} →
                   Transitive ∼₁ → Transitive ∼₂ →
                   Transitive (∼₁ ×-Rel ∼₂)
  trans₁ ×-transitive trans₂ = λ x∼y y∼z →
    trans₁ (proj₁ x∼y) (proj₁ y∼z) ,
    trans₂ (proj₂ x∼y) (proj₂ y∼z)

  _×-antisymmetric_ : ∀ {≈₁ ≤₁ ≈₂ ≤₂} →
                      Antisymmetric ≈₁ ≤₁ → Antisymmetric ≈₂ ≤₂ →
                      Antisymmetric (≈₁ ×-Rel ≈₂) (≤₁ ×-Rel ≤₂)
  antisym₁ ×-antisymmetric antisym₂ = λ x≤y y≤x →
    ( antisym₁ (proj₁ x≤y) (proj₁ y≤x)
    , antisym₂ (proj₂ x≤y) (proj₂ y≤x) )

  ×-asymmetric₁ : ∀ {<₁ ∼₂} → Asymmetric <₁ → Asymmetric (<₁ ×-Rel ∼₂)
  ×-asymmetric₁ asym₁ = λ x<y y<x → asym₁ (proj₁ x<y) (proj₁ y<x)

  ×-asymmetric₂ : ∀ {∼₁ <₂} → Asymmetric <₂ → Asymmetric (∼₁ ×-Rel <₂)
  ×-asymmetric₂ asym₂ = λ x<y y<x → asym₂ (proj₂ x<y) (proj₂ y<x)

  _×-≈-respects₂_ : ∀ {≈₁ ∼₁ ≈₂ ∼₂} →
                    ∼₁ Respects₂ ≈₁ → ∼₂ Respects₂ ≈₂ →
                    (∼₁ ×-Rel ∼₂) Respects₂ (≈₁ ×-Rel ≈₂)
  _×-≈-respects₂_ {≈₁ = ≈₁} {∼₁ = ∼₁} {≈₂ = ≈₂} {∼₂ = ∼₂}
                  resp₁ resp₂ =
    (λ {x y z} → resp¹ {x} {y} {z}) ,
    (λ {x y z} → resp² {x} {y} {z})
    where
    ∼ = ∼₁ ×-Rel ∼₂

    resp¹ : ∀ {x} → (∼ x) Respects (≈₁ ×-Rel ≈₂)
    resp¹ y≈y' x∼y = proj₁ resp₁ (proj₁ y≈y') (proj₁ x∼y) ,
                     proj₁ resp₂ (proj₂ y≈y') (proj₂ x∼y)

    resp² : ∀ {y} → (flip ∼ y) Respects (≈₁ ×-Rel ≈₂)
    resp² x≈x' x∼y = proj₂ resp₁ (proj₁ x≈x') (proj₁ x∼y) ,
                     proj₂ resp₂ (proj₂ x≈x') (proj₂ x∼y)

  ×-total : ∀ {∼₁ ∼₂} →
            Symmetric ∼₁ → Total ∼₁ → Total ∼₂ → Total (∼₁ ×-Rel ∼₂)
  ×-total {∼₁ = ∼₁} {∼₂ = ∼₂} sym₁ total₁ total₂ = total
    where
    total : Total (∼₁ ×-Rel ∼₂)
    total x y with total₁ (proj₁ x) (proj₁ y)
                 | total₂ (proj₂ x) (proj₂ y)
    ... | inj₁ x₁∼y₁ | inj₁ x₂∼y₂ = inj₁ (     x₁∼y₁ , x₂∼y₂)
    ... | inj₁ x₁∼y₁ | inj₂ y₂∼x₂ = inj₂ (sym₁ x₁∼y₁ , y₂∼x₂)
    ... | inj₂ y₁∼x₁ | inj₂ y₂∼x₂ = inj₂ (     y₁∼x₁ , y₂∼x₂)
    ... | inj₂ y₁∼x₁ | inj₁ x₂∼y₂ = inj₁ (sym₁ y₁∼x₁ , x₂∼y₂)

  _×-decidable_ : ∀ {∼₁ ∼₂} →
                  Decidable ∼₁ → Decidable ∼₂ → Decidable (∼₁ ×-Rel ∼₂)
  dec₁ ×-decidable dec₂ = λ x y →
    dec₁ (proj₁ x) (proj₁ y)
      ×-dec
    dec₂ (proj₂ x) (proj₂ y)

  -- Some collections of properties which are preserved by ×-Rel.

  _×-isEquivalence_ : ∀ {≈₁ ≈₂} →
                      IsEquivalence ≈₁ → IsEquivalence ≈₂ →
                      IsEquivalence (≈₁ ×-Rel ≈₂)
  _×-isEquivalence_ {≈₁ = ≈₁} {≈₂ = ≈₂} eq₁ eq₂ = record
    { refl  = λ {x} →
              _×-refl_        {∼₁ = ≈₁} {∼₂ = ≈₂}
                              (refl  eq₁) (refl  eq₂) {x}
    ; sym   = λ {x y} →
              _×-symmetric_   {∼₁ = ≈₁} {∼₂ = ≈₂}
                              (sym   eq₁) (sym   eq₂) {x} {y}
    ; trans = λ {x y z} →
              _×-transitive_  {∼₁ = ≈₁} {∼₂ = ≈₂}
                              (trans eq₁) (trans eq₂) {x} {y} {z}
    }
    where open IsEquivalence

  _×-isPreorder_ : ∀ {≈₁ ∼₁ ≈₂ ∼₂} →
                   IsPreorder ≈₁ ∼₁ → IsPreorder ≈₂ ∼₂ →
                   IsPreorder (≈₁ ×-Rel ≈₂) (∼₁ ×-Rel ∼₂)
  _×-isPreorder_ {∼₁ = ∼₁} {∼₂ = ∼₂} pre₁ pre₂ = record
    { isEquivalence = isEquivalence pre₁ ×-isEquivalence
                      isEquivalence pre₂
    ; reflexive     = λ {x y} →
                      _×-reflexive_  {∼₁ = ∼₁} {∼₂ = ∼₂}
                                     (reflexive pre₁) (reflexive pre₂)
                                     {x} {y}
    ; trans         = λ {x y z} →
                      _×-transitive_ {∼₁ = ∼₁} {∼₂ = ∼₂}
                                     (trans pre₁) (trans pre₂)
                                     {x} {y} {z}
    ; ∼-resp-≈      = ∼-resp-≈ pre₁ ×-≈-respects₂ ∼-resp-≈ pre₂
    }
    where open IsPreorder

  _×-isDecEquivalence_ : ∀ {≈₁ ≈₂} →
                         IsDecEquivalence ≈₁ → IsDecEquivalence ≈₂ →
                         IsDecEquivalence (≈₁ ×-Rel ≈₂)
  eq₁ ×-isDecEquivalence eq₂ = record
    { isEquivalence = isEquivalence eq₁ ×-isEquivalence
                      isEquivalence eq₂
    ; _≟_           = _≟_ eq₁ ×-decidable _≟_ eq₂
    }
    where open IsDecEquivalence

  _×-isPartialOrder_ : ∀ {≈₁ ≤₁ ≈₂ ≤₂} →
                       IsPartialOrder ≈₁ ≤₁ → IsPartialOrder ≈₂ ≤₂ →
                       IsPartialOrder (≈₁ ×-Rel ≈₂) (≤₁ ×-Rel ≤₂)
  _×-isPartialOrder_ {≤₁ = ≤₁} {≤₂ = ≤₂} po₁ po₂ = record
    { isPreorder = isPreorder po₁ ×-isPreorder isPreorder po₂
    ; antisym    = λ {x y} →
                   _×-antisymmetric_ {≤₁ = ≤₁} {≤₂ = ≤₂}
                                     (antisym po₁) (antisym po₂)
                                     {x} {y}
    }
    where open IsPartialOrder

  _×-isStrictPartialOrder_ :
    ∀ {≈₁ <₁ ≈₂ <₂} →
    IsStrictPartialOrder ≈₁ <₁ → IsStrictPartialOrder ≈₂ <₂ →
    IsStrictPartialOrder (≈₁ ×-Rel ≈₂) (<₁ ×-Rel <₂)
  _×-isStrictPartialOrder_ {<₁ = <₁} {≈₂ = ≈₂} {<₂ = <₂} spo₁ spo₂ =
    record
      { isEquivalence = isEquivalence spo₁ ×-isEquivalence
                        isEquivalence spo₂
      ; irrefl        = λ {x y} →
                        ×-irreflexive₁ {<₁ = <₁} {≈₂ = ≈₂} {<₂ = <₂}
                                       (irrefl spo₁) {x} {y}
      ; trans         = λ {x y z} →
                        _×-transitive_ {∼₁ = <₁} {∼₂ = <₂}
                                       (trans spo₁) (trans spo₂)
                                       {x} {y} {z}
      ; <-resp-≈      = <-resp-≈ spo₁ ×-≈-respects₂ <-resp-≈ spo₂
      }
    where open IsStrictPartialOrder

open Dummy public

-- "Packages" (e.g. setoids) can also be combined.

_×-preorder_ : Preorder _ _ _ → Preorder _ _ _ → Preorder _ _ _
p₁ ×-preorder p₂ = record
  { isPreorder = isPreorder p₁ ×-isPreorder isPreorder p₂
  } where open Preorder

_×-setoid_ : Setoid _ _ → Setoid _ _ → Setoid _ _
s₁ ×-setoid s₂ = record
  { isEquivalence = isEquivalence s₁ ×-isEquivalence isEquivalence s₂
  } where open Setoid

_×-decSetoid_ : DecSetoid _ _ → DecSetoid _ _ → DecSetoid _ _
s₁ ×-decSetoid s₂ = record
  { isDecEquivalence = isDecEquivalence s₁ ×-isDecEquivalence
                       isDecEquivalence s₂
  } where open DecSetoid

_×-poset_ : Poset _ _ _ → Poset _ _ _ → Poset _ _ _
s₁ ×-poset s₂ = record
  { isPartialOrder = isPartialOrder s₁ ×-isPartialOrder
                     isPartialOrder s₂
  } where open Poset

_×-strictPartialOrder_ :
  StrictPartialOrder _ _ _ → StrictPartialOrder _ _ _ →
  StrictPartialOrder _ _ _
s₁ ×-strictPartialOrder s₂ = record
  { isStrictPartialOrder = isStrictPartialOrder s₁
                             ×-isStrictPartialOrder
                           isStrictPartialOrder s₂
  } where open StrictPartialOrder

------------------------------------------------------------------------
-- Some properties related to equivalences and inverses

×-left-identity : {A : Set} → (⊤ × A) ⇿ A
×-left-identity = record
  { to         = P.→-to-⟶ proj₂
  ; from       = P.→-to-⟶ (λ y → _ , y)
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

×-right-identity : {A : Set} → (A × ⊤) ⇿ A
×-right-identity = record
  { to         = P.→-to-⟶ proj₁
  ; from       = P.→-to-⟶ (λ x → x , _)
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

×-assoc : {A B C : Set} → ((A × B) × C) ⇿ (A × (B × C))
×-assoc = record
  { to         = P.→-to-⟶ λ t → (proj₁ (proj₁ t) , (proj₂ (proj₁ t) , proj₂ t))
  ; from       = P.→-to-⟶ λ t → ((proj₁ t , proj₁ (proj₂ t)) , proj₂ (proj₂ t))
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

×-comm : {A B : Set} → (A × B) ⇿ (B × A)
×-comm = record
  { to         = P.→-to-⟶ swap
  ; from       = P.→-to-⟶ swap
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

∃×⇿×∃ : {A B : Set} {C : A → Set} →
        (∃ λ x → B × C x) ⇿ (B × ∃ λ x → C x)
∃×⇿×∃ = record
  { to         = P.→-to-⟶ λ p → (proj₁ (proj₂ p) , proj₁ p , proj₂ (proj₂ p))
  ; from       = P.→-to-⟶ λ p → (proj₁ (proj₂ p) , proj₁ p , proj₂ (proj₂ p))
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

×-Rel⇿≡ : {A B : Set} →
          Inverse (P.setoid A ×-setoid P.setoid B) (P.setoid (A × B))
×-Rel⇿≡ = record
  { to         = record { _⟨$⟩_ = id; cong = to-cong   }
  ; from       = record { _⟨$⟩_ = id; cong = from-cong }
  ; inverse-of = record
    { left-inverse-of  = λ _ → (P.refl , P.refl)
    ; right-inverse-of = λ _ → P.refl
    }
  }
  where
  to-cong : (P._≡_ ×-Rel P._≡_) ⇒ P._≡_
  to-cong {i = (x , y)} {j = (.x , .y)} (P.refl , P.refl) = P.refl

  from-cong : P._≡_ ⇒ (P._≡_ ×-Rel P._≡_)
  from-cong P.refl = (P.refl , P.refl)

_×-equivalent_ :
  {A B C D : Setoid zero zero} →
  Equivalent A B → Equivalent C D →
  Equivalent (A ×-setoid C) (B ×-setoid D)
_×-equivalent_ {A} {B} {C} {D} A⇔B C⇔D = record
  { to   = record { _⟨$⟩_ = to;   cong = λ {x y} → to-cong   {x} {y} }
  ; from = record { _⟨$⟩_ = from; cong = λ {x y} → from-cong {x} {y} }
  }
  where
  open Setoid (A ×-setoid C) using () renaming (_≈_ to _≈AC_)
  open Setoid (B ×-setoid D) using () renaming (_≈_ to _≈BD_)

  to = Prod.map (_⟨$⟩_ (Equivalent.to A⇔B))
                (_⟨$⟩_ (Equivalent.to C⇔D))

  to-cong : _≈AC_ =[ to ]⇒ _≈BD_
  to-cong (∼₁ , ∼₂) =
    (F.cong (Equivalent.to A⇔B) ∼₁ , F.cong (Equivalent.to C⇔D) ∼₂)

  from = Prod.map (_⟨$⟩_ (Equivalent.from A⇔B))
                  (_⟨$⟩_ (Equivalent.from C⇔D))

  from-cong : _≈BD_ =[ from ]⇒ _≈AC_
  from-cong (∼₁ , ∼₂) =
    (F.cong (Equivalent.from A⇔B) ∼₁ , F.cong (Equivalent.from C⇔D) ∼₂)

_×-⇔_ : {A B C D : Set} → A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
A⇔B ×-⇔ C⇔D =
  Inverse.equivalent ×-Rel⇿≡ ⟨∘⟩
  A⇔B ×-equivalent C⇔D ⟨∘⟩
  Eq.sym (Inverse.equivalent ×-Rel⇿≡)

_×-inverse_ :
  {A B C D : Setoid zero zero} →
  Inverse A B → Inverse C D → Inverse (A ×-setoid C) (B ×-setoid D)
A⇿B ×-inverse C⇿D = record
  { to         = Equivalent.to   eq
  ; from       = Equivalent.from eq
  ; inverse-of = record
    { left-inverse-of  = left
    ; right-inverse-of = right
    }
  }
  where
  eq = Inverse.equivalent A⇿B ×-equivalent Inverse.equivalent C⇿D

  left : Equivalent.from eq LeftInverseOf Equivalent.to eq
  left (x , y) = ( Inverse.left-inverse-of A⇿B x
                 , Inverse.left-inverse-of C⇿D y
                 )

  right : Equivalent.from eq RightInverseOf Equivalent.to eq
  right (x , y) = ( Inverse.right-inverse-of A⇿B x
                  , Inverse.right-inverse-of C⇿D y
                  )

_×-⇿_ : {A B C D : Set} → A ⇿ B → C ⇿ D → (A × C) ⇿ (B × D)
A⇿B ×-⇿ C⇿D = ×-Rel⇿≡ ⟪∘⟫ A⇿B ×-inverse C⇿D ⟪∘⟫ Inv.sym ×-Rel⇿≡
