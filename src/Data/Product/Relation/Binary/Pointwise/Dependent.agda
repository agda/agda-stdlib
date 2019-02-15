------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of binary relations to sigma types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Relation.Binary.Pointwise.Dependent where

open import Data.Product as Prod
open import Level
open import Function
open import Function.Equality as F using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Equiv
  using (Equivalence; _⇔_; module Equivalence)
open import Function.HalfAdjointEquivalence using (_≃_; ↔→≃)
open import Function.Injection as Inj
  using (Injection; _↣_; module Injection; Injective)
open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; module LeftInverse;
         _LeftInverseOf_; _RightInverseOf_)
open import Function.Related as Related
  using (_∼[_]_; lam; app-←; app-↢)
open import Function.Related.TypeIsomorphisms
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)
open import Relation.Binary as B
  using (_⇒_; Setoid; IsEquivalence)
open import Relation.Binary.Indexed.Heterogeneous as I
  using (IREL; IRel; IndexedSetoid; IsIndexedEquivalence)
open import Relation.Binary.Indexed.Heterogeneous.Construct.At
  using (_atₛ_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Pointwise lifting

infixr 4 _,_

record POINTWISE {a₁ a₂ b₁ b₂ ℓ₁ ℓ₂}
                 {A₁ : Set a₁} (B₁ : A₁ → Set b₁)
                 {A₂ : Set a₂} (B₂ : A₂ → Set b₂)
                 (_R₁_ : B.REL A₁ A₂ ℓ₁) (_R₂_ : IREL B₁ B₂ ℓ₂)
                 (xy₁ : Σ A₁ B₁) (xy₂ : Σ A₂ B₂)
                 : Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    proj₁ : (proj₁ xy₁) R₁ (proj₁ xy₂)
    proj₂ : (proj₂ xy₁) R₂ (proj₂ xy₂)

open POINTWISE public

Pointwise : ∀ {a b ℓ₁ ℓ₂} {A : Set a} (B : A → Set b)
            (_R₁_ : B.Rel A ℓ₁) (_R₂_ : IRel B ℓ₂) → B.Rel (Σ A B) _
Pointwise B = POINTWISE B B

------------------------------------------------------------------------
-- Pointwise preserves many relational properties

module _ {a b ℓ₁ ℓ₂} {A : Set a} {B : A → Set b}
         {R : B.Rel A ℓ₁} {S : IRel B ℓ₂} where

  private
    R×S = Pointwise B R S

  refl : B.Reflexive R → I.Reflexive B S → B.Reflexive R×S
  refl refl₁ refl₂ = (refl₁ , refl₂)

  symmetric : B.Symmetric R → I.Symmetric B S → B.Symmetric R×S
  symmetric sym₁ sym₂ (x₁Rx₂ , y₁Ry₂) = (sym₁ x₁Rx₂ , sym₂ y₁Ry₂)

  transitive : B.Transitive R → I.Transitive B S → B.Transitive R×S
  transitive trans₁ trans₂ (x₁Rx₂ , y₁Ry₂) (x₂Rx₃ , y₂Ry₃) =
    (trans₁ x₁Rx₂ x₂Rx₃ , trans₂ y₁Ry₂ y₂Ry₃)

  isEquivalence : IsEquivalence R → IsIndexedEquivalence B S →
                  IsEquivalence R×S
  isEquivalence eq₁ eq₂ = record
    { refl  = refl       Eq.refl  IEq.refl
    ; sym   = symmetric  Eq.sym   IEq.sym
    ; trans = transitive Eq.trans IEq.trans
    } where
    module Eq = IsEquivalence eq₁
    module IEq = IsIndexedEquivalence eq₂

module _ {a b ℓ₁ ℓ₂} where

  setoid : (A : Setoid a ℓ₁) →
           IndexedSetoid (Setoid.Carrier A) b ℓ₂ →
           Setoid _ _
  setoid s₁ s₂ = record
    { isEquivalence = isEquivalence Eq.isEquivalence IEq.isEquivalence
    } where
    module Eq = Setoid s₁
    module IEq = IndexedSetoid s₂




{-
------------------------------------------------------------------------
-- Properties related to "relatedness"
------------------------------------------------------------------------

private

  subst-cong : ∀ {i a p} {I : Set i} {A : I → Set a}
               (P : ∀ {i} → A i → A i → Set p) {i i′} {x y : A i}
               (i≡i′ : i P.≡ i′) →
               P x y → P (P.subst A i≡i′ x) (P.subst A i≡i′ y)
  subst-cong P P.refl p = p

⟶ : ∀ {a₁ a₂ b₁ b₁′ b₂ b₂′}
      {A₁ : Set a₁} {A₂ : Set a₂}
      {B₁ : IndexedSetoid A₁ b₁ b₁′} (B₂ : IndexedSetoid A₂ b₂ b₂′)
    (f : A₁ → A₂) → (∀ {x} → (B₁ atₛ x) ⟶ (B₂ atₛ (f x))) →
    setoid (P.setoid A₁) B₁ ⟶ setoid (P.setoid A₂) B₂
⟶ {A₁ = A₁} {A₂} {B₁} B₂ f g = record
  { _⟨$⟩_ = fg
  ; cong  = fg-cong
  }
  where
  open B.Setoid (setoid (P.setoid A₁) B₁)
    using () renaming (_≈_ to _≈₁_)
  open B.Setoid (setoid (P.setoid A₂) B₂)
    using () renaming (_≈_ to _≈₂_)
  open B using (_=[_]⇒_)

  fg = Prod.map f (_⟨$⟩_ g)

  fg-cong : _≈₁_ =[ fg ]⇒ _≈₂_
  fg-cong (P.refl , ∼) = (P.refl , F.cong g ∼)


module _ {a₁ a₂ b₁ b₁′ b₂ b₂′} {A₁ : Set a₁} {A₂ : Set a₂} where

  equivalence : {B₁ : IndexedSetoid A₁ b₁ b₁′} {B₂ : IndexedSetoid A₂ b₂ b₂′}
    (A₁⇔A₂ : A₁ ⇔ A₂) →
    (∀ {x} → _⟶_ (B₁ atₛ x) (B₂ atₛ (Equivalence.to   A₁⇔A₂ ⟨$⟩ x))) →
    (∀ {y} → _⟶_ (B₂ atₛ y) (B₁ atₛ (Equivalence.from A₁⇔A₂ ⟨$⟩ y))) →
    Equivalence (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  equivalence {B₁} {B₂} A₁⇔A₂ B-to B-from = record
    { to   = ⟶ B₂ (_⟨$⟩_ (to   A₁⇔A₂)) B-to
    ; from = ⟶ B₁ (_⟨$⟩_ (from A₁⇔A₂)) B-from
    } where open Equivalence

  equivalence-↞ : (B₁ : IndexedSetoid A₁ b₁ b₁′) {B₂ : IndexedSetoid A₂ b₂ b₂′}
    (A₁↞A₂ : A₁ ↞ A₂) →
    (∀ {x} → Equivalence (B₁ atₛ (LeftInverse.from A₁↞A₂ ⟨$⟩ x))
                         (B₂ atₛ x)) →
    Equivalence (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  equivalence-↞ B₁ {B₂} A₁↞A₂ B₁⇔B₂ =
    equivalence (LeftInverse.equivalence A₁↞A₂) B-to B-from
    where
    B-to : ∀ {x} → _⟶_ (B₁ atₛ x) (B₂ atₛ (LeftInverse.to A₁↞A₂ ⟨$⟩ x))
    B-to = record
      { _⟨$⟩_ = λ x → Equivalence.to B₁⇔B₂ ⟨$⟩
                      P.subst (IndexedSetoid.Carrier B₁)
                         (P.sym $ LeftInverse.left-inverse-of A₁↞A₂ _)
                         x
      ; cong  = F.cong (Equivalence.to B₁⇔B₂) ∘
              subst-cong (λ {x} → IndexedSetoid._≈_ B₁ {x} {x})
                         (P.sym (LeftInverse.left-inverse-of A₁↞A₂ _))
      }

    B-from : ∀ {y} → _⟶_ (B₂ atₛ y) (B₁ atₛ (LeftInverse.from A₁↞A₂ ⟨$⟩ y))
    B-from = Equivalence.from B₁⇔B₂

  equivalence-↠ : {B₁ : IndexedSetoid A₁ b₁ b₁′} (B₂ : IndexedSetoid A₂ b₂ b₂′)
    (A₁↠A₂ : A₁ ↠ A₂) →
    (∀ {x} → Equivalence (B₁ atₛ x) (B₂ atₛ (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
    Equivalence (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  equivalence-↠ {B₁ = B₁} B₂ A₁↠A₂ B₁⇔B₂ =
    equivalence (Surjection.equivalence A₁↠A₂) B-to B-from
    where
    B-to : ∀ {x} → _⟶_ (B₁ atₛ x) (B₂ atₛ (Surjection.to A₁↠A₂ ⟨$⟩ x))
    B-to = Equivalence.to B₁⇔B₂

    B-from : ∀ {y} → _⟶_ (B₂ atₛ y) (B₁ atₛ (Surjection.from A₁↠A₂ ⟨$⟩ y))
    B-from = record
      { _⟨$⟩_ = λ x → Equivalence.from B₁⇔B₂ ⟨$⟩
                      P.subst (IndexedSetoid.Carrier B₂)
                         (P.sym $ Surjection.right-inverse-of A₁↠A₂ _)
                         x
      ; cong  = F.cong (Equivalence.from B₁⇔B₂) ∘
              subst-cong (λ {x} → IndexedSetoid._≈_ B₂ {x} {x})
                         (P.sym (Surjection.right-inverse-of A₁↠A₂ _))
      }

  injection : {B₁ : IndexedSetoid A₁ b₁ b₁′} (B₂ : IndexedSetoid A₂ b₂ b₂′) →
    (A₁↣A₂ : A₁ ↣ A₂) →
    (∀ {x} → Injection (B₁ atₛ x) (B₂ atₛ (Injection.to A₁↣A₂ ⟨$⟩ x))) →
    Injection (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  injection {B₁ = B₁} B₂ A₁↣A₂ B₁↣B₂ = record
    { to        = to
    ; injective = inj
    }
    where
    to = ⟶ B₂ (Injection.to A₁↣A₂ ⟨$⟩_) (Injection.to B₁↣B₂)

    inj : Injective to
    inj (x , y) =
      Injection.injective A₁↣A₂ x ,
      lemma (Injection.injective A₁↣A₂ x) y
      where
      lemma :
        ∀ {x x′}
          {y : IndexedSetoid.Carrier B₁ x} {y′ : IndexedSetoid.Carrier B₁ x′} →
        x ≡ x′ →
        (eq : IndexedSetoid._≈_ B₂ (Injection.to B₁↣B₂ ⟨$⟩ y)
                              (Injection.to B₁↣B₂ ⟨$⟩ y′)) →
        IndexedSetoid._≈_ B₁ y y′
      lemma P.refl = Injection.injective B₁↣B₂

  left-inverse : (B₁ : IndexedSetoid A₁ b₁ b₁′) {B₂ : IndexedSetoid A₂ b₂ b₂′} →
    (A₁↞A₂ : A₁ ↞ A₂) →
    (∀ {x} → LeftInverse (B₁ atₛ (LeftInverse.from A₁↞A₂ ⟨$⟩ x))
                         (B₂ atₛ x)) →
    LeftInverse (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  left-inverse B₁ {B₂} A₁↞A₂ B₁↞B₂ = record
    { to              = Equivalence.to   eq
    ; from            = Equivalence.from eq
    ; left-inverse-of = left
    }
    where
    eq = equivalence-↞ B₁ A₁↞A₂ (LeftInverse.equivalence B₁↞B₂)

    left : Equivalence.from eq LeftInverseOf Equivalence.to eq
    left (x , y) =
      LeftInverse.left-inverse-of A₁↞A₂ x ,
      IndexedSetoid.trans B₁
        (LeftInverse.left-inverse-of B₁↞B₂ _)
        (lemma (P.sym (LeftInverse.left-inverse-of A₁↞A₂ x)))
      where
      lemma :
        ∀ {x x′ y} (eq : x ≡ x′) →
        IndexedSetoid._≈_ B₁ (P.subst (IndexedSetoid.Carrier B₁) eq y) y
      lemma P.refl = IndexedSetoid.refl B₁

  surjection : {B₁ : IndexedSetoid A₁ b₁ b₁′} (B₂ : IndexedSetoid A₂ b₂ b₂′) →
    (A₁↠A₂ : A₁ ↠ A₂) →
    (∀ {x} → Surjection (B₁ atₛ x) (B₂ atₛ (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
    Surjection (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  surjection B₂ A₁↠A₂ B₁↠B₂ = record
    { to         = Equivalence.to eq
    ; surjective = record
      { from             = Equivalence.from eq
      ; right-inverse-of = right
      }
    }
    where
    eq = equivalence-↠ B₂ A₁↠A₂ (Surjection.equivalence B₁↠B₂)

    right : Equivalence.from eq RightInverseOf Equivalence.to eq
    right (x , y) =
      Surjection.right-inverse-of A₁↠A₂ x ,
      IndexedSetoid.trans B₂
        (Surjection.right-inverse-of B₁↠B₂ _)
        (lemma (P.sym $ Surjection.right-inverse-of A₁↠A₂ x))
      where
      lemma : ∀ {x x′ y} (eq : x ≡ x′) →
              IndexedSetoid._≈_ B₂ (P.subst (IndexedSetoid.Carrier B₂) eq y) y
      lemma P.refl = IndexedSetoid.refl B₂

  -- See also Data.Product.Relation.Binary.Pointwise.Dependent.WithK.inverse.
-}

------------------------------------------------------------------------
-- TODO: The code in this section no longer depends on POINTWISE or
-- Pointwise. Perhaps it should be moved somewhere else.

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {b₁ b₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
         where

  ⇔ : (A₁⇔A₂ : A₁ ⇔ A₂) →
      (∀ {x} → B₁ x → B₂ (Equivalence.to   A₁⇔A₂ ⟨$⟩ x)) →
      (∀ {y} → B₂ y → B₁ (Equivalence.from A₁⇔A₂ ⟨$⟩ y)) →
      Σ A₁ B₁ ⇔ Σ A₂ B₂
  ⇔ A₁⇔A₂ B-to B-from = Equiv.equivalence
    (Prod.map (Equivalence.to   A₁⇔A₂ ⟨$⟩_) B-to)
    (Prod.map (Equivalence.from A₁⇔A₂ ⟨$⟩_) B-from)

  ⇔-↠ : ∀ (A₁↠A₂ : A₁ ↠ A₂) →
        (∀ {x} → _⇔_ (B₁ x) (B₂ (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
        _⇔_ (Σ A₁ B₁) (Σ A₂ B₂)
  ⇔-↠ A₁↠A₂ B₁⇔B₂ = Equiv.equivalence
    (Prod.map (Surjection.to   A₁↠A₂ ⟨$⟩_) (Equivalence.to B₁⇔B₂ ⟨$⟩_))
    (Prod.map (Surjection.from A₁↠A₂ ⟨$⟩_)
       ((Equivalence.from B₁⇔B₂ ⟨$⟩_) ∘
        P.subst B₂ (P.sym $ Surjection.right-inverse-of A₁↠A₂ _)))

  -- See also Data.Product.Relation.Binary.Pointwise.Dependent.WithK.↣.

  ↣ : ∀ (A₁↔A₂ : A₁ ↔ A₂) →
      (∀ {x} → B₁ x ↣ B₂ (Inverse.to A₁↔A₂ ⟨$⟩ x)) →
      Σ A₁ B₁ ↣ Σ A₂ B₂
  ↣ A₁↔A₂ B₁↣B₂ = Inj.injection to to-injective
    where
    open P.≡-Reasoning

    A₁≃A₂ = ↔→≃ A₁↔A₂

    subst-application′ :
      let open _≃_ A₁≃A₂ in
      {x₁ x₂ : A₁} {y : B₁ (from (to x₁))}
      (g : ∀ x → B₁ (from (to x)) → B₂ (to x)) (eq : to x₁ ≡ to x₂) →
      P.subst B₂ eq (g x₁ y) ≡ g x₂ (P.subst B₁ (P.cong from eq) y)
    subst-application′ {x₁} {x₂} {y} g eq =
      P.subst B₂ eq (g x₁ y)                      ≡⟨ P.cong (P.subst B₂ eq) (P.sym (g′-lemma _ _)) ⟩
      P.subst B₂ eq (g′ (to x₁) y)                ≡⟨ P.subst-application B₁ g′ eq ⟩
      g′ (to x₂) (P.subst B₁ (P.cong from eq) y)  ≡⟨ g′-lemma _ _ ⟩
      g x₂ (P.subst B₁ (P.cong from eq) y)        ∎
      where
      open _≃_ A₁≃A₂

      g′ : ∀ x → B₁ (from x) → B₂ x
      g′ x =
        P.subst B₂ (right-inverse-of x) ∘
        g (from x) ∘
        P.subst B₁ (P.sym (P.cong from (right-inverse-of x)))

      g′-lemma : ∀ x y → g′ (to x) y ≡ g x y
      g′-lemma x y =
        P.subst B₂ (right-inverse-of (to x))
          (g (from (to x)) $
           P.subst B₁ (P.sym (P.cong from (right-inverse-of (to x)))) y)  ≡⟨ P.cong (λ p → P.subst B₂ p (g (from (to x))
                                                                                                           (P.subst B₁ (P.sym (P.cong from p)) y)))
                                                                               (P.sym (left-right x)) ⟩
        P.subst B₂ (P.cong to (left-inverse-of x))
          (g (from (to x)) $
           P.subst B₁
             (P.sym (P.cong from (P.cong to (left-inverse-of x))))
             y)                                                           ≡⟨ lemma _ ⟩

        g x y                                                             ∎
        where
        lemma :
          ∀ {x′} eq {y : B₁ (from (to x′))} →
          P.subst B₂ (P.cong to eq)
            (g (from (to x))
               (P.subst B₁ (P.sym (P.cong from (P.cong to eq))) y)) ≡
          g x′ y
        lemma P.refl = P.refl

    to = Prod.map (_≃_.to A₁≃A₂) (Injection.to B₁↣B₂ ⟨$⟩_)

    to-injective : Injective (P.→-to-⟶ {B = P.setoid _} to)
    to-injective {(x₁ , x₂)} {(y₁ , y₂)} =
      (Inverse.to Σ-≡,≡↔≡ ⟨$⟩_) ∘′

      Prod.map (_≃_.injective A₁≃A₂) (λ {eq₁} eq₂ →

        let lemma =

              Injection.to B₁↣B₂ ⟨$⟩
              P.subst B₁ (_≃_.injective A₁≃A₂ eq₁) x₂                     ≡⟨⟩

              Injection.to B₁↣B₂ ⟨$⟩
              P.subst B₁
                (P.trans (P.sym (_≃_.left-inverse-of A₁≃A₂ x₁))
                   (P.trans (P.cong (_≃_.from A₁≃A₂) eq₁)
                      (P.trans (_≃_.left-inverse-of A₁≃A₂ y₁)
                         P.refl)))
                x₂                                                        ≡⟨ P.cong (λ p → Injection.to B₁↣B₂ ⟨$⟩
                                                                                             P.subst B₁
                                                                                               (P.trans (P.sym (_≃_.left-inverse-of A₁≃A₂ _))
                                                                                                  (P.trans (P.cong (_≃_.from A₁≃A₂) eq₁) p))
                                                                                               x₂)
                                                                               (P.trans-reflʳ _) ⟩
              Injection.to B₁↣B₂ ⟨$⟩
              P.subst B₁
                (P.trans (P.sym (_≃_.left-inverse-of A₁≃A₂ x₁))
                   (P.trans (P.cong (_≃_.from A₁≃A₂) eq₁)
                      (_≃_.left-inverse-of A₁≃A₂ y₁)))
                x₂                                                        ≡⟨ P.cong (Injection.to B₁↣B₂ ⟨$⟩_)
                                                                               (P.sym (P.subst-subst (P.sym (_≃_.left-inverse-of A₁≃A₂ _)))) ⟩
              Injection.to B₁↣B₂ ⟨$⟩
              (P.subst B₁ (P.trans (P.cong (_≃_.from A₁≃A₂) eq₁)
                             (_≃_.left-inverse-of A₁≃A₂ y₁)) $
               P.subst B₁ (P.sym (_≃_.left-inverse-of A₁≃A₂ x₁)) x₂)      ≡⟨ P.cong (Injection.to B₁↣B₂ ⟨$⟩_)
                                                                               (P.sym (P.subst-subst (P.cong (_≃_.from A₁≃A₂) eq₁))) ⟩
              Injection.to B₁↣B₂ ⟨$⟩
              (P.subst B₁ (_≃_.left-inverse-of A₁≃A₂ y₁) $
               P.subst B₁ (P.cong (_≃_.from A₁≃A₂) eq₁) $
               P.subst B₁ (P.sym (_≃_.left-inverse-of A₁≃A₂ x₁)) x₂)      ≡⟨ P.sym (subst-application′
                                                                                      (λ x y → Injection.to B₁↣B₂ ⟨$⟩
                                                                                                 P.subst B₁ (_≃_.left-inverse-of A₁≃A₂ x) y)
                                                                                      eq₁) ⟩
              P.subst B₂ eq₁
                (Injection.to B₁↣B₂ ⟨$⟩
                 (P.subst B₁ (_≃_.left-inverse-of A₁≃A₂ x₁) $
                  P.subst B₁ (P.sym (_≃_.left-inverse-of A₁≃A₂ x₁)) x₂))  ≡⟨ P.cong (P.subst B₂ eq₁ ∘ (Injection.to B₁↣B₂ ⟨$⟩_))
                                                                               (P.subst-subst (P.sym (_≃_.left-inverse-of A₁≃A₂ _))) ⟩
              P.subst B₂ eq₁
                (Injection.to B₁↣B₂ ⟨$⟩
                 P.subst B₁
                   (P.trans (P.sym (_≃_.left-inverse-of A₁≃A₂ x₁))
                      (_≃_.left-inverse-of A₁≃A₂ x₁))
                   x₂)                                                    ≡⟨ P.cong (λ p → P.subst B₂ eq₁
                                                                                             (Injection.to B₁↣B₂ ⟨$⟩ P.subst B₁ p x₂))
                                                                               (P.trans-symˡ (_≃_.left-inverse-of A₁≃A₂ _)) ⟩
              P.subst B₂ eq₁
                (Injection.to B₁↣B₂ ⟨$⟩ P.subst B₁ P.refl x₂)             ≡⟨⟩

              P.subst B₂ eq₁ (Injection.to B₁↣B₂ ⟨$⟩ x₂)                  ≡⟨ eq₂ ⟩

              Injection.to B₁↣B₂ ⟨$⟩ y₂                                   ∎

        in

        P.subst B₁ (_≃_.injective A₁≃A₂ eq₁) x₂  ≡⟨ Injection.injective B₁↣B₂ lemma ⟩
        y₂                                       ∎) ∘

      (Inverse.from Σ-≡,≡↔≡ ⟨$⟩_)

  ↞ : (A₁↞A₂ : A₁ ↞ A₂) →
      (∀ {x} → B₁ (LeftInverse.from A₁↞A₂ ⟨$⟩ x) ↞ B₂ x) →
      Σ A₁ B₁ ↞ Σ A₂ B₂
  ↞ A₁↞A₂ B₁↞B₂ = record
    { to              = P.→-to-⟶ to
    ; from            = P.→-to-⟶ from
    ; left-inverse-of = left-inverse-of
    }
    where
    open P.≡-Reasoning

    from = Prod.map (LeftInverse.from A₁↞A₂ ⟨$⟩_)
                    (LeftInverse.from B₁↞B₂ ⟨$⟩_)

    to   = Prod.map
      (LeftInverse.to A₁↞A₂ ⟨$⟩_)
      (λ {x} y →
         LeftInverse.to B₁↞B₂ ⟨$⟩
           P.subst B₁ (P.sym (LeftInverse.left-inverse-of A₁↞A₂ x)) y)

    left-inverse-of : ∀ p → from (to p) ≡ p
    left-inverse-of (x , y) = Inverse.to Σ-≡,≡↔≡ ⟨$⟩
      ( LeftInverse.left-inverse-of A₁↞A₂ x
      , (P.subst B₁ (LeftInverse.left-inverse-of A₁↞A₂ x)
           (LeftInverse.from B₁↞B₂ ⟨$⟩ (LeftInverse.to B₁↞B₂ ⟨$⟩
              (P.subst B₁ (P.sym (LeftInverse.left-inverse-of A₁↞A₂ x))
                 y)))                                                    ≡⟨ P.cong (P.subst B₁ _) (LeftInverse.left-inverse-of B₁↞B₂ _) ⟩

         P.subst B₁ (LeftInverse.left-inverse-of A₁↞A₂ x)
           (P.subst B₁ (P.sym (LeftInverse.left-inverse-of A₁↞A₂ x))
              y)                                                         ≡⟨ P.subst-subst-sym (LeftInverse.left-inverse-of A₁↞A₂ x) ⟩

         y                                                               ∎)
      )

  ↠ : (A₁↠A₂ : A₁ ↠ A₂) →
      (∀ {x} → B₁ x ↠ B₂ (Surjection.to A₁↠A₂ ⟨$⟩ x)) →
      Σ A₁ B₁ ↠ Σ A₂ B₂
  ↠ A₁↠A₂ B₁↠B₂ = record
    { to         = P.→-to-⟶ to
    ; surjective = record
      { from             = P.→-to-⟶ from
      ; right-inverse-of = right-inverse-of
      }
    }
    where
    open P.≡-Reasoning

    to   = Prod.map (Surjection.to A₁↠A₂ ⟨$⟩_)
                    (Surjection.to B₁↠B₂ ⟨$⟩_)
    from = Prod.map
      (Surjection.from A₁↠A₂ ⟨$⟩_)
      (λ {x} y →
         Surjection.from B₁↠B₂ ⟨$⟩
           P.subst B₂ (P.sym (Surjection.right-inverse-of A₁↠A₂ x)) y)

    right-inverse-of : ∀ p → to (from p) ≡ p
    right-inverse-of (x , y) = Inverse.to Σ-≡,≡↔≡ ⟨$⟩
      ( Surjection.right-inverse-of A₁↠A₂ x
      , (P.subst B₂ (Surjection.right-inverse-of A₁↠A₂ x)
           (Surjection.to B₁↠B₂ ⟨$⟩ (Surjection.from B₁↠B₂ ⟨$⟩
              (P.subst B₂ (P.sym (Surjection.right-inverse-of A₁↠A₂ x))
                 y)))                                                    ≡⟨ P.cong (P.subst B₂ _) (Surjection.right-inverse-of B₁↠B₂ _) ⟩

         P.subst B₂ (Surjection.right-inverse-of A₁↠A₂ x)
           (P.subst B₂ (P.sym (Surjection.right-inverse-of A₁↠A₂ x))
              y)                                                         ≡⟨ P.subst-subst-sym (Surjection.right-inverse-of A₁↠A₂ x) ⟩

         y                                                               ∎)
      )

  ↔ : (A₁↔A₂ : A₁ ↔ A₂) →
      (∀ {x} → B₁ x ↔ B₂ (Inverse.to A₁↔A₂ ⟨$⟩ x)) →
      Σ A₁ B₁ ↔ Σ A₂ B₂
  ↔ A₁↔A₂ B₁↔B₂ = Inv.inverse
    (Surjection.to   surjection′ ⟨$⟩_)
    (Surjection.from surjection′ ⟨$⟩_)
    left-inverse-of
    (Surjection.right-inverse-of surjection′)
    where
    open P.≡-Reasoning

    A₁≃A₂ = ↔→≃ A₁↔A₂

    surjection′ : _↠_ (Σ A₁ B₁) (Σ A₂ B₂)
    surjection′ =
      ↠ (Inverse.surjection (_≃_.inverse A₁≃A₂))
        (Inverse.surjection B₁↔B₂)

    left-inverse-of :
      ∀ p → Surjection.from surjection′ ⟨$⟩
              (Surjection.to surjection′ ⟨$⟩ p) ≡ p
    left-inverse-of (x , y) = Inverse.to Σ-≡,≡↔≡ ⟨$⟩
      ( _≃_.left-inverse-of A₁≃A₂ x
      , (P.subst B₁ (_≃_.left-inverse-of A₁≃A₂ x)
           (Inverse.from B₁↔B₂ ⟨$⟩
              (P.subst B₂ (P.sym (_≃_.right-inverse-of A₁≃A₂
                                    (_≃_.to A₁≃A₂ x)))
                 (Inverse.to B₁↔B₂ ⟨$⟩ y)))                   ≡⟨ P.subst-application B₂ (λ _ → Inverse.from B₁↔B₂ ⟨$⟩_) _ ⟩

         Inverse.from B₁↔B₂ ⟨$⟩
           (P.subst B₂ (P.cong (_≃_.to A₁≃A₂)
                          (_≃_.left-inverse-of A₁≃A₂ x))
              (P.subst B₂ (P.sym (_≃_.right-inverse-of A₁≃A₂
                                    (_≃_.to A₁≃A₂ x)))
                 (Inverse.to B₁↔B₂ ⟨$⟩ y)))                   ≡⟨ P.cong (λ eq → Inverse.from B₁↔B₂ ⟨$⟩ P.subst B₂ eq
                                                                                  (P.subst B₂ (P.sym (_≃_.right-inverse-of A₁≃A₂ _)) _))
                                                                   (_≃_.left-right A₁≃A₂ _) ⟩
         Inverse.from B₁↔B₂ ⟨$⟩
           (P.subst B₂ (_≃_.right-inverse-of A₁≃A₂
                          (_≃_.to A₁≃A₂ x))
              (P.subst B₂ (P.sym (_≃_.right-inverse-of A₁≃A₂
                                    (_≃_.to A₁≃A₂ x)))
                 (Inverse.to B₁↔B₂ ⟨$⟩ y)))                   ≡⟨ P.cong (Inverse.from B₁↔B₂ ⟨$⟩_)
                                                                   (P.subst-subst-sym (_≃_.right-inverse-of A₁≃A₂ _)) ⟩

         Inverse.from B₁↔B₂ ⟨$⟩ (Inverse.to B₁↔B₂ ⟨$⟩ y)      ≡⟨ Inverse.left-inverse-of B₁↔B₂ _ ⟩

         y                                                    ∎)
      )

private

  swap-coercions : ∀ {k a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : A₁ → Set b₁} (B₂ : A₂ → Set b₂)
    (A₁↔A₂ : _↔_ A₁ A₂) →
    (∀ {x} → B₁ x ∼[ k ] B₂ (Inverse.to A₁↔A₂ ⟨$⟩ x)) →
    ∀ {x} → B₁ (Inverse.from A₁↔A₂ ⟨$⟩ x) ∼[ k ] B₂ x
  swap-coercions {k} {B₁ = B₁} B₂ A₁↔A₂ eq {x} =
    B₁ (Inverse.from A₁↔A₂ ⟨$⟩ x)
      ∼⟨ eq ⟩
    B₂ (Inverse.to A₁↔A₂ ⟨$⟩ (Inverse.from A₁↔A₂ ⟨$⟩ x))
      ↔⟨ Related.K-reflexive
         (P.cong B₂ $ Inverse.right-inverse-of A₁↔A₂ x) ⟩
    B₂ x
      ∎
    where open Related.EquationalReasoning

cong : ∀ {k a₁ a₂ b₁ b₂}
         {A₁ : Set a₁} {A₂ : Set a₂}
         {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
       (A₁↔A₂ : _↔_ A₁ A₂) →
       (∀ {x} → B₁ x ∼[ k ] B₂ (Inverse.to A₁↔A₂ ⟨$⟩ x)) →
       Σ A₁ B₁ ∼[ k ] Σ A₂ B₂
cong {Related.implication}                   =
  λ A₁↔A₂ → Prod.map (_⟨$⟩_ (Inverse.to A₁↔A₂))
cong {Related.reverse-implication} {B₂ = B₂} =
  λ A₁↔A₂ B₁←B₂ → lam (Prod.map (_⟨$⟩_ (Inverse.from A₁↔A₂))
    (app-← (swap-coercions B₂ A₁↔A₂ B₁←B₂)))
cong {Related.equivalence}                   = ⇔-↠ ∘ Inverse.surjection
cong {Related.injection}                     = ↣
cong {Related.reverse-injection}   {B₂ = B₂} =
  λ A₁↔A₂ B₁↢B₂ → lam (↣ (Inv.sym A₁↔A₂)
    (app-↢ (swap-coercions B₂ A₁↔A₂ B₁↢B₂)))
cong {Related.left-inverse}                  =
  λ A₁↔A₂ → ↞ (Inverse.left-inverse A₁↔A₂) ∘ swap-coercions _ A₁↔A₂
cong {Related.surjection}                    = ↠ ∘ Inverse.surjection
cong {Related.bijection}                     = ↔

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

Rel = Pointwise
{-# WARNING_ON_USAGE Rel
"Warning: Rel was deprecated in v0.15.
Please use Pointwise instead."
#-}

-- Version 0.15

REL = POINTWISE
{-# WARNING_ON_USAGE REL
"Warning: REL was deprecated in v0.18.
Please use POINTWISE instead."
#-}
