------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for propositional equality
-- preserving functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Function.Dependent.Propositional where

open import Data.Product
open import Data.Product.Function.NonDependent.Setoid
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary
open import Function.Equality using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Eq using (_⇔_; module Equivalence)
open import Function.Injection as Inj using (_↣_; module Injection)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (_↞_; _LeftInverseOf_; module LeftInverse)
open import Function.Related
open import Function.Surjection as Surj using (_↠_; module Surjection)

------------------------------------------------------------------------
-- Combinators for various function types

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
