------------------------------------------------------------------------
-- The Agda standard library
--
-- Propertiers of any for containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Relation.Unary.Any.Properties where

open import Level
open import Algebra
open import Data.Product as Prod using (∃; _×_; ∃₂; _,_; proj₂)
open import Data.Product.Function.NonDependent.Propositional using (_×-cong_)
import Data.Product.Function.Dependent.Propositional as Σ
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function.Core
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (equivalence)
open import Function.HalfAdjointEquivalence using (_≃_; ↔→≃)
open import Function.Inverse as Inv using (_↔_; inverse; module Inverse)
open import Function.Related as Related using (Related; SK-sym)
open import Function.Related.TypeIsomorphisms
open import Relation.Unary using (Pred ; _∪_ ; _∩_)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_; refl)

open Related.EquationalReasoning hiding (_≡⟨_⟩_)
private
  module ×⊎ {k ℓ} = CommutativeSemiring (×-⊎-commutativeSemiring k ℓ)


open import Data.Container.Core
import Data.Container.Combinator as C
open import Data.Container.Combinator.Properties
open import Data.Container.Related
open import Data.Container.Relation.Unary.Any as Any using (◇; any)
open import Data.Container.Membership

module _ {s p} (C : Container s p) {x} {X : Set x} {ℓ} {P : Pred X ℓ} where

-- ◇ can be unwrapped to reveal the Σ type

  ↔Σ : ∀ {xs : ⟦ C ⟧ X} → ◇ C P xs ↔ ∃ λ p → P (proj₂ xs p)
  ↔Σ {xs} = inverse ◇.proof any (λ _ → P.refl) (λ _ → P.refl)

-- ◇ can be expressed using _∈_.

  ↔∈ : ∀ {xs : ⟦ C ⟧ X} → ◇ C P xs ↔ (∃ λ x → x ∈ xs × P x)
  ↔∈ {xs} = inverse to from (λ _ → P.refl) (to∘from) where

    to : ◇ C P xs → ∃ λ x → x ∈ xs × P x
    to (any (p , Px)) = (proj₂ xs p , (any (p , P.refl)) , Px)

    from : (∃ λ x → x ∈ xs × P x) → ◇ C P xs
    from (.(proj₂ xs p) , (any (p , refl)) , Px) = any (p , Px)

    to∘from : to ∘ from ≗ id
    to∘from (.(proj₂ xs p) , any (p , refl) , Px) = P.refl

module _ {s p} {C : Container s p} {x} {X : Set x}
         {ℓ₁ ℓ₂} {P₁ : Pred X ℓ₁} {P₂ : Pred X ℓ₂} where
-- ◇ is a congruence for bag and set equality and related preorders.

  cong : ∀ {k} {xs₁ xs₂ : ⟦ C ⟧ X} →
         (∀ x → Related k (P₁ x) (P₂ x)) → xs₁ ∼[ k ] xs₂ →
         Related k (◇ C P₁ xs₁) (◇ C P₂ xs₂)
  cong {k} {xs₁} {xs₂} P₁↔P₂ xs₁≈xs₂ =
    ◇ C P₁ xs₁               ↔⟨ ↔∈ C ⟩
    (∃ λ x → x ∈ xs₁ × P₁ x) ∼⟨ Σ.cong Inv.id (xs₁≈xs₂ ×-cong P₁↔P₂ _) ⟩
    (∃ λ x → x ∈ xs₂ × P₂ x) ↔⟨ SK-sym (↔∈ C) ⟩
    ◇ C P₂ xs₂               ∎

-- Nested occurrences of ◇ can sometimes be swapped.

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {x y} {X : Set x} {Y : Set y} {r} {P : REL X Y r} where

  swap : {xs : ⟦ C₁ ⟧ X} {ys : ⟦ C₂ ⟧ Y} →
         let ◈ : ∀ {s p} {C : Container s p} {x} {X : Set x} {ℓ} → ⟦ C ⟧ X → Pred X ℓ → Set (p ⊔ ℓ)
             ◈ = λ {_} {_} → flip (◇ _) in
         ◈ xs (◈ ys ∘ P) ↔ ◈ ys (◈ xs ∘ flip P)
  swap {xs} {ys} =
    ◇ _ (λ x → ◇ _ (P x) ys) xs                ↔⟨ ↔∈ C₁ ⟩
    (∃ λ x → x ∈ xs × ◇ _ (P x) ys)            ↔⟨ Σ.cong Inv.id $ Σ.cong Inv.id $ ↔∈ C₂ ⟩
    (∃ λ x → x ∈ xs × ∃ λ y → y ∈ ys × P x y)  ↔⟨ Σ.cong Inv.id (λ {x} → ∃∃↔∃∃ (λ _ y → y ∈ ys × P x y)) ⟩
    (∃₂ λ x y → x ∈ xs × y ∈ ys × P x y)       ↔⟨ ∃∃↔∃∃ (λ x y → x ∈ xs × y ∈ ys × P x y) ⟩
    (∃₂ λ y x → x ∈ xs × y ∈ ys × P x y)       ↔⟨ Σ.cong Inv.id (λ {y} → Σ.cong Inv.id (λ {x} →
      (x ∈ xs × y ∈ ys × P x y)                     ↔⟨ SK-sym Σ-assoc ⟩
      ((x ∈ xs × y ∈ ys) × P x y)                   ↔⟨ Σ.cong (×-comm _ _) Inv.id ⟩
      ((y ∈ ys × x ∈ xs) × P x y)                   ↔⟨ Σ-assoc ⟩
      (y ∈ ys × x ∈ xs × P x y)                     ∎)) ⟩
    (∃₂ λ y x → y ∈ ys × x ∈ xs × P x y)       ↔⟨ Σ.cong Inv.id (λ {y} → ∃∃↔∃∃ {B = y ∈ ys} (λ x _ → x ∈ xs × P x y)) ⟩
    (∃ λ y → y ∈ ys × ∃ λ x → x ∈ xs × P x y)  ↔⟨ Σ.cong Inv.id (Σ.cong Inv.id (SK-sym (↔∈ C₁))) ⟩
    (∃ λ y → y ∈ ys × ◇ _ (flip P y) xs)       ↔⟨ SK-sym (↔∈ C₂) ⟩
    ◇ _ (λ y → ◇ _ (flip P y) xs) ys           ∎

-- Nested occurrences of ◇ can sometimes be flattened.

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {x} {X : Set x} {ℓ} (P : Pred X ℓ) where

  flatten : ∀ (xss : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)) →
            ◇ C₁ (◇ C₂ P) xss ↔
            ◇ (C₁ C.∘ C₂) P (Inverse.from (Composition.correct C₁ C₂) ⟨$⟩ xss)
  flatten xss = inverse t f (λ _ → P.refl) (λ _ → P.refl) where

    ◇₁ = ◇ C₁; ◇₂ = ◇ C₂; ◇₁₂ = ◇ (C₁ C.∘ C₂)
    open Inverse

    t : ◇₁ (◇₂ P) xss → ◇₁₂ P (from (Composition.correct C₁ C₂) ⟨$⟩ xss)
    t (any (p₁ , (any (p₂ , p)))) = any (any (p₁ , p₂) , p)

    f : ◇₁₂ P (from (Composition.correct C₁ C₂) ⟨$⟩ xss) → ◇₁ (◇₂ P) xss
    f (any (any (p₁ , p₂) , p)) = any (p₁ , any (p₂ , p))

-- Sums commute with ◇ (for a fixed instance of a given container).

module _ {s p} {C : Container s p} {x} {X : Set x}
         {ℓ ℓ′} {P : Pred X ℓ} {Q : Pred X ℓ′} where

  ◇⊎↔⊎◇ : ∀ {xs : ⟦ C ⟧ X} → ◇ C (P ∪ Q) xs ↔ (◇ C P xs ⊎ ◇ C Q xs)
  ◇⊎↔⊎◇ {xs} = inverse to from from∘to to∘from
    where
    to : ◇ C (λ x → P x ⊎ Q x) xs → ◇ C P xs ⊎ ◇ C Q xs
    to (any (pos , inj₁ p)) = inj₁ (any (pos , p))
    to (any (pos , inj₂ q)) = inj₂ (any (pos , q))

    from : ◇ C P xs ⊎ ◇ C Q xs → ◇ C (λ x → P x ⊎ Q x) xs
    from = [ Any.map₂ inj₁ , Any.map₂ inj₂ ]

    from∘to : from ∘ to ≗ id
    from∘to (any (pos , inj₁ p)) = P.refl
    from∘to (any (pos , inj₂ q)) = P.refl

    to∘from : to ∘ from ≗ id
    to∘from = [ (λ _ → P.refl) , (λ _ → P.refl) ]

-- Products "commute" with ◇.

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {x y} {X : Set x} {Y : Set y} {ℓ ℓ′} {P : Pred X ℓ} {Q : Pred Y ℓ′} where

  ×◇↔◇◇× : ∀ {xs : ⟦ C₁ ⟧ X} {ys : ⟦ C₂ ⟧ Y} →
           ◇ C₁ (λ x → ◇ C₂ (λ y → P x × Q y) ys) xs ↔ (◇ C₁ P xs × ◇ C₂ Q ys)
  ×◇↔◇◇× {xs} {ys} = inverse to from (λ _ → P.refl) (λ _ → P.refl)
    where
    ◇₁ = ◇ C₁; ◇₂ = ◇ C₂

    to : ◇₁ (λ x → ◇₂ (λ y → P x × Q y) ys) xs → ◇₁ P xs × ◇₂ Q ys
    to (any (p₁ , any (p₂ , p , q))) = (any (p₁ , p) , any (p₂ , q))

    from : ◇₁ P xs × ◇₂ Q ys → ◇₁ (λ x → ◇₂ (λ y → P x × Q y) ys) xs
    from (any (p₁ , p) , any (p₂ , q)) = any (p₁ , any (p₂ , p , q))

-- map can be absorbed by the predicate.

module _ {s p} (C : Container s p) {x y} {X : Set x} {Y : Set y}
         {ℓ} (P : Pred Y ℓ) where

  map↔∘ : ∀ {xs : ⟦ C ⟧ X} (f : X → Y) → ◇ C P (map f xs) ↔ ◇ C (P ∘′ f) xs
  map↔∘ {xs} f =
   ◇ C P (map f xs)          ↔⟨ ↔Σ C ⟩
   ∃ (P ∘′ proj₂ (map f xs)) ↔⟨⟩
   ∃ (P ∘′ f ∘′ proj₂ xs)    ↔⟨ SK-sym (↔Σ C) ⟩
   ◇ C (P ∘′ f) xs           ∎

-- Membership in a mapped container can be expressed without reference
-- to map.

module _ {s p} (C : Container s p) {x y} {X : Set x} {Y : Set y}
         {ℓ} (P : Pred Y ℓ) where

  ∈map↔∈×≡ : ∀ {f : X → Y} {xs : ⟦ C ⟧ X} {y} →
             y ∈ map f xs ↔ (∃ λ x → x ∈ xs × y ≡ f x)
  ∈map↔∈×≡ {f = f} {xs} {y} =
    y ∈ map f xs               ↔⟨ map↔∘ C (y ≡_) f ⟩
    ◇ C (λ x → y ≡ f x) xs     ↔⟨ ↔∈ C ⟩
    ∃ (λ x → x ∈ xs × y ≡ f x) ∎

-- map is a congruence for bag and set equality and related preorders.

module _ {s p} (C : Container s p) {x y} {X : Set x} {Y : Set y}
         {ℓ} (P : Pred Y ℓ) where

  map-cong : ∀ {k} {f₁ f₂ : X → Y} {xs₁ xs₂ : ⟦ C ⟧ X} →
             f₁ ≗ f₂ → xs₁ ∼[ k ] xs₂ →
             map f₁ xs₁ ∼[ k ] map f₂ xs₂
  map-cong {f₁ = f₁} {f₂} {xs₁} {xs₂} f₁≗f₂ xs₁≈xs₂ {x} =
    x ∈ map f₁ xs₁           ↔⟨ map↔∘ C (_≡_ x) f₁ ⟩
    ◇ C (λ y → x ≡ f₁ y) xs₁ ∼⟨ cong (Related.↔⇒ ∘ helper) xs₁≈xs₂ ⟩
    ◇ C (λ y → x ≡ f₂ y) xs₂ ↔⟨ SK-sym (map↔∘ C (_≡_ x) f₂) ⟩
    x ∈ map f₂ xs₂           ∎
    where
    helper : ∀ y → (x ≡ f₁ y) ↔ (x ≡ f₂ y)
    helper y rewrite f₁≗f₂ y = Inv.id

-- Uses of linear morphisms can be removed.

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {x} {X : Set x} {ℓ} (P : Pred X ℓ) where

  remove-linear : ∀ {xs : ⟦ C₁ ⟧ X} (m : C₁ ⊸ C₂) → ◇ C₂ P (⟪ m ⟫⊸ xs) ↔ ◇ C₁ P xs
  remove-linear {xs} m = Inv.inverse t f f∘t t∘f
    where
    open _≃_
    open P.≡-Reasoning renaming (_∎ to _∎′)

    position⊸m : ∀ {s} → Position C₂ (shape⊸ m s) ≃ Position C₁ s
    position⊸m = ↔→≃ (position⊸ m)

    ◇₁ = ◇ C₁; ◇₂ = ◇ C₂

    t : ◇₂ P (⟪ m ⟫⊸ xs) → ◇₁ P xs
    t = Any.map₁ (_⊸_.morphism m)

    f : ◇₁ P xs → ◇₂ P (⟪ m ⟫⊸ xs)
    f (any (x , p)) =
      any $ from position⊸m x
          , P.subst (P ∘′ proj₂ xs) (P.sym (right-inverse-of position⊸m _)) p

    f∘t : f ∘ t ≗ id
    f∘t (any (p₂ , p)) = P.cong any $ Inverse.to Σ-≡,≡↔≡ ⟨$⟩
      ( left-inverse-of position⊸m p₂
      , (P.subst (P ∘ proj₂ xs ∘ to position⊸m)
           (left-inverse-of position⊸m p₂)
           (P.subst (P ∘ proj₂ xs)
              (P.sym (right-inverse-of position⊸m
                        (to position⊸m p₂)))
              p)                                                ≡⟨ P.subst-∘ (left-inverse-of position⊸m _) ⟩

         P.subst (P ∘ proj₂ xs)
           (P.cong (to position⊸m)
              (left-inverse-of position⊸m p₂))
           (P.subst (P ∘ proj₂ xs)
              (P.sym (right-inverse-of position⊸m
                        (to position⊸m p₂)))
              p)                                                ≡⟨ P.cong (λ eq → P.subst (P ∘ proj₂ xs) eq
                                                                                    (P.subst (P ∘ proj₂ xs)
                                                                                       (P.sym (right-inverse-of position⊸m _)) _))
                                                                     (_≃_.left-right position⊸m _) ⟩
         P.subst (P ∘ proj₂ xs)
           (right-inverse-of position⊸m
              (to position⊸m p₂))
           (P.subst (P ∘ proj₂ xs)
              (P.sym (right-inverse-of position⊸m
                        (to position⊸m p₂)))
              p)                                                ≡⟨ P.subst-subst (P.sym (right-inverse-of position⊸m _)) ⟩

         P.subst (P ∘ proj₂ xs)
           (P.trans
              (P.sym (right-inverse-of position⊸m
                        (to position⊸m p₂)))
              (right-inverse-of position⊸m
                 (to position⊸m p₂)))
           p                                                    ≡⟨ P.cong (λ eq → P.subst (P ∘ proj₂ xs) eq p)
                                                                     (P.trans-symˡ (right-inverse-of position⊸m _)) ⟩

         P.subst (P ∘ proj₂ xs) P.refl p                        ≡⟨⟩

        p                                                       ∎′)
      )

    t∘f : t ∘ f ≗ id
    t∘f (any (p₁ , p)) = P.cong any $ Inverse.to Σ-≡,≡↔≡ ⟨$⟩
      ( right-inverse-of position⊸m p₁
      , (P.subst (P ∘ proj₂ xs)
           (right-inverse-of position⊸m p₁)
           (P.subst (P ∘ proj₂ xs)
              (P.sym (right-inverse-of position⊸m p₁))
              p)                                                ≡⟨ P.subst-subst (P.sym (right-inverse-of position⊸m _)) ⟩

         P.subst (P ∘ proj₂ xs)
           (P.trans
              (P.sym (right-inverse-of position⊸m p₁))
              (right-inverse-of position⊸m p₁))
           p                                                    ≡⟨ P.cong (λ eq → P.subst (P ∘ proj₂ xs) eq p)
                                                                     (P.trans-symˡ (right-inverse-of position⊸m _)) ⟩
         P.subst (P ∘ proj₂ xs) P.refl p                        ≡⟨⟩

        p                                                       ∎′)
      )

-- Linear endomorphisms are identity functions if bag equality is used.

module _ {s p} {C : Container s p} {x} {X : Set x} where

  linear-identity : ∀ {xs : ⟦ C ⟧ X} (m : C ⊸ C) → ⟪ m ⟫⊸ xs ∼[ bag ] xs
  linear-identity {xs} m {x} =
    x ∈ ⟪ m ⟫⊸ xs  ↔⟨ remove-linear (_≡_ x) m ⟩
    x ∈        xs  ∎

-- If join can be expressed using a linear morphism (in a certain
-- way), then it can be absorbed by the predicate.

module _ {s₁ s₂ s₃ p₁ p₂ p₃}
         {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} {C₃ : Container s₃ p₃}
         {x} {X : Set x} {ℓ} (P : Pred X ℓ) where

  join↔◇ : (join′ : (C₁ C.∘ C₂) ⊸ C₃) (xss : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)) →
           let join : ∀ {X} → ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) → ⟦ C₃ ⟧ X
               join = λ {_} → ⟪ join′ ⟫⊸ ∘
                      _⟨$⟩_ (Inverse.from (Composition.correct C₁ C₂)) in
           ◇ C₃ P (join xss) ↔ ◇ C₁ (◇ C₂ P) xss
  join↔◇ join xss =
    ◇ C₃ P (⟪ join ⟫⊸ xss′) ↔⟨ remove-linear P join ⟩
    ◇ (C₁ C.∘ C₂) P xss′    ↔⟨ SK-sym $ flatten P xss ⟩
    ◇ C₁ (◇ C₂ P) xss       ∎
    where xss′ = Inverse.from (Composition.correct C₁ C₂) ⟨$⟩ xss
