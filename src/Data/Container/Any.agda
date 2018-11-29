------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to ◇
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Container.Any where

open import Level
open import Algebra
open import Data.Container as C
open import Data.Container.Combinator
  using (module Composition) renaming (_∘_ to _⟨∘⟩_)
open import Data.Product as Prod hiding (swap)
open import Data.Product.Relation.Pointwise.NonDependent
import Data.Product.Relation.Pointwise.Dependent as Σ
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Function
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

module _ {s p} (C : Container s p) {x} {X : Set x} {ℓ} {P : Pred X ℓ} where

-- ◇ can be expressed using _∈_.

  ↔∈ : ∀ {xs : ⟦ C ⟧ X} → ◇ P xs ↔ (∃ λ x → x ∈ xs × P x)
  ↔∈ {xs} = inverse to from (λ _ → P.refl) (to∘from)
    where

    to : ◇ P xs → ∃ λ x → x ∈ xs × P x
    to (p , Px) = (proj₂ xs p , (p , P.refl) , Px)

    from : (∃ λ x → x ∈ xs × P x) → ◇ P xs
    from (.(proj₂ xs p) , (p , refl) , Px) = (p , Px)

    to∘from : to ∘ from ≗ id
    to∘from (.(proj₂ xs p) , (p , refl) , Px) = P.refl

module _ {s p} {C : Container s p} {x} {X : Set x}
         {ℓ₁ ℓ₂} {P₁ : Pred X ℓ₁} {P₂ : Pred X ℓ₂} where
-- ◇ is a congruence for bag and set equality and related preorders.

  cong : ∀ {k} {xs₁ xs₂ : ⟦ C ⟧ X} →
         (∀ x → Related k (P₁ x) (P₂ x)) → xs₁ ∼[ k ] xs₂ →
         Related k (◇ P₁ xs₁) (◇ P₂ xs₂)
  cong {k} {xs₁} {xs₂} P₁↔P₂ xs₁≈xs₂ =
    ◇ P₁ xs₁                  ↔⟨ ↔∈ C ⟩
    (∃ λ x → x ∈ xs₁ × P₁ x)  ∼⟨ Σ.cong Inv.id (xs₁≈xs₂ ×-cong P₁↔P₂ _) ⟩
    (∃ λ x → x ∈ xs₂ × P₂ x)  ↔⟨ SK-sym (↔∈ C) ⟩
    ◇ P₂ xs₂                  ∎

-- Nested occurrences of ◇ can sometimes be swapped.

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {x y} {X : Set x} {Y : Set y} {r} {P : REL X Y r} where

  swap : {xs : ⟦ C₁ ⟧ X} {ys : ⟦ C₂ ⟧ Y} →
         let ◈ : ∀ {s p} {C : Container s p} {x} {X : Set x} {ℓ} → ⟦ C ⟧ X → Pred X ℓ → Set (p ⊔ ℓ)
             ◈ = λ {_} {_} → flip ◇ in
         ◈ xs (◈ ys ∘ P) ↔ ◈ ys (◈ xs ∘ flip P)
  swap {xs} {ys} =
    ◇ (λ x → ◇ (P x) ys) xs                    ↔⟨ ↔∈ C₁ ⟩
    (∃ λ x → x ∈ xs × ◇ (P x) ys)              ↔⟨ Σ.cong Inv.id $ Σ.cong Inv.id $ ↔∈ C₂ ⟩
    (∃ λ x → x ∈ xs × ∃ λ y → y ∈ ys × P x y)  ↔⟨ Σ.cong Inv.id (λ {x} → ∃∃↔∃∃ (λ _ y → y ∈ ys × P x y)) ⟩
    (∃₂ λ x y → x ∈ xs × y ∈ ys × P x y)       ↔⟨ ∃∃↔∃∃ (λ x y → x ∈ xs × y ∈ ys × P x y) ⟩
    (∃₂ λ y x → x ∈ xs × y ∈ ys × P x y)       ↔⟨ Σ.cong Inv.id (λ {y} → Σ.cong Inv.id (λ {x} →
      (x ∈ xs × y ∈ ys × P x y)                     ↔⟨ SK-sym Σ-assoc ⟩
      ((x ∈ xs × y ∈ ys) × P x y)                   ↔⟨ Σ.cong (×-comm _ _) Inv.id ⟩
      ((y ∈ ys × x ∈ xs) × P x y)                   ↔⟨ Σ-assoc ⟩
      (y ∈ ys × x ∈ xs × P x y)                     ∎)) ⟩
    (∃₂ λ y x → y ∈ ys × x ∈ xs × P x y)       ↔⟨ Σ.cong Inv.id (λ {y} → ∃∃↔∃∃ {B = y ∈ ys} (λ x _ → x ∈ xs × P x y)) ⟩
    (∃ λ y → y ∈ ys × ∃ λ x → x ∈ xs × P x y)  ↔⟨ Σ.cong Inv.id (Σ.cong Inv.id (SK-sym (↔∈ C₁))) ⟩
    (∃ λ y → y ∈ ys × ◇ (flip P y) xs)         ↔⟨ SK-sym (↔∈ C₂) ⟩
    ◇ (λ y → ◇ (flip P y) xs) ys               ∎

-- Nested occurrences of ◇ can sometimes be flattened.

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {x} {X : Set x} {ℓ} (P : Pred X ℓ) where

  flatten : ∀ (xss : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)) →
            ◇ (◇ P) xss ↔
            ◇ P (Inverse.from (Composition.correct C₁ C₂) ⟨$⟩ xss)
  flatten xss = inverse t f (λ _ → P.refl) (λ _ → P.refl)
    where
    open Inverse

    t : ◇ (◇ P) xss → ◇ P (from (Composition.correct C₁ C₂) ⟨$⟩ xss)
    t (p₁ , p₂ , p) = ((p₁ , p₂) , p)

    f : ◇ P (from (Composition.correct C₁ C₂) ⟨$⟩ xss) → ◇ (◇ P) xss
    f ((p₁ , p₂) , p) = (p₁ , p₂ , p)

-- Sums commute with ◇ (for a fixed instance of a given container).

module _ {s p} {C : Container s p} {x} {X : Set x}
         {ℓ ℓ′} {P : Pred X ℓ} {Q : Pred X ℓ′} where

  ◇⊎↔⊎◇ : ∀ {xs : ⟦ C ⟧ X} → ◇ (P ∪ Q) xs ↔ (◇ P xs ⊎ ◇ Q xs)
  ◇⊎↔⊎◇ {xs} = inverse to from from∘to to∘from
    where
    to : ◇ (λ x → P x ⊎ Q x) xs → ◇ P xs ⊎ ◇ Q xs
    to (pos , inj₁ p) = inj₁ (pos , p)
    to (pos , inj₂ q) = inj₂ (pos , q)

    from : ◇ P xs ⊎ ◇ Q xs → ◇ (λ x → P x ⊎ Q x) xs
    from = [ Prod.map id inj₁ , Prod.map id inj₂ ]

    from∘to : from ∘ to ≗ id
    from∘to (pos , inj₁ p) = P.refl
    from∘to (pos , inj₂ q) = P.refl

    to∘from : to ∘ from ≗ id
    to∘from = [ (λ _ → P.refl) , (λ _ → P.refl) ]

-- Products "commute" with ◇.

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {x y} {X : Set x} {Y : Set y} {ℓ ℓ′} {P : Pred X ℓ} {Q : Pred Y ℓ′} where

  ×◇↔◇◇× : ∀ {xs : ⟦ C₁ ⟧ X} {ys : ⟦ C₂ ⟧ Y} →
           ◇ (λ x → ◇ (λ y → P x × Q y) ys) xs ↔ (◇ P xs × ◇ Q ys)
  ×◇↔◇◇× {xs} {ys} = inverse to from (λ _ → P.refl) (λ _ → P.refl)
    where
    to : ◇ (λ x → ◇ (λ y → P x × Q y) ys) xs → ◇ P xs × ◇ Q ys
    to (p₁ , p₂ , p , q) = ((p₁ , p) , (p₂ , q))

    from : ◇ P xs × ◇ Q ys → ◇ (λ x → ◇ (λ y → P x × Q y) ys) xs
    from ((p₁ , p) , (p₂ , q)) = (p₁ , p₂ , p , q)

-- map can be absorbed by the predicate.

module _ {s p} (C : Container s p) {x y} {X : Set x} {Y : Set y}
         {ℓ} (P : Pred Y ℓ) where

  map↔∘ : ∀ {xs : ⟦ C ⟧ X} (f : X → Y) → ◇ P (C.map f xs) ↔ ◇ (P ∘ f) xs
  map↔∘ f = Inv.id

-- Membership in a mapped container can be expressed without reference
-- to map.

module _ {s p} (C : Container s p) {x y} {X : Set x} {Y : Set y}
         {ℓ} (P : Pred Y ℓ) where

  ∈map↔∈×≡ : ∀ {f : X → Y} {xs : ⟦ C ⟧ X} {y} →
             y ∈ C.map f xs ↔ (∃ λ x → x ∈ xs × y ≡ f x)
  ∈map↔∈×≡ {f = f} {xs} {y} =
    y ∈ C.map f xs              ↔⟨ map↔∘ C (y ≡_) f ⟩
    ◇ (λ x → y ≡ f x) xs        ↔⟨ ↔∈ C ⟩
    (∃ λ x → x ∈ xs × y ≡ f x)  ∎

-- map is a congruence for bag and set equality and related preorders.

module _ {s p} (C : Container s p) {x y} {X : Set x} {Y : Set y}
         {ℓ} (P : Pred Y ℓ) where

  map-cong : ∀ {k} {f₁ f₂ : X → Y} {xs₁ xs₂ : ⟦ C ⟧ X} →
             f₁ ≗ f₂ → xs₁ ∼[ k ] xs₂ →
             C.map f₁ xs₁ ∼[ k ] C.map f₂ xs₂
  map-cong {f₁ = f₁} {f₂} {xs₁} {xs₂} f₁≗f₂ xs₁≈xs₂ {x} =
    x ∈ C.map f₁ xs₁        ↔⟨ map↔∘ C (_≡_ x) f₁ ⟩
    ◇ (λ y → x ≡ f₁ y) xs₁  ∼⟨ cong {xs₁ = xs₁} {xs₂ = xs₂} (Related.↔⇒ ∘ helper) xs₁≈xs₂ ⟩
    ◇ (λ y → x ≡ f₂ y) xs₂  ↔⟨ SK-sym (map↔∘ C (_≡_ x) f₂) ⟩
    x ∈ C.map f₂ xs₂        ∎
    where
    helper : ∀ y → (x ≡ f₁ y) ↔ (x ≡ f₂ y)
    helper y = record
      { to         = P.→-to-⟶ (λ x≡f₁y → P.trans x≡f₁y (        f₁≗f₂ y))
      ; from       = P.→-to-⟶ (λ x≡f₂y → P.trans x≡f₂y (P.sym $ f₁≗f₂ y))
      ; inverse-of = record
        { left-inverse-of  = λ { P.refl → P.trans-symʳ (f₁≗f₂ y) }
        ; right-inverse-of = λ { P.refl → P.trans-symˡ (f₁≗f₂ y) }
        }
      }

-- Uses of linear morphisms can be removed.

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         {x} {X : Set x} {ℓ} (P : Pred X ℓ) where

  remove-linear : ∀ {xs : ⟦ C₁ ⟧ X} (m : C₁ ⊸ C₂) → ◇ P (⟪ m ⟫⊸ xs) ↔ ◇ P xs
  remove-linear {xs} m = Inv.inverse t f f∘t t∘f
    where
    open _≃_
    open P.≡-Reasoning renaming (_∎ to _∎′)

    position⊸m : ∀ {s} → Position C₂ (shape⊸ m s) ≃ Position C₁ s
    position⊸m = ↔→≃ (position⊸ m)

    t : ◇ P (⟪ m ⟫⊸ xs) → ◇ P xs
    t = Prod.map (to position⊸m) id

    f : ◇ P xs → ◇ P (⟪ m ⟫⊸ xs)
    f = Prod.map (from position⊸m)
                 (P.subst (P ∘ proj₂ xs)
                          (P.sym $ right-inverse-of position⊸m _))

    f∘t : f ∘ t ≗ id
    f∘t (p₂ , p) = Inverse.to Σ-≡,≡↔≡ ⟨$⟩
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
    t∘f (p₁ , p) = Inverse.to Σ-≡,≡↔≡ ⟨$⟩
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

-- Linear endomorphisms are identity functions if bag equality is
-- used.

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

  join↔◇ : (join′ : (C₁ ⟨∘⟩ C₂) ⊸ C₃) (xss : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)) →
           let join : ∀ {X} → ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) → ⟦ C₃ ⟧ X
               join = λ {_} → ⟪ join′ ⟫⊸ ∘
                      _⟨$⟩_ (Inverse.from (Composition.correct C₁ C₂)) in
           ◇ P (join xss) ↔ ◇ (◇ P) xss
  join↔◇ join xss =
    ◇ P (⟪ join ⟫⊸ xss′)  ↔⟨ remove-linear P join ⟩
    ◇ P            xss′   ↔⟨ SK-sym $ flatten P xss ⟩
    ◇ (◇ P) xss           ∎
    where xss′ = Inverse.from (Composition.correct C₁ C₂) ⟨$⟩ xss
