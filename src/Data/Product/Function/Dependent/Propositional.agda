------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for propositional equality
-- preserving functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Function.Dependent.Propositional where

open import Data.Product.Base as Prod
open import Data.Product.Function.NonDependent.Setoid using ()
open import Data.Product.Relation.Binary.Pointwise.NonDependent using ()
open import Data.Product.Properties using (Σ-≡,≡→≡; Σ-≡,≡↔≡; Σ-≡,≡←≡)
open import Level using (Level; 0ℓ)
open import Function.Related.TypeIsomorphisms
open import Function.Related.Propositional
open import Function.Base
open import Function.Properties.Inverse
open import Function.Properties.RightInverse
open import Function.Properties.Inverse.HalfAdjointEquivalence
open import Function.Consequences.Propositional
  using (inverseʳ⇒injective; strictlySurjective⇒surjective)
open import Function.Definitions using (Inverseˡ; Inverseʳ; Injective; StrictlySurjective)
open import Function.Bundles
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private
  variable
    i a b c d : Level
    I J : Set i
    A B : I → Set a

------------------------------------------------------------------------
-- Functions

module _ where
  open Func

  Σ-⟶ : (I⟶J : I ⟶ J) →
         (∀ {i} → A i ⟶ B (to I⟶J i)) →
         Σ I A ⟶ Σ J B
  Σ-⟶ I⟶J A⟶B = mk⟶ $ Prod.map (to I⟶J) (to A⟶B)

------------------------------------------------------------------------
-- Equivalences

module _ where
  open Surjection

  Σ-⇔ : (I↠J : I ↠ J) →
         (∀ {i} → A i ⇔ B (to I↠J i)) →
         Σ I A ⇔ Σ J B
  Σ-⇔ {B = B} I↠J A⇔B = mk⇔
    (map (to  I↠J) (Equivalence.to A⇔B))
    (map (to⁻ I↠J) (Equivalence.from A⇔B ∘ P.subst B (P.sym (proj₂ (surjective I↠J _) P.refl))))

  -- See also Data.Product.Relation.Binary.Pointwise.Dependent.WithK.↣.

------------------------------------------------------------------------
-- Injections

module _ where

  Σ-↣ : (I↔J : I ↔ J) →
         (∀ {i} → A i ↣ B (Inverse.to I↔J i)) →
         Σ I A ↣ Σ J B
  Σ-↣ {I = I} {J = J} {A = A} {B = B} I↔J A↣B = mk↣ to-injective
    where
    open P.≡-Reasoning

    I≃J = ↔⇒≃ I↔J

    subst-application′ :
      let open _≃_ I≃J in
      {x₁ x₂ : I} {y : A (from (to x₁))}
      (g : ∀ x → A (from (to x)) → B (to x))
      (eq : to x₁ ≡ to x₂) →
      P.subst B eq (g x₁ y) ≡ g x₂ (P.subst A (P.cong from eq) y)
    subst-application′ {x₁} {x₂} {y} g eq =
      P.subst B eq (g x₁ y)                      ≡⟨ P.cong (P.subst B eq) (P.sym (g′-lemma _ _)) ⟩
      P.subst B eq (g′ (to x₁) y)                ≡⟨ P.subst-application A g′ eq ⟩
      g′ (to x₂) (P.subst A (P.cong from eq) y)  ≡⟨ g′-lemma _ _ ⟩
      g x₂ (P.subst A (P.cong from eq) y)        ∎
      where
      open _≃_ I≃J

      g′ : ∀ x → A (from x) → B x
      g′ x =
        P.subst B (right-inverse-of x) ∘
        g (from x) ∘
        P.subst A (P.sym (P.cong from (right-inverse-of x)))

      g′-lemma : ∀ x y → g′ (to x) y ≡ g x y
      g′-lemma x y =
        P.subst B (right-inverse-of (to x))
          (g (from (to x)) $
           P.subst A (P.sym (P.cong from (right-inverse-of (to x)))) y)  ≡⟨ P.cong (λ p → P.subst B p (g (from (to x))
                                                                                                           (P.subst A (P.sym (P.cong from p)) y)))
                                                                               (P.sym (left-right x)) ⟩
        P.subst B (P.cong to (left-inverse-of x))
          (g (from (to x)) $
           P.subst A
             (P.sym (P.cong from (P.cong to (left-inverse-of x))))
             y)                                                           ≡⟨ lemma _ ⟩

        g x y                                                             ∎
        where
        lemma : ∀ {x′} eq {y : A (from (to x′))} →
                  P.subst B (P.cong to eq)
                    (g (from (to x))
                      (P.subst A (P.sym (P.cong from (P.cong to eq))) y)) ≡
                  g x′ y
        lemma P.refl = P.refl

    open Injection

    to′ : Σ I A → Σ J B
    to′ = Prod.map (_≃_.to I≃J) (to A↣B)

    to-injective : Injective _≡_ _≡_ to′
    to-injective {(x₁ , x₂)} {(y₁ , y₂)} =

      Σ-≡,≡→≡ ∘′

      map (_≃_.injective I≃J) (λ {eq₁} eq₂ → injective A↣B (
              to A↣B (P.subst A (_≃_.injective I≃J eq₁) x₂)             ≡⟨⟩

              (let eq =
                      P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                        (P.trans (P.cong (_≃_.from I≃J) eq₁)
                          (P.trans (_≃_.left-inverse-of I≃J y₁)
                            P.refl)) in
              to A↣B (P.subst A eq x₂))                                   ≡⟨ P.cong (λ p → to A↣B
                                                                                             (P.subst A
                                                                                               (P.trans (P.sym (_≃_.left-inverse-of I≃J _))
                                                                                                  (P.trans (P.cong (_≃_.from I≃J) eq₁) p))
                                                                                               x₂))
                                                                               (P.trans-reflʳ _) ⟩

              (let eq = P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                          (P.trans (P.cong (_≃_.from I≃J) eq₁)
                            (_≃_.left-inverse-of I≃J y₁)) in
              to A↣B (P.subst A eq x₂))                                  ≡⟨ P.cong (to A↣B)
                                                                               (P.sym (P.subst-subst (P.sym (_≃_.left-inverse-of I≃J _)))) ⟩

              to A↣B ((P.subst A (P.trans (P.cong (_≃_.from I≃J) eq₁)
                             (_≃_.left-inverse-of I≃J y₁)) $
               P.subst A (P.sym (_≃_.left-inverse-of I≃J x₁)) x₂))      ≡⟨ P.cong (to A↣B)
                                                                               (P.sym (P.subst-subst (P.cong (_≃_.from I≃J) eq₁))) ⟩
              to A↣B (
              (P.subst A (_≃_.left-inverse-of I≃J y₁) $
               P.subst A (P.cong (_≃_.from I≃J) eq₁) $
               P.subst A (P.sym (_≃_.left-inverse-of I≃J x₁)) x₂))      ≡⟨ P.sym (subst-application′
                                                                                      (λ x y → to A↣B
                                                                                                 (P.subst A (_≃_.left-inverse-of I≃J x) y))
                                                                                      eq₁) ⟩
              P.subst B eq₁ (to A↣B $
                 (P.subst A (_≃_.left-inverse-of I≃J x₁) $
                  P.subst A (P.sym (_≃_.left-inverse-of I≃J x₁)) x₂))  ≡⟨ P.cong (P.subst B eq₁ ∘ to A↣B)
                                                                               (P.subst-subst (P.sym (_≃_.left-inverse-of I≃J _))) ⟩

              (let eq = P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                          (_≃_.left-inverse-of I≃J x₁) in
              P.subst B eq₁ (to A↣B (P.subst A eq x₂)))                  ≡⟨ P.cong (λ p → P.subst B eq₁ (to A↣B (P.subst A p x₂)))
                                                                              (P.trans-symˡ (_≃_.left-inverse-of I≃J _)) ⟩
              P.subst B eq₁ (to A↣B (P.subst A P.refl x₂))               ≡⟨⟩

              P.subst B eq₁ (to A↣B x₂)                                  ≡⟨ eq₂ ⟩

              to A↣B y₂                                                  ∎

        )) ∘

      Σ-≡,≡←≡

------------------------------------------------------------------------
-- Surjections

module _ where
  open Surjection

  Σ-↠ : (I↠J : I ↠ J) →
       (∀ {x} → A x ↠ B (to I↠J x)) →
       Σ I A ↠ Σ J B
  Σ-↠ {I = I} {J = J} {A = A} {B = B} I↠J A↠B =
    mk↠ₛ strictlySurjective′
    where
    to′ : Σ I A → Σ J B
    to′ = map (to I↠J) (to A↠B)

    backcast : ∀ {i} → B i → B (to I↠J (to⁻ I↠J i))
    backcast = P.subst B (P.sym (to∘to⁻ I↠J _))

    to⁻′ : Σ J B → Σ I A
    to⁻′ = map (to⁻ I↠J) (Surjection.to⁻ A↠B ∘ backcast)

    strictlySurjective′ : StrictlySurjective _≡_ to′
    strictlySurjective′ (x , y) = to⁻′ (x , y) , Σ-≡,≡→≡
      ( to∘to⁻ I↠J x
      , (P.subst B (to∘to⁻ I↠J x) (to A↠B (to⁻ A↠B (backcast y))) ≡⟨ P.cong (P.subst B _) (to∘to⁻ A↠B _) ⟩
         P.subst B (to∘to⁻ I↠J x) (backcast y)                      ≡⟨ P.subst-subst-sym (to∘to⁻ I↠J x) ⟩
         y                                                          ∎)
      ) where open P.≡-Reasoning


------------------------------------------------------------------------
-- Left inverses

module _ where
  open LeftInverse

  Σ-↩ : (I↩J : I ↩ J) →
         (∀ {i} → A i ↩ B (to I↩J i)) →
         Σ I A ↩ Σ J B
  Σ-↩ {I = I} {J = J} {A = A} {B = B} I↩J A↩B = mk↩ {to = to′ } {from = from′} inv
    where
    to′ : Σ I A → Σ J B
    to′ = map (to I↩J) (to A↩B)

    backcast : ∀ {j} → B j → B (to I↩J (from I↩J j))
    backcast = P.subst B (P.sym (inverseˡ I↩J P.refl))

    from′ : Σ J B → Σ I A
    from′ = map (from I↩J) (from A↩B ∘ backcast)

    inv : Inverseˡ _≡_ _≡_ to′ from′
    inv {j , b} P.refl = Σ-≡,≡→≡ (strictlyInverseˡ I↩J j  , (
      begin
        P.subst B (inverseˡ I↩J P.refl) (to A↩B (from A↩B (backcast b))) ≡⟨ P.cong (P.subst B _) (inverseˡ A↩B P.refl) ⟩
        P.subst B (inverseˡ I↩J P.refl) (backcast b)                       ≡⟨ P.subst-subst-sym (inverseˡ I↩J _) ⟩
        b                                                                  ∎)) where open P.≡-Reasoning

------------------------------------------------------------------------
-- Right inverses

------------------------------------------------------------------------
-- Inverses

module _ where
  open Inverse

  Σ-↔ : (I↔J : I ↔ J) →
      (∀ {x} → A x ↔ B (to I↔J x)) →
      Σ I A ↔ Σ J B
  Σ-↔ {I = I} {J = J} {A = A} {B = B} I↔J A↔B = mk↔ₛ′
    (Surjection.to surjection′)
    (Surjection.to⁻ surjection′)
    (Surjection.to∘to⁻ surjection′)
    left-inverse-of
    where
    open P.≡-Reasoning

    I≃J = ↔⇒≃ I↔J

    surjection′ : Σ I A ↠ Σ J B
    surjection′ = Σ-↠ (↔⇒↠ (≃⇒↔ I≃J)) (↔⇒↠ A↔B)

    left-inverse-of : ∀ p → Surjection.to⁻ surjection′ (Surjection.to surjection′ p) ≡ p
    left-inverse-of (x , y) = to Σ-≡,≡↔≡
      ( _≃_.left-inverse-of I≃J x
      , (P.subst A (_≃_.left-inverse-of I≃J x)
           (from A↔B
              (P.subst B (P.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (to A↔B y)))                   ≡⟨ P.subst-application B (λ _ → from A↔B) _ ⟩

         from A↔B
           (P.subst B (P.cong (_≃_.to I≃J)
                          (_≃_.left-inverse-of I≃J x))
              (P.subst B (P.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (to A↔B y)))                   ≡⟨ P.cong (λ eq → from A↔B (P.subst B eq
                                                                                  (P.subst B (P.sym (_≃_.right-inverse-of I≃J _)) _)))
                                                                   (_≃_.left-right I≃J _) ⟩
         from A↔B
           (P.subst B (_≃_.right-inverse-of I≃J
                          (_≃_.to I≃J x))
              (P.subst B (P.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (to A↔B y)))                   ≡⟨ P.cong (from A↔B)
                                                                   (P.subst-subst-sym (_≃_.right-inverse-of I≃J _)) ⟩

         from A↔B (to A↔B y)      ≡⟨ Inverse.strictlyInverseʳ A↔B _ ⟩

         y                                                    ∎)
      )


private module _ where
  open Inverse

  swap-coercions : ∀ {k} (B : J → Set b)
    (I↔J : _↔_ I J) →
    (∀ {x} → A x ∼[ k ] B (to I↔J x)) →
    ∀ {x} → A (from I↔J x) ∼[ k ] B x
  swap-coercions {A = A} B I↔J eq {x} =
    A (from I↔J x)           ∼⟨ eq ⟩
    B (to I↔J (from I↔J x)) ↔⟨ K-reflexive (P.cong B $ strictlyInverseˡ I↔J x) ⟩
    B x                       ∎
    where open EquationalReasoning


cong : ∀ {k} (I↔J : I ↔ J) →
       (∀ {x} → A x ∼[ k ] B (Inverse.to I↔J x)) →
       Σ I A ∼[ k ] Σ J B
cong {k = implication}                I↔J A⟶B = Σ-⟶ (↔⇒⟶ I↔J) A⟶B
cong {B = B} {k = reverseImplication} I↔J A⟵B = Σ-⟶ (↔⇒⟵ I↔J) (swap-coercions {k = reverseImplication} B I↔J A⟵B)
cong {k = equivalence}                I↔J A⇔B = Σ-⇔ (↔⇒↠ I↔J) A⇔B
cong {k = injection}                  I↔J A↣B = Σ-↣ I↔J A↣B
cong {B = B} {k = reverseInjection}   I↔J A↢B = Σ-↣ (↔-sym I↔J) (swap-coercions {k = reverseInjection} B I↔J A↢B)
cong {B = B} {k = leftInverse}        I↔J A↩B = ↩⇒↪ (Σ-↩ (↔⇒↩ (↔-sym I↔J)) (↪⇒↩ (swap-coercions {k = leftInverse} B I↔J A↩B)))
cong {k = surjection}                 I↔J A↠B = Σ-↠ (↔⇒↠ I↔J) A↠B
cong {k = bijection}                  I↔J A↔B = Σ-↔ I↔J A↔B
