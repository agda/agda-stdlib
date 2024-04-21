------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for propositional equality
-- preserving functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Function.Dependent.Propositional where

open import Data.Product.Base as Product using (Σ; map; proj₂; _,_)
open import Data.Product.Properties using (Σ-≡,≡→≡; Σ-≡,≡↔≡; Σ-≡,≡←≡)
open import Level using (Level; 0ℓ)
open import Function.Related.Propositional
  using (_∼[_]_; module EquationalReasoning; K-reflexive;
         implication; reverseImplication; equivalence; injection;
         reverseInjection; leftInverse; surjection; bijection)
open import Function.Base using (_$_; _∘_; _∘′_)
open import Function.Properties.Inverse using (↔⇒↠; ↔⇒⟶; ↔⇒⟵; ↔-sym; ↔⇒↩)
open import Function.Properties.RightInverse using (↩⇒↪; ↪⇒↩)
open import Function.Properties.Inverse.HalfAdjointEquivalence
  using (↔⇒≃; _≃_; ≃⇒↔)
open import Function.Consequences.Propositional
  using (inverseʳ⇒injective; strictlySurjective⇒surjective)
open import Function.Definitions using (Inverseˡ; Inverseʳ; Injective; StrictlySurjective)
open import Function.Bundles
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties as ≡
  using (module ≡-Reasoning)

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
  Σ-⟶ I⟶J A⟶B = mk⟶ $ Product.map (to I⟶J) (to A⟶B)

------------------------------------------------------------------------
-- Equivalences

module _ where
  open Surjection

  Σ-⇔ : (I↠J : I ↠ J) →
         (∀ {i} → A i ⇔ B (to I↠J i)) →
         Σ I A ⇔ Σ J B
  Σ-⇔ {B = B} I↠J A⇔B = mk⇔
    (map (to  I↠J) (Equivalence.to A⇔B))
    (map (to⁻ I↠J) (Equivalence.from A⇔B ∘ ≡.subst B (≡.sym (proj₂ (surjective I↠J _) ≡.refl))))

  -- See also Data.Product.Relation.Binary.Pointwise.Dependent.WithK.↣.

------------------------------------------------------------------------
-- Injections

module _ where

  Σ-↣ : (I↔J : I ↔ J) →
         (∀ {i} → A i ↣ B (Inverse.to I↔J i)) →
         Σ I A ↣ Σ J B
  Σ-↣ {I = I} {J = J} {A = A} {B = B} I↔J A↣B = mk↣ to-injective
    where
    open ≡.≡-Reasoning

    I≃J = ↔⇒≃ I↔J

    subst-application′ :
      let open _≃_ I≃J in
      {x₁ x₂ : I} {y : A (from (to x₁))}
      (g : ∀ x → A (from (to x)) → B (to x))
      (eq : to x₁ ≡ to x₂) →
      ≡.subst B eq (g x₁ y) ≡ g x₂ (≡.subst A (≡.cong from eq) y)
    subst-application′ {x₁} {x₂} {y} g eq =
      ≡.subst B eq (g x₁ y)                      ≡⟨ ≡.cong (≡.subst B eq) (≡.sym (g′-lemma _ _)) ⟩
      ≡.subst B eq (g′ (to x₁) y)                ≡⟨ ≡.subst-application A g′ eq ⟩
      g′ (to x₂) (≡.subst A (≡.cong from eq) y)  ≡⟨ g′-lemma _ _ ⟩
      g x₂ (≡.subst A (≡.cong from eq) y)        ∎
      where
      open _≃_ I≃J

      g′ : ∀ x → A (from x) → B x
      g′ x =
        ≡.subst B (right-inverse-of x) ∘
        g (from x) ∘
        ≡.subst A (≡.sym (≡.cong from (right-inverse-of x)))

      g′-lemma : ∀ x y → g′ (to x) y ≡ g x y
      g′-lemma x y =
        ≡.subst B (right-inverse-of (to x))
          (g (from (to x)) $
           ≡.subst A (≡.sym (≡.cong from (right-inverse-of (to x)))) y)  ≡⟨ ≡.cong (λ p → ≡.subst B p (g (from (to x))
                                                                                                           (≡.subst A (≡.sym (≡.cong from p)) y)))
                                                                               (≡.sym (left-right x)) ⟩
        ≡.subst B (≡.cong to (left-inverse-of x))
          (g (from (to x)) $
           ≡.subst A
             (≡.sym (≡.cong from (≡.cong to (left-inverse-of x))))
             y)                                                           ≡⟨ lemma _ ⟩

        g x y                                                             ∎
        where
        lemma : ∀ {x′} eq {y : A (from (to x′))} →
                  ≡.subst B (≡.cong to eq)
                    (g (from (to x))
                      (≡.subst A (≡.sym (≡.cong from (≡.cong to eq))) y)) ≡
                  g x′ y
        lemma ≡.refl = ≡.refl

    open Injection

    to′ : Σ I A → Σ J B
    to′ = Product.map (_≃_.to I≃J) (to A↣B)

    to-injective : Injective _≡_ _≡_ to′
    to-injective {(x₁ , x₂)} {(y₁ , y₂)} =

      Σ-≡,≡→≡ ∘′

      map (_≃_.injective I≃J) (λ {eq₁} eq₂ → injective A↣B (
              to A↣B (≡.subst A (_≃_.injective I≃J eq₁) x₂)             ≡⟨⟩

              (let eq =
                      ≡.trans (≡.sym (_≃_.left-inverse-of I≃J x₁))
                        (≡.trans (≡.cong (_≃_.from I≃J) eq₁)
                          (≡.trans (_≃_.left-inverse-of I≃J y₁)
                            ≡.refl)) in
              to A↣B (≡.subst A eq x₂))                                   ≡⟨ ≡.cong (λ p → to A↣B
                                                                                             (≡.subst A
                                                                                               (≡.trans (≡.sym (_≃_.left-inverse-of I≃J _))
                                                                                                  (≡.trans (≡.cong (_≃_.from I≃J) eq₁) p))
                                                                                               x₂))
                                                                               (≡.trans-reflʳ _) ⟩

              (let eq = ≡.trans (≡.sym (_≃_.left-inverse-of I≃J x₁))
                          (≡.trans (≡.cong (_≃_.from I≃J) eq₁)
                            (_≃_.left-inverse-of I≃J y₁)) in
              to A↣B (≡.subst A eq x₂))                                  ≡⟨ ≡.cong (to A↣B)
                                                                               (≡.sym (≡.subst-subst (≡.sym (_≃_.left-inverse-of I≃J _)))) ⟩

              to A↣B ((≡.subst A (≡.trans (≡.cong (_≃_.from I≃J) eq₁)
                             (_≃_.left-inverse-of I≃J y₁)) $
               ≡.subst A (≡.sym (_≃_.left-inverse-of I≃J x₁)) x₂))      ≡⟨ ≡.cong (to A↣B)
                                                                               (≡.sym (≡.subst-subst (≡.cong (_≃_.from I≃J) eq₁))) ⟩
              to A↣B (
              (≡.subst A (_≃_.left-inverse-of I≃J y₁) $
               ≡.subst A (≡.cong (_≃_.from I≃J) eq₁) $
               ≡.subst A (≡.sym (_≃_.left-inverse-of I≃J x₁)) x₂))      ≡⟨ ≡.sym (subst-application′
                                                                                      (λ x y → to A↣B
                                                                                                 (≡.subst A (_≃_.left-inverse-of I≃J x) y))
                                                                                      eq₁) ⟩
              ≡.subst B eq₁ (to A↣B $
                 (≡.subst A (_≃_.left-inverse-of I≃J x₁) $
                  ≡.subst A (≡.sym (_≃_.left-inverse-of I≃J x₁)) x₂))  ≡⟨ ≡.cong (≡.subst B eq₁ ∘ to A↣B)
                                                                               (≡.subst-subst (≡.sym (_≃_.left-inverse-of I≃J _))) ⟩

              (let eq = ≡.trans (≡.sym (_≃_.left-inverse-of I≃J x₁))
                          (_≃_.left-inverse-of I≃J x₁) in
              ≡.subst B eq₁ (to A↣B (≡.subst A eq x₂)))                  ≡⟨ ≡.cong (λ p → ≡.subst B eq₁ (to A↣B (≡.subst A p x₂)))
                                                                              (≡.trans-symˡ (_≃_.left-inverse-of I≃J _)) ⟩
              ≡.subst B eq₁ (to A↣B (≡.subst A ≡.refl x₂))               ≡⟨⟩

              ≡.subst B eq₁ (to A↣B x₂)                                  ≡⟨ eq₂ ⟩

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
    backcast = ≡.subst B (≡.sym (to∘to⁻ I↠J _))

    to⁻′ : Σ J B → Σ I A
    to⁻′ = map (to⁻ I↠J) (Surjection.to⁻ A↠B ∘ backcast)

    strictlySurjective′ : StrictlySurjective _≡_ to′
    strictlySurjective′ (x , y) = to⁻′ (x , y) , Σ-≡,≡→≡
      ( to∘to⁻ I↠J x
      , (≡.subst B (to∘to⁻ I↠J x) (to A↠B (to⁻ A↠B (backcast y))) ≡⟨ ≡.cong (≡.subst B _) (to∘to⁻ A↠B _) ⟩
         ≡.subst B (to∘to⁻ I↠J x) (backcast y)                      ≡⟨ ≡.subst-subst-sym (to∘to⁻ I↠J x) ⟩
         y                                                          ∎)
      ) where open ≡.≡-Reasoning


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
    backcast = ≡.subst B (≡.sym (inverseˡ I↩J ≡.refl))

    from′ : Σ J B → Σ I A
    from′ = map (from I↩J) (from A↩B ∘ backcast)

    inv : Inverseˡ _≡_ _≡_ to′ from′
    inv {j , b} ≡.refl = Σ-≡,≡→≡ (strictlyInverseˡ I↩J j  , (
      begin
        ≡.subst B (inverseˡ I↩J ≡.refl) (to A↩B (from A↩B (backcast b))) ≡⟨ ≡.cong (≡.subst B _) (inverseˡ A↩B ≡.refl) ⟩
        ≡.subst B (inverseˡ I↩J ≡.refl) (backcast b)                       ≡⟨ ≡.subst-subst-sym (inverseˡ I↩J _) ⟩
        b                                                                  ∎)) where open ≡.≡-Reasoning

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
    open ≡.≡-Reasoning

    I≃J = ↔⇒≃ I↔J

    surjection′ : Σ I A ↠ Σ J B
    surjection′ = Σ-↠ (↔⇒↠ (≃⇒↔ I≃J)) (↔⇒↠ A↔B)

    left-inverse-of : ∀ p → Surjection.to⁻ surjection′ (Surjection.to surjection′ p) ≡ p
    left-inverse-of (x , y) = to Σ-≡,≡↔≡
      ( _≃_.left-inverse-of I≃J x
      , (≡.subst A (_≃_.left-inverse-of I≃J x)
           (from A↔B
              (≡.subst B (≡.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (to A↔B y)))                   ≡⟨ ≡.subst-application B (λ _ → from A↔B) _ ⟩

         from A↔B
           (≡.subst B (≡.cong (_≃_.to I≃J)
                          (_≃_.left-inverse-of I≃J x))
              (≡.subst B (≡.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (to A↔B y)))                   ≡⟨ ≡.cong (λ eq → from A↔B (≡.subst B eq
                                                                                  (≡.subst B (≡.sym (_≃_.right-inverse-of I≃J _)) _)))
                                                                   (_≃_.left-right I≃J _) ⟩
         from A↔B
           (≡.subst B (_≃_.right-inverse-of I≃J
                          (_≃_.to I≃J x))
              (≡.subst B (≡.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (to A↔B y)))                   ≡⟨ ≡.cong (from A↔B)
                                                                   (≡.subst-subst-sym (_≃_.right-inverse-of I≃J _)) ⟩

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
    B (to I↔J (from I↔J x)) ↔⟨ K-reflexive (≡.cong B $ strictlyInverseˡ I↔J x) ⟩
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
