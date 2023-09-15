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
open import Level using (Level)
open import Function.Related.TypeIsomorphisms
open import Function.Related.Propositional
open import Function.Base
open import Function.Properties.Inverse
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
-- Combinators for various function types

module _ where
  open Func

  Σ-⟶ : (I⟶J : I ⟶ J) →
         (∀ {i} → A i ⟶ B (to I⟶J i)) →
         Σ I A ⟶ Σ J B
  Σ-⟶ I⟶J A⟶B = mk⟶ $ Prod.map (to I⟶J) (to A⟶B)

 
module _ where
  open Equivalence

  Σ-⇔ : (I⇔J : I ⇔ J) →
         (∀ {i} → A i → B (to I⇔J i)) →
         (∀ {j} → B j → A (from I⇔J j)) →
         Σ I A ⇔ Σ J B
  Σ-⇔ I⇔J B-to B-from = mk⇔
    (Prod.map (to I⇔J) B-to)
    (Prod.map (from I⇔J) B-from)

module _ where
  open Surjection

  Σ-↠ : (I↠J : I ↠ J) →
         (∀ {i} → A i ⇔ B (to I↠J i)) →
         Σ I A ⇔ Σ J B
  Σ-↠ {B = B} I↠J A⇔B = mk⇔
    (map (to  I↠J) (Equivalence.to A⇔B))
    (map (to⁻ I↠J) (Equivalence.from A⇔B ∘ P.subst B (P.sym (proj₂ (surjective I↠J _) P.refl))))

  -- See also Data.Product.Relation.Binary.Pointwise.Dependent.WithK.↣.

module _ where
  open Injection hiding (to)

  ↣ : (I↔J : I ↔ J) →
      (∀ {i} → A i ↣ B (Inverse.to I↔J i)) →
      Σ I A ↣ Σ J B
  ↣ {I = I} {J = J} {A = A} {B = B} I↔J A↣B = mk↣ to-injective
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

    to′ : Σ I A → Σ J B
    to′ = Prod.map (_≃_.to I≃J) (Injection.to A↣B)

    to-injective : Injective _≡_ _≡_ to′
    to-injective {(x₁ , x₂)} {(y₁ , y₂)} =
    
      Σ-≡,≡→≡ ∘′

      map (_≃_.injective I≃J) (λ {eq₁} eq₂ → Injection.injective A↣B (
              Injection.to A↣B (P.subst A (_≃_.injective I≃J eq₁) x₂)  ≡⟨⟩

              Injection.to A↣B (P.subst A
                (P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                   (P.trans (P.cong (_≃_.from I≃J) eq₁)
                      (P.trans (_≃_.left-inverse-of I≃J y₁)
                         P.refl)))
                x₂)                                                        ≡⟨ P.cong (λ p → Injection.to A↣B $
                                                                                             P.subst A
                                                                                               (P.trans (P.sym (_≃_.left-inverse-of I≃J _))
                                                                                                  (P.trans (P.cong (_≃_.from I≃J) eq₁) p))
                                                                                               x₂)
                                                                               (P.trans-reflʳ _) ⟩
              Injection.to A↣B (
              P.subst A
                (P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                   (P.trans (P.cong (_≃_.from I≃J) eq₁)
                      (_≃_.left-inverse-of I≃J y₁)))
                x₂                                   )                     ≡⟨ P.cong (Injection.to A↣B $_)
                                                                               (P.sym (P.subst-subst (P.sym (_≃_.left-inverse-of I≃J _)))) ⟩
              Injection.to A↣B (
              (P.subst A (P.trans (P.cong (_≃_.from I≃J) eq₁)
                             (_≃_.left-inverse-of I≃J y₁)) $
               P.subst A (P.sym (_≃_.left-inverse-of I≃J x₁)) x₂))      ≡⟨ P.cong (Injection.to A↣B $_)
                                                                               (P.sym (P.subst-subst (P.cong (_≃_.from I≃J) eq₁))) ⟩
              Injection.to A↣B (
              (P.subst A (_≃_.left-inverse-of I≃J y₁) $
               P.subst A (P.cong (_≃_.from I≃J) eq₁) $
               P.subst A (P.sym (_≃_.left-inverse-of I≃J x₁)) x₂))      ≡⟨ P.sym (subst-application′
                                                                                      (λ x y → Injection.to A↣B $
                                                                                                 P.subst A (_≃_.left-inverse-of I≃J x) y)
                                                                                      eq₁) ⟩
              P.subst B eq₁
                (Injection.to A↣B $
                 (P.subst A (_≃_.left-inverse-of I≃J x₁) $
                  P.subst A (P.sym (_≃_.left-inverse-of I≃J x₁)) x₂))  ≡⟨ P.cong (P.subst B eq₁ ∘ (Injection.to A↣B $_))
                                                                               (P.subst-subst (P.sym (_≃_.left-inverse-of I≃J _))) ⟩
              P.subst B eq₁
                (Injection.to A↣B $
                 P.subst A
                   (P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                      (_≃_.left-inverse-of I≃J x₁))
                   x₂)                                                    ≡⟨ P.cong (λ p → P.subst B eq₁
                                                                                             (Injection.to A↣B $ P.subst A p x₂))
                                                                               (P.trans-symˡ (_≃_.left-inverse-of I≃J _)) ⟩
              P.subst B eq₁
                (Injection.to A↣B $ P.subst A P.refl x₂)             ≡⟨⟩

              P.subst B eq₁ (Injection.to A↣B $ x₂)                  ≡⟨ eq₂ ⟩

              Injection.to A↣B y₂                                   ∎

        )) ∘

      Σ-≡,≡←≡

module _ where
  open LeftInverse

  Σ-↩ : (I↩J : I ↩ J) →
         (∀ {i} → A i ↩ B (to I↩J i)) →
         Σ I A ↩ Σ J B
  Σ-↩ {I = I} {J = J} {A = A} {B = B} I↩J A↩B = mk↩ {to = to′ } {from = from′} inv
    where
    open P.≡-Reasoning

    to′ : Σ I A → Σ J B
    to′   = map (to I↩J) (to A↩B)
    from′ : Σ J B → Σ I A
    from′ = map (from I↩J) λ bx → from A↩B (P.subst B (P.sym (strictlyInverseˡ I↩J _)) bx)

    inv : {x : Σ J B} {y : Σ I A} → y ≡ from′ x → to′ y ≡ x
    inv {j , b} {.(from′ (j , b))} P.refl = Σ-≡,≡→≡ (strictlyInverseˡ I↩J j  , (
      begin
        P.subst B (inverseˡ I↩J P.refl)
          (to A↩B (from A↩B (P.subst B (P.sym (inverseˡ I↩J P.refl)) b))) ≡⟨ P.cong (P.subst B _) (inverseˡ A↩B P.refl) ⟩
        P.subst B (inverseˡ I↩J P.refl)
          (P.subst B (P.sym (inverseˡ I↩J P.refl)) b)                       ≡⟨ P.subst-subst-sym (inverseˡ I↩J _) ⟩
        b ∎))

module _ where
  open Surjection
  
  ↠ : (I↠J : I ↠ J) →
       (∀ {x} → A x ↠ B (to I↠J x)) →
       Σ I A ↠ Σ J B
  ↠ {I = I} {J = J} {A = A} {B = B} I↠J A↠B =
    mk↠ (strictlySurjective⇒surjective strictlySurjective′)
    where
    open P.≡-Reasoning

    to′ : Σ I A → Σ J B
    to′ = map (to I↠J) (to A↠B)

    to⁻′ : Σ J B → Σ I A
    to⁻′ = map
      (to⁻ I↠J)
      (λ {x} y →
         Surjection.to⁻ A↠B (
           P.subst B (P.sym (proj₂ (strictlySurjective I↠J x))) y))

    strictlySurjective′ : StrictlySurjective _≡_ to′
    strictlySurjective′ (x , y) = to⁻′ (x , y) , Σ-≡,≡→≡
      ( proj₂ (strictlySurjective I↠J x)
      , (P.subst B (to∘to⁻ I↠J x)
           (Surjection.to A↠B ((Surjection.to⁻ A↠B 
              ((P.subst B (P.sym (to∘to⁻ I↠J x))
                 y)))))                                                    ≡⟨ P.cong (P.subst B _) (to∘to⁻ A↠B _) ⟩

         P.subst B (to∘to⁻ I↠J x)
           (P.subst B (P.sym (to∘to⁻ I↠J x))
              y)                                                         ≡⟨ P.subst-subst-sym (to∘to⁻ I↠J x) ⟩

         y                                                               ∎)
      )
      

module _ where
  open Inverse


  ↔ : (I↔J : I ↔ J) →
      (∀ {x} → A x ↔ B (Inverse.to I↔J x)) →
      Σ I A ↔ Σ J B
  ↔ {I = I} {J = J} {A = A} {B = B} I↔J A↔B = mk↔′
    (Surjection.to  surjection′)
    (Surjection.to⁻ surjection′)
    (Surjection.to∘to⁻  surjection′)
    left-inverse-of
    where
    open P.≡-Reasoning

    I≃J = ↔⇒≃ I↔J

    surjection′ : _↠_ (Σ I A) (Σ J B)
    surjection′ = ↠ (↔⇒↠ (≃⇒↔ I≃J)) (↔⇒↠ A↔B)

    left-inverse-of :
      ∀ p → Surjection.to⁻ surjection′
              (Surjection.to surjection′ p) ≡ p
    left-inverse-of (x , y) = Inverse.to Σ-≡,≡↔≡
      ( _≃_.left-inverse-of I≃J x
      , (P.subst A (_≃_.left-inverse-of I≃J x)
           (Inverse.from A↔B
              (P.subst B (P.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (Inverse.to A↔B y)))                   ≡⟨ P.subst-application B (λ _ → Inverse.from A↔B) _ ⟩

         Inverse.from A↔B
           (P.subst B (P.cong (_≃_.to I≃J)
                          (_≃_.left-inverse-of I≃J x))
              (P.subst B (P.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (Inverse.to A↔B y)))                   ≡⟨ P.cong (λ eq → Inverse.from A↔B (P.subst B eq
                                                                                  (P.subst B (P.sym (_≃_.right-inverse-of I≃J _)) _)))
                                                                   (_≃_.left-right I≃J _) ⟩
         Inverse.from A↔B 
           (P.subst B (_≃_.right-inverse-of I≃J
                          (_≃_.to I≃J x))
              (P.subst B (P.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (Inverse.to A↔B y)))                   ≡⟨ P.cong (Inverse.from A↔B)
                                                                   (P.subst-subst-sym (_≃_.right-inverse-of I≃J _)) ⟩

         Inverse.from A↔B (Inverse.to A↔B y)      ≡⟨ Inverse.strictlyInverseʳ A↔B _ ⟩

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
   

cong : ∀ {k} (I↔J : _↔_ I J) →
       (∀ {x} → A x ∼[ k ] B (Inverse.to I↔J x)) →
       Σ I A ∼[ k ] Σ J B
cong {k = implication}                   = λ I↔J A⟶B → Σ-⟶ (↔⇒⟶ I↔J) A⟶B
cong {B = B} {k = reverseImplication}    = λ I↔J A⟵B → Σ-⟶ (↔⇒⟵ I↔J) (swap-coercions {k = reverseImplication} B I↔J A⟵B)
cong {k = equivalence}                   = Σ-↠ ∘ ↔⇒↠
cong {k = injection}                     = ↣
cong {B = B} {k = reverseInjection}      = λ I↔J A↢B → ↣ {!↔-sym {?} {?} {?} ?!} (swap-coercions {k = reverseInjection} B I↔J A↢B)
  -- lam (↣ (Inv.sym I↔J) (app-↢ (swap-coercions B I↔J A↢B)))
cong {B = B} {k = leftInverse}           = λ I↔J → {!Σ-↩!} ∘ swap-coercions B I↔J --↩ (Inverse.left-inverse I↔J)
cong {k = surjection}                    = ↠ ∘ ↔⇒↠
cong {k = bijection}                     = ↔
