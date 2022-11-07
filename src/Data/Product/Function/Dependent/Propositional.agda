------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for propositional equality
-- preserving functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Function.Dependent.Propositional where

open import Data.Product as Prod
open import Data.Product.Function.NonDependent.Setoid using ()
open import Data.Product.Relation.Binary.Pointwise.NonDependent using ()
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Level using (Level)
open import Function.Base
open import Function.Bundles
-- open import Function.Related
-- open import Function.Related.TypeIsomorphisms
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private
  variable
    i a b c d : Level
    I J : Set i
    A B : I → Set a
    
------------------------------------------------------------------------
-- Combinators for various function types

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
    (map (to⁻ I↠J) (Equivalence.from A⇔B ∘ P.subst B (P.sym $ proj₂ (surjective I↠J _))))

  -- See also Data.Product.Relation.Binary.Pointwise.Dependent.WithK.↣.
{-
module _ where
  open Injection
  
  Σ-↣ : ∀ (I↔J : I ↔ J) →
      (∀ {x} → A x ↣ B (Inverse.to I↔J x)) →
      Σ I A ↣ Σ J B
  Σ-↣ I↔J A↣B = Inj.injection to to-injective
    where
    open P.≡-Reasoning

    I≃J = ↔→≃ I↔J

    subst-application′ :
      let open _≃_ I≃J in
      {x₁ x₂ : I} {y : A (from (to x₁))}
      (g : ∀ x → A (from (to x)) → B (to x)) (eq : to x₁ ≡ to x₂) →
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
        lemma :
          ∀ {x′} eq {y : A (from (to x′))} →
          P.subst B (P.cong to eq)
            (g (from (to x))
               (P.subst A (P.sym (P.cong from (P.cong to eq))) y)) ≡
          g x′ y
        lemma P.refl = P.refl

    to = map (_≃_.to I≃J) (Injection.to A↣B ⟨$⟩_)

    to-injective : Injective (P.→-to-⟶ {B = P.setoid _} to)
    to-injective {(x₁ , x₂)} {(y₁ , y₂)} =
      Σ-≡,≡→≡ ∘′

      map (_≃_.injective I≃J) (λ {eq₁} eq₂ →

        let lemma =

              Injection.to A↣B ⟨$⟩
              P.subst A (_≃_.injective I≃J eq₁) x₂                     ≡⟨⟩

              Injection.to A↣B ⟨$⟩
              P.subst A
                (P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                   (P.trans (P.cong (_≃_.from I≃J) eq₁)
                      (P.trans (_≃_.left-inverse-of I≃J y₁)
                         P.refl)))
                x₂                                                        ≡⟨ P.cong (λ p → Injection.to A↣B ⟨$⟩
                                                                                             P.subst A
                                                                                               (P.trans (P.sym (_≃_.left-inverse-of I≃J _))
                                                                                                  (P.trans (P.cong (_≃_.from I≃J) eq₁) p))
                                                                                               x₂)
                                                                               (P.trans-reflʳ _) ⟩
              Injection.to A↣B ⟨$⟩
              P.subst A
                (P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                   (P.trans (P.cong (_≃_.from I≃J) eq₁)
                      (_≃_.left-inverse-of I≃J y₁)))
                x₂                                                        ≡⟨ P.cong (Injection.to A↣B ⟨$⟩_)
                                                                               (P.sym (P.subst-subst (P.sym (_≃_.left-inverse-of I≃J _)))) ⟩
              Injection.to A↣B ⟨$⟩
              (P.subst A (P.trans (P.cong (_≃_.from I≃J) eq₁)
                             (_≃_.left-inverse-of I≃J y₁)) $
               P.subst A (P.sym (_≃_.left-inverse-of I≃J x₁)) x₂)      ≡⟨ P.cong (Injection.to A↣B ⟨$⟩_)
                                                                               (P.sym (P.subst-subst (P.cong (_≃_.from I≃J) eq₁))) ⟩
              Injection.to A↣B ⟨$⟩
              (P.subst A (_≃_.left-inverse-of I≃J y₁) $
               P.subst A (P.cong (_≃_.from I≃J) eq₁) $
               P.subst A (P.sym (_≃_.left-inverse-of I≃J x₁)) x₂)      ≡⟨ P.sym (subst-application′
                                                                                      (λ x y → Injection.to A↣B ⟨$⟩
                                                                                                 P.subst A (_≃_.left-inverse-of I≃J x) y)
                                                                                      eq₁) ⟩
              P.subst B eq₁
                (Injection.to A↣B ⟨$⟩
                 (P.subst A (_≃_.left-inverse-of I≃J x₁) $
                  P.subst A (P.sym (_≃_.left-inverse-of I≃J x₁)) x₂))  ≡⟨ P.cong (P.subst B eq₁ ∘ (Injection.to A↣B ⟨$⟩_))
                                                                               (P.subst-subst (P.sym (_≃_.left-inverse-of I≃J _))) ⟩
              P.subst B eq₁
                (Injection.to A↣B ⟨$⟩
                 P.subst A
                   (P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                      (_≃_.left-inverse-of I≃J x₁))
                   x₂)                                                    ≡⟨ P.cong (λ p → P.subst B eq₁
                                                                                             (Injection.to A↣B ⟨$⟩ P.subst A p x₂))
                                                                               (P.trans-symˡ (_≃_.left-inverse-of I≃J _)) ⟩
              P.subst B eq₁
                (Injection.to A↣B ⟨$⟩ P.subst A P.refl x₂)             ≡⟨⟩

              P.subst B eq₁ (Injection.to A↣B ⟨$⟩ x₂)                  ≡⟨ eq₂ ⟩

              Injection.to A↣B ⟨$⟩ y₂                                   ∎

        in

        P.subst A (_≃_.injective I≃J eq₁) x₂  ≡⟨ Injection.injective A↣B lemma ⟩
        y₂                                       ∎) ∘

      Σ-≡,≡←≡
-}

module _ where
  open LeftInverse
  
  Σ-↩ : (I↩J : I ↩ J) →
      (∀ {j} → A (LeftInverse.from I↩J j) ↩ B j) →
      Σ I A ↩ Σ J B
  Σ-↩ {A = A} I↩J A↩B = mk↩ {to = to′} {from = from′} inverseˡ′
    where
    open P.≡-Reasoning

    to′   = map (to I↩J)
      (λ {x} y → to A↩B ?) --(P.subst A (P.sym (inverseˡ I↩J x)) y))
    
    from′ = map (from I↩J) (from A↩B)

{-
  
-}
    inverseˡ′ : ∀ p → from′ (to′ p) ≡ p
    inverseˡ′ (x , y) = ?
{-
Σ-≡,≡→≡
      ( LeftInverse.inverseˡ I↩J x
      , (P.subst A (LeftInverse.inverseˡ I↩J x)
           (LeftInverse.from A↩B (LeftInverse.to A↩B
              (P.subst A (P.sym (LeftInverse.inverseˡ I↩J x))
                 y)))                                                    ≡⟨ P.cong (P.subst A _) (LeftInverse.inverseˡ A↩B _) ⟩

         P.subst A (LeftInverse.inverseˡ I↩J x)
           (P.subst A (P.sym (LeftInverse.inverseˡ I↩J x))
              y)                                                         ≡⟨ P.subst-subst-sym (LeftInverse.inverseˡ I↩J x) ⟩

         y                                                               ∎)
      )
-}
{-
  ↠ : (I↠J : I ↠ J) →
      (∀ {x} → A x ↠ B (Surjection.to I↠J ⟨$⟩ x)) →
      Σ I A ↠ Σ J B
  ↠ I↠J A↠B = record
    { to         = P.→-to-⟶ to
    ; surjective = record
      { from             = P.→-to-⟶ from
      ; right-inverse-of = right-inverse-of
      }
    }
    where
    open P.≡-Reasoning

    to   = map (Surjection.to I↠J ⟨$⟩_)
                    (Surjection.to A↠B ⟨$⟩_)
    from = map
      (Surjection.from I↠J ⟨$⟩_)
      (λ {x} y →
         Surjection.from A↠B ⟨$⟩
           P.subst B (P.sym (Surjection.right-inverse-of I↠J x)) y)

    right-inverse-of : ∀ p → to (from p) ≡ p
    right-inverse-of (x , y) = Σ-≡,≡→≡
      ( Surjection.right-inverse-of I↠J x
      , (P.subst B (Surjection.right-inverse-of I↠J x)
           (Surjection.to A↠B ⟨$⟩ (Surjection.from A↠B ⟨$⟩
              (P.subst B (P.sym (Surjection.right-inverse-of I↠J x))
                 y)))                                                    ≡⟨ P.cong (P.subst B _) (Surjection.right-inverse-of A↠B _) ⟩

         P.subst B (Surjection.right-inverse-of I↠J x)
           (P.subst B (P.sym (Surjection.right-inverse-of I↠J x))
              y)                                                         ≡⟨ P.subst-subst-sym (Surjection.right-inverse-of I↠J x) ⟩

         y                                                               ∎)
      )

  ↔ : (I↔J : I ↔ J) →
      (∀ {x} → A x ↔ B (Inverse.to I↔J ⟨$⟩ x)) →
      Σ I A ↔ Σ J B
  ↔ I↔J A↔B = Inv.inverse
    (Surjection.to   surjection′ ⟨$⟩_)
    (Surjection.from surjection′ ⟨$⟩_)
    left-inverse-of
    (Surjection.right-inverse-of surjection′)
    where
    open P.≡-Reasoning

    I≃J = ↔→≃ I↔J

    surjection′ : _↠_ (Σ I A) (Σ J B)
    surjection′ =
      ↠ (Inverse.surjection (_≃_.inverse I≃J))
        (Inverse.surjection A↔B)

    left-inverse-of :
      ∀ p → Surjection.from surjection′ ⟨$⟩
              (Surjection.to surjection′ ⟨$⟩ p) ≡ p
    left-inverse-of (x , y) = Σ-≡,≡→≡
      ( _≃_.left-inverse-of I≃J x
      , (P.subst A (_≃_.left-inverse-of I≃J x)
           (Inverse.from A↔B ⟨$⟩
              (P.subst B (P.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (Inverse.to A↔B ⟨$⟩ y)))                   ≡⟨ P.subst-application B (λ _ → Inverse.from A↔B ⟨$⟩_) _ ⟩

         Inverse.from A↔B ⟨$⟩
           (P.subst B (P.cong (_≃_.to I≃J)
                          (_≃_.left-inverse-of I≃J x))
              (P.subst B (P.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (Inverse.to A↔B ⟨$⟩ y)))                   ≡⟨ P.cong (λ eq → Inverse.from A↔B ⟨$⟩ P.subst B eq
                                                                                  (P.subst B (P.sym (_≃_.right-inverse-of I≃J _)) _))
                                                                   (_≃_.left-right I≃J _) ⟩
         Inverse.from A↔B ⟨$⟩
           (P.subst B (_≃_.right-inverse-of I≃J
                          (_≃_.to I≃J x))
              (P.subst B (P.sym (_≃_.right-inverse-of I≃J
                                    (_≃_.to I≃J x)))
                 (Inverse.to A↔B ⟨$⟩ y)))                   ≡⟨ P.cong (Inverse.from A↔B ⟨$⟩_)
                                                                   (P.subst-subst-sym (_≃_.right-inverse-of I≃J _)) ⟩

         Inverse.from A↔B ⟨$⟩ (Inverse.to A↔B ⟨$⟩ y)      ≡⟨ Inverse.left-inverse-of A↔B _ ⟩

         y                                                    ∎)
      )

private

  swap-coercions : ∀ {k a₁ a₂ b₁ b₂} {I : Set a₁} {J : Set a₂}
    {A : I → Set b₁} (B : J → Set b₂)
    (I↔J : _↔_ I J) →
    (∀ {x} → A x ∼[ k ] B (Inverse.to I↔J ⟨$⟩ x)) →
    ∀ {x} → A (Inverse.from I↔J ⟨$⟩ x) ∼[ k ] B x
  swap-coercions {k} {A = A} B I↔J eq {x} =
    A (Inverse.from I↔J ⟨$⟩ x)
      ∼⟨ eq ⟩
    B (Inverse.to I↔J ⟨$⟩ (Inverse.from I↔J ⟨$⟩ x))
      ↔⟨ K-reflexive
         (P.cong B $ Inverse.right-inverse-of I↔J x) ⟩
    B x
      ∎
    where open EquationalReasoning

cong : ∀ {k a₁ a₂ b₁ b₂}
         {I : Set a₁} {J : Set a₂}
         {A : I → Set b₁} {B : J → Set b₂}
       (I↔J : _↔_ I J) →
       (∀ {x} → A x ∼[ k ] B (Inverse.to I↔J ⟨$⟩ x)) →
       Σ I A ∼[ k ] Σ J B
cong {implication}                   =
  λ I↔J → map (_⟨$⟩_ (Inverse.to I↔J))
cong {reverse-implication} {B = B} =
  λ I↔J A←B → lam (map (_⟨$⟩_ (Inverse.from I↔J))
    (app-← (swap-coercions B I↔J A←B)))
cong {equivalence}                   = ⇔-↠ ∘ Inverse.surjection
cong {injection}                     = ↣
cong {reverse-injection}   {B = B} =
  λ I↔J A↢B → lam (↣ (Inv.sym I↔J)
    (app-↢ (swap-coercions B I↔J A↢B)))
cong {left-inverse}                  =
  λ I↔J → ↩ (Inverse.left-inverse I↔J) ∘ swap-coercions _ I↔J
cong {surjection}                    = ↠ ∘ Inverse.surjection
cong {bijection}                     = ↔
-}
