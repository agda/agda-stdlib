------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for propositional equality
-- preserving functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Function.Dependent.Propositional where

open import Data.Product as Prod
open import Data.Product.Function.NonDependent.Setoid using ()
open import Data.Product.Relation.Binary.Pointwise.NonDependent using ()
open import Data.Product.Properties using (Σ-≡,≡→≡)
open import Level using (Level)
open import Function.Base
open import Function.Consequences.Propositional using (inverseʳ⇒injective)
open import Function.Definitions using (Inverseˡ; Inverseʳ; Injective)
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

  Σ-↣ : ∀ (I↔J : I ↔ J) →
      (∀ {x} → A x ↣ B (Inverse.to I↔J x)) →
      Σ I A ↣ Σ J B
  Σ-↣ {I = I} {J = J} {A = A} {B = B} I↔J A↣B = mk↣ {to = to′} {!!}
    where
    open P.≡-Reasoning

    to′ : Σ I A → Σ J B
    to′ = map (Inverse.to I↔J) (Injection.to A↣B)
    module IJ = Inverse I↔J
 
    subst-application′ :
      {x₁ x₂ : I} {y : A (IJ.from (IJ.to x₁))}
      (g : ∀ x → A (IJ.from (IJ.to x)) → B (IJ.to x)) (eq : IJ.to x₁ ≡ IJ.to x₂) →
      P.subst B eq (g x₁ y) ≡ g x₂ (P.subst A (P.cong IJ.from eq) y)
    subst-application′ {x₁} {x₂} {y} g eq = begin
      P.subst B eq (g x₁ y)                      ≡⟨ P.cong (P.subst B eq) (P.sym (g′-lemma _ _)) ⟩
      P.subst B eq (g′ (to x₁) y)                ≡⟨ P.subst-application A g′ eq ⟩
      g′ (to x₂) (P.subst A (P.cong from eq) y)  ≡⟨ g′-lemma _ _ ⟩
      g x₂ (P.subst A (P.cong from eq) y)        ∎
      where
      open Inverse I↔J

      g′ : ∀ x → A (from x) → B x
      g′ x =
        P.subst B (strictlyInverseˡ x) ∘
        g (from x) ∘
        P.subst A (P.sym (P.cong from (strictlyInverseˡ x)))

      g′-lemma : ∀ x y → g′ (to x) y ≡ g x y
      g′-lemma x y =
        P.subst B (strictlyInverseˡ (to x))
          (g (from (to x)) $
           P.subst A (P.sym (P.cong from (strictlyInverseˡ (to x)))) y)  ≡⟨ P.cong (λ p → P.subst B p (g (from (to x))
                                                                                                           (P.subst A (P.sym (P.cong from p)) y)))
                                                                               (P.sym ({!!})) ⟩  -- was: left-right x
        P.subst B (P.cong to (strictlyInverseʳ x))
          (g (from (to x)) $
           P.subst A
             (P.sym (P.cong from (P.cong to (strictlyInverseʳ x))))
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


    to-injective : Injective _≡_ _≡_ to′
    to-injective {(x₁ , x₂)} {(y₁ , y₂)} to-eq =
      Σ-≡,≡→≡ ( inj₁ , inj₂)

        where
          A→B : ∀ {x} → A x → B (Inverse.to I↔J x)
          A→B Ax = Injection.to A↣B Ax
          Inj : Injection (P.setoid I) (P.setoid J)
          Inj = record { to = IJ.to
                       ; cong = IJ.to-cong
                       ; injective = λ {x} {y} eq → P.trans (P.sym (IJ.strictlyInverseʳ x)) (P.trans (P.cong IJ.from eq) (IJ.strictlyInverseʳ y))
                       }
          from∘to : ∀ x → IJ.from (IJ.to x) ≡ x
          from∘to = IJ.strictlyInverseʳ
          inj₁ : x₁ ≡ y₁
          inj₁ = injective Inj (P.cong proj₁ to-eq)
          A→B-eq : A→B (P.subst A inj₁ x₂) ≡ A→B y₂
          A→B-eq = begin
            A→B (P.subst A
             (P.trans (P.sym (from∘to x₁))
             (P.trans (P.cong IJ.from (P.cong proj₁ to-eq)) (from∘to y₁))) x₂)    ≡˘⟨ P.cong A→B (P.subst-subst (P.sym (from∘to x₁))) ⟩ 
            A→B (P.subst A
             (P.trans (P.cong IJ.from (P.cong proj₁ to-eq)) (from∘to y₁))
             (P.subst A (P.sym (from∘to x₁)) x₂))                              ≡˘⟨ P.cong A→B (P.subst-subst (P.cong IJ.from (P.cong proj₁ to-eq))) ⟩
            A→B (P.subst A (from∘to y₁)
                (P.subst A (P.cong IJ.from (P.cong proj₁ to-eq))
                (P.subst A (P.sym (from∘to x₁)) x₂)))                          ≡˘⟨ {!!}  ⟩
           {- P.subst B {!P.cong proj₁ to-eq!}
              (A→B (P.subst A {!from∘to x₁!}
                   (P.subst A (P.sym (from∘to x₁)) x₂)))                            ≡⟨ {!!} ⟩ -}
            P.subst B (P.cong proj₁ to-eq) (A→B {x₁} x₂)                       ≡⟨ {!P.cong proj₂ to-eq!} ⟩
            A→B y₂ ∎ 
          inj₂ : P.subst A inj₁ x₂ ≡ y₂
          inj₂ = injective A↣B A→B-eq
         {-
      map (_≃_.injective I≃J) (λ {eq₁} eq₂ →
        let lemma =

              Injection.to A↣B ⟨$⟩
              P.subst A
                (P.trans (P.sym (_≃_.left-inverse-of I≃J x₁))
                   (P.trans (P.cong (_≃_.from I≃J) eq₁)
                      (_≃_.left-inverse-of I≃J y₁)))
                x₂                                                        ≡⟨ P.cong (Injection.to A↣B ⟨$⟩_)
                                                                               (P.sym (P.subst-subst (P.sym (_≃_.left-inverse-of I≃J _)))) ⟩
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
      -- (∀ {j} → A (LeftInverse.from I↩J j) ↩ B j) →
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
          (P.subst B (P.sym (inverseˡ I↩J P.refl)) b)                        ≡⟨ P.subst-subst-sym (inverseˡ I↩J _) ⟩
        b ∎))
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
-}
module _ where
  open Inverse

  ↔ : (I↔J : I ↔ J) →
      (∀ {x} → A x ↔ B (to I↔J x)) →
      Σ I A ↔ Σ J B
  ↔ {I = I} {J = J} {A = A} {B = B} I↔J A↔B = mk↔ {to = to′} {from = from′} (invˡ , invʳ)
   where
     open P.≡-Reasoning
     -- useful to make things look shorter
     I↔Jˡ : ∀ i → to I↔J (from I↔J i) ≡ i
     I↔Jˡ = strictlyInverseˡ I↔J
     I↔Jʳ : ∀ j → from I↔J (to I↔J j) ≡ j
     I↔Jʳ = strictlyInverseʳ I↔J
     to′ : Σ I A → Σ J B
     to′ = map (to I↔J) (to A↔B)
     from′ : Σ J B → Σ I A
     from′ = map (from I↔J) λ {x} bx → from A↔B (P.subst B (P.sym {!strictlyInverseʳ I↔J ?!}) bx) -- (P.subst B (P.sym (strictlyInverseˡ I↔J x)) bx)
     invˡ : Inverseˡ _≡_ _≡_ to′ from′
     invˡ {x = x₀ , x₁} P.refl = Σ-≡,≡→≡ (I↔Jˡ x₀ , (begin
       P.subst B (I↔Jˡ x₀)
         (to A↔B (from A↔B (P.subst B (P.sym (I↔Jˡ x₀)) x₁))) ≡⟨ P.cong (P.subst B _) (strictlyInverseˡ A↔B _) ⟩
       P.subst B (I↔Jˡ x₀) (P.subst B (P.sym (I↔Jˡ x₀)) x₁)   ≡⟨ P.subst-subst-sym (I↔Jˡ x₀) ⟩
       x₁ ∎))
     invʳ : Inverseʳ _≡_ _≡_ to′ from′
     invʳ {x = x₀ , x₁} {y₀ , y₁} P.refl = Σ-≡,≡→≡ (eq₁ , eq₂) 
       where
         eq₁ : proj₁ (from′ (y₀ , y₁)) ≡ x₀
         eq₁ = {!strictlyInverseˡ I↔J (to I↔J x₀)!} -- strictlyInverseʳ I↔J x₀ -- proj₂ (inverse I↔J) P.refl -- inverseʳ I↔J (P.cong proj₁ y≡to-x)
         eq₃ : to I↔J (from I↔J (to I↔J x₀)) ≡ to I↔J x₀
         eq₃ = {!I↔J!} -- this proof is forced upon us
         -- eq₄ : eq₃ ≡ P.cong (to I↔J) eq₁
         eq₄ : {A B : Set} {f : A → B} {g : B → A} {a : A} {b : B} (eq₁ : f a ≡ b) (p : g (f a) ≡ a) (q : f (g b) ≡ b) → q ≡ P.subst (λ bb → f (g bb) ≡ bb) eq₁ (P.cong f p)
         eq₄ P.refl p q = {!!}
         eq₂ : P.subst A eq₁ (proj₂ (from′ (y₀ , y₁))) ≡ x₁
         eq₂ = begin
           P.subst A eq₁ (proj₂ (from′ (y₀ , y₁)))                               ≡⟨⟩
           P.subst A eq₁ (from A↔B (P.subst B (P.sym eq₃) y₁))                   ≡⟨ P.subst-application B (λ _ y → from A↔B y) eq₁ ⟩
           from A↔B (P.subst B (P.cong (to I↔J) eq₁) (P.subst B (P.sym eq₃) y₁)) ≡⟨ {!eq₁!} ⟩
           from A↔B (P.subst B (P.trans (P.sym eq₃) (P.cong (to I↔J) eq₁)) y₁)   ≡⟨ {!to-cong A↔B!} ⟩ 
           x₁ ∎
         

{-
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
