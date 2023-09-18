------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for setoid equality preserving
-- functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Function.Dependent.Setoid where

open import Data.Product.Base using (map; _,_)
open import Data.Product.Relation.Binary.Pointwise.Dependent as Σ
open import Level using (Level)
open import Function
open import Relation.Binary.Core using (_=[_]⇒_)
open import Relation.Binary.Bundles as B
open import Relation.Binary.Indexed.Heterogeneous
  using (IndexedSetoid)
open import Relation.Binary.Indexed.Heterogeneous.Construct.At
  using (_atₛ_)
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
import Relation.Binary.PropositionalEquality.Properties as P

private
  variable
    i a b ℓ₁ ℓ₂ : Level
    I J : Set i
    A B : IndexedSetoid I a ℓ₁

------------------------------------------------------------------------
-- Properties related to "relatedness"
------------------------------------------------------------------------

private
  subst-cong : ∀ {A : I → Set a}
               (P : ∀ {i} → A i → A i → Set ℓ₁) {i i′} {x y : A i}
               (i≡i′ : i ≡ i′) →
               P x y → P (P.subst A i≡i′ x) (P.subst A i≡i′ y)
  subst-cong P P.refl p = p

  _×ₛ_ : (I : Set i) → IndexedSetoid I a ℓ₁ → Setoid _ _
  I ×ₛ A = Σ.setoid (P.setoid I) A
  
------------------------------------------------------------------------
-- Functions

module _ where
  open Func
  open Setoid
  
  ⟶ : (f : I ⟶ J) →
        (∀ {i} → Func (A atₛ i) (B atₛ (to f i))) →
        Func (I ×ₛ A) (J ×ₛ B)
  ⟶ {I = I} {J = J} {A = A} {B = B} I⟶J A⟶B = record
    { to    = to′
    ; cong  = cong′
    }
    where
    to′ = map (to I⟶J) (to A⟶B)

    cong′ : Congruent (_≈_ (I ×ₛ A)) (_≈_ (J ×ₛ B)) to′
    cong′ (P.refl , ∼) = (P.refl , cong A⟶B ∼)

------------------------------------------------------------------------
-- Equivalences

module _ where
  open Equivalence
  
  equivalence : 
    (I⇔J : I ⇔ J) →
    (∀ {x} → Func (A atₛ x) (B atₛ (to   I⇔J x))) →
    (∀ {y} → Func (B atₛ y) (A atₛ (from I⇔J y))) →
    Equivalence (I ×ₛ A) (J ×ₛ B)
  equivalence I⇔J A⟶B B⟶A = record
    { to      = map (to   I⇔J) {!!}
    ; to-cong = {!!}
    ; from    = map (from I⇔J) {!!} --B-from
    ; from-cong = {!!}
    } where open Equivalence

  equivalence-↪ :
    (I↪J : I ↪ J) →
    (∀ {i} → Equivalence (A atₛ (RightInverse.from I↪J i)) (B atₛ i)) →
    Equivalence (I ×ₛ A) (J ×ₛ B)
  equivalence-↪ {A = A} {B = B} I↪J A⇔B =
    equivalence (RightInverse.equivalence I↪J) B-to {!from ?!}
    where
    B-to : ∀ {i} → Func (A atₛ i) (B atₛ (RightInverse.to I↪J i))
    B-to = record
      { _⟨$⟩_ = λ x → Equivalence.to A⇔B $ 
                      P.subst (IndexedSetoid.Carrier A)
                         (P.sym $ {!!}) --LeftInverse.left-inverse-of I↞J _)
                         x
      ; cong  = {!!} {-F.cong (Equivalence.to A⇔B) ∘
              subst-cong (λ {x} → IndexedSetoid._≈_ A {x} {x})
                         (P.sym (LeftInverse.left-inverse-of I↞J _)) -}
      }

    B-from : ∀ {y} → Func (B atₛ y) (A atₛ (RightInverse.from I↪J y))
    B-from = {!!} --Equivalence.from A⇔B
{-
  equivalence-↠ : {A : IndexedSetoid I b₁ b₁′} (B : IndexedSetoid J b₂ b₂′)
    (I↠J : I ↠ J) →
    (∀ {x} → Equivalence (A atₛ x) (B atₛ (Surjection.to I↠J ⟨$⟩ x))) →
    Equivalence (I ×ₛ A) (J ×ₛ B)
  equivalence-↠ {A = A} B I↠J A⇔B =
    equivalence (Surjection.equivalence I↠J) B-to B-from
    where
    B-to : ∀ {x} → _⟶_ (A atₛ x) (B atₛ (Surjection.to I↠J ⟨$⟩ x))
    B-to = Equivalence.to A⇔B

    B-from : ∀ {y} → _⟶_ (B atₛ y) (A atₛ (Surjection.from I↠J ⟨$⟩ y))
    B-from = record
      { _⟨$⟩_ = λ x → Equivalence.from A⇔B ⟨$⟩
                      P.subst (IndexedSetoid.Carrier B)
                         (P.sym $ Surjection.right-inverse-of I↠J _)
                         x
      ; cong  = F.cong (Equivalence.from A⇔B) ∘
              subst-cong (λ {x} → IndexedSetoid._≈_ B {x} {x})
                         (P.sym (Surjection.right-inverse-of I↠J _))
      }
-}
{-
  injection : {A : IndexedSetoid I b₁ b₁′} (B : IndexedSetoid J b₂ b₂′) →
    (I↣J : I ↣ J) →
    (∀ {x} → Injection (A atₛ x) (B atₛ (Injection.to I↣J ⟨$⟩ x))) →
    Injection (I ×ₛ A) (J ×ₛ B)
  injection {A = A} B I↣J A↣B = record
    { to        = to
    ; injective = inj
    }
    where
    to = ⟶ B (Injection.to I↣J ⟨$⟩_) (Injection.to A↣B)

    inj : Injective to
    inj (x , y) =
      Injection.injective I↣J x ,
      lemma (Injection.injective I↣J x) y
      where
      lemma :
        ∀ {x x′}
          {y : IndexedSetoid.Carrier A x} {y′ : IndexedSetoid.Carrier A x′} →
        x ≡ x′ →
        (eq : IndexedSetoid._≈_ B (Injection.to A↣B ⟨$⟩ y)
                              (Injection.to A↣B ⟨$⟩ y′)) →
        IndexedSetoid._≈_ A y y′
      lemma P.refl = Injection.injective A↣B

  left-inverse : (A : IndexedSetoid I b₁ b₁′) {B : IndexedSetoid J b₂ b₂′} →
    (I↞J : I ↞ J) →
    (∀ {x} → LeftInverse (A atₛ (LeftInverse.from I↞J ⟨$⟩ x))
                         (B atₛ x)) →
    LeftInverse (I ×ₛ A) (J ×ₛ B)
  left-inverse A {B} I↞J A↞B = record
    { to              = Equivalence.to   eq
    ; from            = Equivalence.from eq
    ; left-inverse-of = left
    }
    where
    eq = equivalence-↞ A I↞J (LeftInverse.equivalence A↞B)

    left : Equivalence.from eq LeftInverseOf Equivalence.to eq
    left (x , y) =
      LeftInverse.left-inverse-of I↞J x ,
      IndexedSetoid.trans A
        (LeftInverse.left-inverse-of A↞B _)
        (lemma (P.sym (LeftInverse.left-inverse-of I↞J x)))
      where
      lemma :
        ∀ {x x′ y} (eq : x ≡ x′) →
        IndexedSetoid._≈_ A (P.subst (IndexedSetoid.Carrier A) eq y) y
      lemma P.refl = IndexedSetoid.refl A

  surjection : {A : IndexedSetoid I b₁ b₁′} (B : IndexedSetoid J b₂ b₂′) →
    (I↠J : I ↠ J) →
    (∀ {x} → Surjection (A atₛ x) (B atₛ (Surjection.to I↠J ⟨$⟩ x))) →
    Surjection (I ×ₛ A) (J ×ₛ B)
  surjection B I↠J A↠B = record
    { to         = Equivalence.to eq
    ; surjective = record
      { from             = Equivalence.from eq
      ; right-inverse-of = right
      }
    }
    where
    eq = equivalence-↠ B I↠J (Surjection.equivalence A↠B)

    right : Equivalence.from eq RightInverseOf Equivalence.to eq
    right (x , y) =
      Surjection.right-inverse-of I↠J x ,
      IndexedSetoid.trans B
        (Surjection.right-inverse-of A↠B _)
        (lemma (P.sym $ Surjection.right-inverse-of I↠J x))
      where
      lemma : ∀ {x x′ y} (eq : x ≡ x′) →
              IndexedSetoid._≈_ B (P.subst (IndexedSetoid.Carrier B) eq y) y
      lemma P.refl = IndexedSetoid.refl B

  -- See also Data.Product.Function.Dependent.Setoid.WithK.inverse.
-}
