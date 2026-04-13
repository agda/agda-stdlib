------------------------------------------------------------------------
-- The Agda standard library
--
-- An All predicate for the partiality monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --guardedness #-}

module Effect.Monad.Partiality.All where

open import Effect.Monad using (RawMonad)
open import Effect.Monad.Partiality as Partiality using (_⊥; ⇒≈)
open import Codata.Musical.Notation using (♭; ∞; ♯_)
open import Function.Base using (flip; _∘_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

open Partiality._⊥
open Partiality.Equality using (Rel)
open Partiality.Equality.Rel
private
  open module E {a} {A : Set a} = Partiality.Equality (_≡_ {A = A})
    using (_≅_; _≳_)
  open module M {f} = RawMonad (Partiality.monad {f = f})
    using (_>>=_)

private
  variable
    a b p ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- All, along with some lemmas

-- All P x means that if x terminates with the value v, then P v
-- holds.

data All {A : Set a} (P : A → Set p) : A ⊥ → Set (a ⊔ p) where
  now   : ∀ {v} (p : P v)             → All P (now v)
  later : ∀ {x} (p : ∞ (All P (♭ x))) → All P (later x)

-- Bind preserves All in the following way:

infixl 1 _>>=-cong_

_>>=-cong_ : ∀ {p q} {P : A → Set p} {Q : B → Set q}
               {x : A ⊥} {f : A → B ⊥} →
             All P x → (∀ {x} → P x → All Q (f x)) →
             All Q (x >>= f)
now p   >>=-cong f = f p
later p >>=-cong f = later (♯ (♭ p >>=-cong f))

-- All respects all the relations, given that the predicate respects
-- the underlying relation.

respects :
  ∀ {k} {P : A → Set p} {_∼_ : A → A → Set ℓ} →
  P Respects _∼_ → All P Respects Rel _∼_ k
respects resp (now    x∼y) (now   p) = now (resp x∼y p)
respects resp (later  x∼y) (later p) = later (♯ respects resp (♭ x∼y) (♭ p))
respects resp (laterˡ x∼y) (later p) =          respects resp    x∼y  (♭ p)
respects resp (laterʳ x≈y) p         = later (♯ respects resp    x≈y     p)

respects-flip :
  ∀ {k} {P : A → Set p} {_∼_ : A → A → Set ℓ} →
  P Respects flip _∼_ → All P Respects flip (Rel _∼_ k)
respects-flip resp (now    x∼y) (now   p) = now (resp x∼y p)
respects-flip resp (later  x∼y) (later p) = later (♯ respects-flip resp (♭ x∼y) (♭ p))
respects-flip resp (laterˡ x∼y) p         = later (♯ respects-flip resp    x∼y     p)
respects-flip resp (laterʳ x≈y) (later p) =          respects-flip resp    x≈y  (♭ p)

-- "Equational" reasoning.

module Reasoning {P : A → Set p}
                 {_∼_ : A → A → Set ℓ}
                 (resp : P Respects flip _∼_) where

  infix  3 finally
  infixr 2 _≡⟨_⟩_ _∼⟨_⟩_

  _≡⟨_⟩_ : ∀ x {y} → x ≡ y → All P y → All P x
  _ ≡⟨ ≡.refl ⟩ p = p

  _∼⟨_⟩_ : ∀ {k} x {y} → Rel _∼_ k x y → All P y → All P x
  _ ∼⟨ x∼y ⟩ p = respects-flip resp (⇒≈ x∼y) p

  -- A cosmetic combinator.

  finally : (x : A ⊥) → All P x → All P x
  finally _ p = p

  syntax finally x p = x ⟨ p ⟩

-- "Equational" reasoning with _∼_ instantiated to propositional
-- equality.

module Reasoning-≡ {a p} {A : Set a} {P : A → Set p}
  = Reasoning {P = P} {_∼_ = _≡_} (≡.subst P ∘ ≡.sym)

------------------------------------------------------------------------
-- An alternative, but equivalent, formulation of All

module Alternative {a p : Level} where

  infix  3 _⟨_⟩P
  infixr 2 _≅⟨_⟩P_ _≳⟨_⟩P_

  -- All "programs".

  data AllP {A : Set a} (P : A → Set p) : A ⊥ → Set (suc (a ⊔ p)) where
    now         : ∀ {x} (p : P x) → AllP P (now x)
    later       : ∀ {x} (p : ∞ (AllP P (♭ x))) → AllP P (later x)
    _>>=-congP_ : ∀ {B : Set a} {Q : B → Set p} {x f}
                  (p-x : AllP Q x) (p-f : ∀ {v} → Q v → AllP P (f v)) →
                  AllP P (x >>= f)
    _≅⟨_⟩P_     : ∀ x {y} (x≅y : x ≅ y) (p : AllP P y) → AllP P x
    _≳⟨_⟩P_     : ∀ x {y} (x≳y : x ≳ y) (p : AllP P y) → AllP P x
    _⟨_⟩P       : ∀ x (p : AllP P x) → AllP P x

  infixl 1 _>>=-congP_

  private

    -- WHNFs.

    data AllW {A} (P : A → Set p) : A ⊥ → Set (suc (a ⊔ p)) where
      now   : ∀ {x} (p : P x) → AllW P (now x)
      later : ∀ {x} (p : AllP P (♭ x)) → AllW P (later x)

    -- A function which turns WHNFs into programs.

    program : ∀ {P : A → Set p} {x} → AllW P x → AllP P x
    program (now   p) = now      p
    program (later p) = later (♯ p)

    -- Functions which turn programs into WHNFs.

    trans-≅ : {P : A → Set p} {x y : A ⊥} →
              x ≅ y → AllW P y → AllW P x
    trans-≅ (now ≡.refl) (now   p) = now p
    trans-≅ (later  x≅y) (later p) = later (_ ≅⟨ ♭ x≅y ⟩P p)

    trans-≳ : {P : A → Set p} {x y : A ⊥} →
              x ≳ y → AllW P y → AllW P x
    trans-≳ (now ≡.refl) (now   p) = now p
    trans-≳ (later  x≳y) (later p) = later (_ ≳⟨ ♭ x≳y ⟩P p)
    trans-≳ (laterˡ x≳y)        p  = later (_ ≳⟨   x≳y ⟩P program p)

    mutual

      _>>=-congW_ : ∀ {P : A → Set p} {Q : B → Set p} {x f} →
                    AllW P x → (∀ {v} → P v → AllP Q (f v)) →
                    AllW Q (x >>= f)
      now   p >>=-congW p-f = whnf (p-f p)
      later p >>=-congW p-f = later (p >>=-congP p-f)

      whnf : ∀ {P : A → Set p} {x} → AllP P x → AllW P x
      whnf (now   p)           = now p
      whnf (later p)           = later (♭ p)
      whnf (p-x >>=-congP p-f) = whnf p-x >>=-congW p-f
      whnf (_ ≅⟨ x≅y ⟩P p)     = trans-≅ x≅y (whnf p)
      whnf (_ ≳⟨ x≳y ⟩P p)     = trans-≳ x≳y (whnf p)
      whnf (_ ⟨ p ⟩P)          = whnf p

  -- AllP P is sound and complete with respect to All P.

  sound : ∀ {P : A → Set p} {x} → AllP P x → All P x
  sound = λ p → soundW (whnf p)
    where
    soundW : ∀ {A} {P : A → Set p} {x} → AllW P x → All P x
    soundW (now   p) = now p
    soundW (later p) = later (♯ sound p)

  complete : ∀ {P : A → Set p} {x} → All P x → AllP P x
  complete (now   p) = now p
  complete (later p) = later (♯ complete (♭ p))
