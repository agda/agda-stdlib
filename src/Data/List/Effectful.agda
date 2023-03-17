------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of List
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Effectful where

open import Data.Bool.Base using (false; true)
open import Data.List.Base
open import Data.List.Properties
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; _≗_; refl)
open P.≡-Reasoning

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- List applicative functor

functor : RawFunctor {ℓ} List
functor = record { _<$>_ = map }

applicative : RawApplicative {ℓ} List
applicative = record
  { rawFunctor = functor
  ; pure = [_]
  ; _<*>_  = ap
  }

empty : RawEmpty {ℓ} List
empty = record { empty = [] }

choice : RawChoice {ℓ} List
choice = record { _<|>_ = _++_ }

applicativeZero : RawApplicativeZero {ℓ} List
applicativeZero = record
  { rawApplicative = applicative
  ; rawEmpty = empty
  }

alternative : RawAlternative {ℓ} List
alternative = record
  { rawApplicativeZero = applicativeZero
  ; rawChoice = choice
  }

------------------------------------------------------------------------
-- List monad

monad : ∀ {ℓ} → RawMonad {ℓ} List
monad = record
  { rawApplicative = applicative
  ; _>>=_  = flip concatMap
  }

monadZero : ∀ {ℓ} → RawMonadZero {ℓ} List
monadZero = record
  { rawMonad = monad
  ; rawEmpty = empty
  }

monadPlus : ∀ {ℓ} → RawMonadPlus {ℓ} List
monadPlus = record
  { rawMonadZero = monadZero
  ; rawChoice  = choice
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {f g F} (App : RawApplicative {f} {g} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → List (F A) → F (List A)
  sequenceA []       = pure []
  sequenceA (x ∷ xs) = _∷_ <$> x <*> sequenceA xs

  mapA : ∀ {a} {A : Set a} {B} → (A → F B) → List A → F (List B)
  mapA f = sequenceA ∘ map f

  forA : ∀ {a} {A : Set a} {B} → List A → (A → F B) → F (List B)
  forA = flip mapA

module TraversableM {m n M} (Mon : RawMonad {m} {n} M) where

  open RawMonad Mon

  open TraversableA rawApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )

------------------------------------------------------------------------
-- The list monad.

private
  open module LMP {ℓ} = RawMonadPlus (monadPlus {ℓ = ℓ})

module MonadProperties where

  left-identity : ∀ {ℓ} {A B : Set ℓ} (x : A) (f : A → List B) →
                  (pure x >>= f) ≡ f x
  left-identity x f = ++-identityʳ (f x)

  right-identity : ∀ {ℓ} {A : Set ℓ} (xs : List A) →
                   (xs >>= pure) ≡ xs
  right-identity []       = refl
  right-identity (x ∷ xs) = P.cong (x ∷_) (right-identity xs)

  left-zero : ∀ {ℓ} {A B : Set ℓ} (f : A → List B) → (∅ >>= f) ≡ ∅
  left-zero f = refl

  right-zero : ∀ {ℓ} {A B : Set ℓ} (xs : List A) →
               (xs >>= const ∅) ≡ ∅ {A = B}
  right-zero []       = refl
  right-zero (x ∷ xs) = right-zero xs

  private

    not-left-distributive :
      let xs = true ∷ false ∷ []; f = pure; g = pure in
      (xs >>= λ x → f x ∣ g x) ≢ ((xs >>= f) ∣ (xs >>= g))
    not-left-distributive ()

  right-distributive : ∀ {ℓ} {A B : Set ℓ}
                       (xs ys : List A) (f : A → List B) →
                       (xs ∣ ys >>= f) ≡ ((xs >>= f) ∣ (ys >>= f))
  right-distributive []       ys f = refl
  right-distributive (x ∷ xs) ys f = begin
    f x ∣ (xs ∣ ys >>= f)              ≡⟨ P.cong (f x ∣_) $ right-distributive xs ys f ⟩
    f x ∣ ((xs >>= f) ∣ (ys >>= f))    ≡⟨ P.sym $ ++-assoc (f x) _ _ ⟩
    ((f x ∣ (xs >>= f)) ∣ (ys >>= f))  ∎

  associative : ∀ {ℓ} {A B C : Set ℓ}
                (xs : List A) (f : A → List B) (g : B → List C) →
                (xs >>= λ x → f x >>= g) ≡ (xs >>= f >>= g)
  associative []       f g = refl
  associative (x ∷ xs) f g = begin
    (f x >>= g) ∣ (xs >>= λ x → f x >>= g)  ≡⟨ P.cong ((f x >>= g) ∣_) $ associative xs f g ⟩
    (f x >>= g) ∣ (xs >>= f >>= g)          ≡⟨ P.sym $ right-distributive (f x) (xs >>= f) g ⟩
    (f x ∣ (xs >>= f) >>= g)                ∎

  cong : ∀ {ℓ} {A B : Set ℓ} {xs₁ xs₂} {f₁ f₂ : A → List B} →
         xs₁ ≡ xs₂ → f₁ ≗ f₂ → (xs₁ >>= f₁) ≡ (xs₂ >>= f₂)
  cong {xs₁ = xs} refl f₁≗f₂ = P.cong concat (map-cong f₁≗f₂ xs)

------------------------------------------------------------------------
-- The applicative functor derived from the list monad.

-- Note that these proofs (almost) show that RawIMonad.rawIApplicative
-- is correctly defined. The proofs can be reused if proof components
-- are ever added to RawIMonad and RawIApplicative.

module Applicative where

  private

    module MP = MonadProperties

    -- A variant of flip map.

    pam : ∀ {ℓ} {A B : Set ℓ} → List A → (A → B) → List B
    pam xs f = xs >>= pure ∘ f

  -- ∅ is a left zero for _⊛_.

  left-zero : ∀ {ℓ} {A B : Set ℓ} → (xs : List A) → (∅ ⊛ xs) ≡ ∅ {A = B}
  left-zero xs = begin
    ∅ ⊛ xs          ≡⟨⟩
    (∅ >>= pam xs)  ≡⟨ MonadProperties.left-zero (pam xs) ⟩
    ∅               ∎

  -- ∅ is a right zero for _⊛_.

  right-zero : ∀ {ℓ} {A B : Set ℓ} → (fs : List (A → B)) → (fs ⊛ ∅) ≡ ∅
  right-zero {ℓ} fs = begin
    fs ⊛ ∅            ≡⟨⟩
    (fs >>= pam ∅)    ≡⟨ (MP.cong (refl {x = fs}) λ f →
                          MP.left-zero (pure ∘ f)) ⟩
    (fs >>= λ _ → ∅)  ≡⟨ MP.right-zero fs ⟩
    ∅                 ∎

  unfold-<$> : ∀ {ℓ} {A B : Set ℓ} → (f : A → B) (as : List A) →
               (f <$> as) ≡ (pure f ⊛ as)
  unfold-<$> f as = P.sym (++-identityʳ (f <$> as))

  -- _⊛_ unfolds to binds.
  unfold-⊛ : ∀ {ℓ} {A B : Set ℓ} → (fs : List (A → B)) (as : List A) →
             (fs ⊛ as) ≡ (fs >>= pam as)
  unfold-⊛ fs as = begin
    fs ⊛ as
      ≡˘⟨ concatMap-cong (λ f → P.cong (map f) (concatMap-pure as)) fs ⟩
    concatMap (λ f → map f (concatMap pure as)) fs
      ≡⟨ concatMap-cong (λ f → map-concatMap f pure as) fs ⟩
    concatMap (λ f → concatMap (λ x → pure (f x)) as) fs
      ≡⟨⟩
    (fs >>= pam as)
      ∎

  -- _⊛_ distributes over _∣_ from the right.

  right-distributive : ∀ {ℓ} {A B : Set ℓ} (fs₁ fs₂ : List (A → B)) xs →
                       ((fs₁ ∣ fs₂) ⊛ xs) ≡ (fs₁ ⊛ xs ∣ fs₂ ⊛ xs)
  right-distributive fs₁ fs₂ xs = begin
    (fs₁ ∣ fs₂) ⊛ xs                     ≡⟨ unfold-⊛ (fs₁ ∣ fs₂) xs ⟩
    (fs₁ ∣ fs₂ >>= pam xs)               ≡⟨ MonadProperties.right-distributive fs₁ fs₂ (pam xs) ⟩
    (fs₁ >>= pam xs) ∣ (fs₂ >>= pam xs)  ≡˘⟨ P.cong₂ _∣_ (unfold-⊛ fs₁ xs) (unfold-⊛ fs₂ xs) ⟩
    (fs₁ ⊛ xs ∣ fs₂ ⊛ xs)                ∎

  -- _⊛_ does not distribute over _∣_ from the left.

  private

    not-left-distributive :
      let fs = id ∷ id ∷ []; xs₁ = true ∷ []; xs₂ = true ∷ false ∷ [] in
      (fs ⊛ (xs₁ ∣ xs₂)) ≢ (fs ⊛ xs₁ ∣ fs ⊛ xs₂)
    not-left-distributive ()

  -- Applicative functor laws.

  identity : ∀ {a} {A : Set a} (xs : List A) → (pure id ⊛ xs) ≡ xs
  identity xs = begin
    pure id ⊛ xs          ≡⟨ unfold-⊛ (pure id) xs ⟩
    (pure id >>= pam xs)  ≡⟨ MonadProperties.left-identity id (pam xs) ⟩
    (xs >>= pure)         ≡⟨ MonadProperties.right-identity xs ⟩
    xs                    ∎

  private

    pam-lemma : ∀ {ℓ} {A B C : Set ℓ}
                (xs : List A) (f : A → B) (fs : B → List C) →
                (pam xs f >>= fs) ≡ (xs >>= λ x → fs (f x))
    pam-lemma xs f fs = begin
      (pam xs f >>= fs)                 ≡˘⟨ MP.associative xs (pure ∘ f) fs ⟩
      (xs >>= λ x → pure (f x) >>= fs)  ≡⟨ MP.cong (refl {x = xs}) (λ x → MP.left-identity (f x) fs) ⟩
      (xs >>= λ x → fs (f x))           ∎

  composition : ∀ {ℓ} {A B C : Set ℓ}
                (fs : List (B → C)) (gs : List (A → B)) xs →
                (pure _∘′_ ⊛ fs ⊛ gs ⊛ xs) ≡ (fs ⊛ (gs ⊛ xs))
  composition {ℓ} fs gs xs = begin
    pure _∘′_ ⊛ fs ⊛ gs ⊛ xs
      ≡⟨ unfold-⊛ (pure _∘′_ ⊛ fs ⊛ gs) xs ⟩
    (pure _∘′_ ⊛ fs ⊛ gs >>= pam xs)
      ≡⟨ P.cong (_>>= pam xs) (unfold-⊛ (pure _∘′_ ⊛ fs) gs) ⟩
    (pure _∘′_ ⊛ fs >>= pam gs >>= pam xs)
      ≡⟨ P.cong (λ h → h >>= pam gs >>= pam xs) (unfold-⊛ (pure _∘′_) fs) ⟩
    (pure _∘′_ >>= pam fs >>= pam gs >>= pam xs)
      ≡⟨ MP.cong (MP.cong (MP.left-identity _∘′_ (pam fs))
                 (λ f → refl {x = pam gs f}))
                 (λ fg → refl {x = pam xs fg}) ⟩
    (pam fs _∘′_ >>= pam gs >>= pam xs)
      ≡⟨ MP.cong (pam-lemma fs _∘′_ (pam gs)) (λ _ → refl) ⟩
    ((fs >>= λ f → pam gs (f ∘′_)) >>= pam xs)
      ≡˘⟨ MP.associative fs (λ f → pam gs (_∘′_ f)) (pam xs) ⟩
    (fs >>= λ f → pam gs (f ∘′_) >>= pam xs)
      ≡⟨ MP.cong (refl {x = fs}) (λ f → pam-lemma gs (f ∘′_) (pam xs)) ⟩
    (fs >>= λ f → gs >>= λ g → pam xs (f ∘′ g))
      ≡⟨ (MP.cong (refl {x = fs}) λ f →
         MP.cong (refl {x = gs}) λ g →
         P.sym $ pam-lemma xs g (pure ∘ f)) ⟩
    (fs >>= λ f → gs >>= λ g → pam (pam xs g) f)
      ≡⟨ MP.cong (refl {x = fs}) (λ f → MP.associative gs (pam xs) (pure ∘ f)) ⟩
    (fs >>= pam (gs >>= pam xs))
      ≡˘⟨ unfold-⊛ fs (gs >>= pam xs) ⟩
    fs ⊛ (gs >>= pam xs)
      ≡˘⟨ P.cong (fs ⊛_) (unfold-⊛ gs xs) ⟩
    fs ⊛ (gs ⊛ xs)
      ∎

  homomorphism : ∀ {ℓ} {A B : Set ℓ} (f : A → B) x →
                 (pure f ⊛ pure x) ≡ pure (f x)
  homomorphism f x = begin
    pure f ⊛ pure x            ≡⟨⟩
    (pure f >>= pam (pure x))  ≡⟨ MP.left-identity f (pam (pure x)) ⟩
    pam (pure x) f             ≡⟨ MP.left-identity x (pure ∘ f) ⟩
    pure (f x)                 ∎

  interchange : ∀ {ℓ} {A B : Set ℓ} (fs : List (A → B)) {x} →
                (fs ⊛ pure x) ≡ (pure (_$′ x) ⊛ fs)
  interchange fs {x} = begin
    fs ⊛ pure x                ≡⟨⟩
    (fs >>= pam (pure x))      ≡⟨ (MP.cong (refl {x = fs}) λ f →
                                      MP.left-identity x (pure ∘ f)) ⟩
    (fs >>= λ f → pure (f x))  ≡⟨⟩
    (pam fs (_$′ x))           ≡⟨ P.sym $ MP.left-identity (_$′ x) (pam fs) ⟩
    (pure (_$′ x) >>= pam fs)  ≡˘⟨ unfold-⊛ (pure (_$′ x)) fs ⟩
    pure (_$′ x) ⊛ fs          ∎
