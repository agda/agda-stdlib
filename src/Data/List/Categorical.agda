------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of List
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Categorical where

open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Data.Bool.Base using (false; true)
open import Data.List.Base
open import Data.List.Properties
open import Function
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; _≗_; refl)
open P.≡-Reasoning

------------------------------------------------------------------------
-- List applicative functor

functor : ∀ {ℓ} → RawFunctor {ℓ} List
functor = record { _<$>_ = map }

applicative : ∀ {ℓ} → RawApplicative {ℓ} List
applicative = record
  { pure = [_]
  ; _⊛_  = λ fs as → concatMap (λ f → map f as) fs
  }

applicativeZero : ∀ {ℓ} → RawApplicativeZero {ℓ} List
applicativeZero = record
  { applicative = applicative
  ; ∅           = []
  }

alternative : ∀ {ℓ} → RawAlternative {ℓ} List
alternative = record
  { applicativeZero = applicativeZero
  ; _∣_             = _++_
  }

------------------------------------------------------------------------
-- List monad

monad : ∀ {ℓ} → RawMonad {ℓ} List
monad = record
  { return = [_]
  ; _>>=_  = flip concatMap
  }

monadZero : ∀ {ℓ} → RawMonadZero {ℓ} List
monadZero = record
  { monad           = monad
  ; applicativeZero = applicativeZero
  }

monadPlus : ∀ {ℓ} → RawMonadPlus {ℓ} List
monadPlus = record
  { monad = monad
  ; alternative = alternative
  }

------------------------------------------------------------------------
-- Get access to other monadic functions

module TraversableA {f F} (App : RawApplicative {f} F) where

  open RawApplicative App

  sequenceA : ∀ {A} → List (F A) → F (List A)
  sequenceA []       = pure []
  sequenceA (x ∷ xs) = _∷_ <$> x ⊛ sequenceA xs

  mapA : ∀ {a} {A : Set a} {B} → (A → F B) → List A → F (List B)
  mapA f = sequenceA ∘ map f

  forA : ∀ {a} {A : Set a} {B} → List A → (A → F B) → F (List B)
  forA = flip mapA

module TraversableM {m M} (Mon : RawMonad {m} M) where

  open RawMonad Mon

  open TraversableA rawIApplicative public
    renaming
    ( sequenceA to sequenceM
    ; mapA      to mapM
    ; forA      to forM
    )

------------------------------------------------------------------------
-- List monad transformer

monadT : ∀ {ℓ} → RawMonadT {ℓ} (_∘′ List)
monadT M = record
  { return = pure ∘′ [_]
  ; _>>=_  = λ mas f → mas >>= λ as → concat <$> mapM f as
  } where open RawMonad M; open TraversableM M

------------------------------------------------------------------------
-- The list monad.

private
  open module LMP {ℓ} = RawMonadPlus (monadPlus {ℓ = ℓ})

module MonadProperties where

  left-identity : ∀ {ℓ} {A B : Set ℓ} (x : A) (f : A → List B) →
                  (return x >>= f) ≡ f x
  left-identity x f = ++-identityʳ (f x)

  right-identity : ∀ {ℓ} {A : Set ℓ} (xs : List A) →
                   (xs >>= return) ≡ xs
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
      let xs = true ∷ false ∷ []; f = return; g = return in
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
    pam xs f = xs >>= return ∘ f

  -- ∅ is a left zero for _⊛_.

  left-zero : ∀ {ℓ} {A B : Set ℓ} (xs : List A) → (∅ ⊛ xs) ≡ ∅ {A = B}
  left-zero xs = begin
    ∅ ⊛ xs          ≡⟨⟩
    (∅ >>= pam xs)  ≡⟨ MonadProperties.left-zero (pam xs) ⟩
    ∅               ∎

  -- ∅ is a right zero for _⊛_.

  right-zero : ∀ {ℓ} {A B : Set ℓ} (fs : List (A → B)) → (fs ⊛ ∅) ≡ ∅
  right-zero {ℓ} fs = begin
    fs ⊛ ∅            ≡⟨⟩
    (fs >>= pam ∅)    ≡⟨ (MP.cong (refl {x = fs}) λ f →
                          MP.left-zero (return ∘ f)) ⟩
    (fs >>= λ _ → ∅)  ≡⟨ MP.right-zero fs ⟩
    ∅                 ∎

  -- _⊛_ distributes over _∣_ from the right.

  right-distributive : ∀ {ℓ} {A B : Set ℓ} (fs₁ fs₂ : List (A → B)) xs →
                       ((fs₁ ∣ fs₂) ⊛ xs) ≡ (fs₁ ⊛ xs ∣ fs₂ ⊛ xs)
  right-distributive fs₁ fs₂ xs = begin
    (fs₁ ∣ fs₂) ⊛ xs                     ≡⟨⟩
    (fs₁ ∣ fs₂ >>= pam xs)               ≡⟨ MonadProperties.right-distributive fs₁ fs₂ (pam xs) ⟩
    (fs₁ >>= pam xs) ∣ (fs₂ >>= pam xs)  ≡⟨⟩
    (fs₁ ⊛ xs ∣ fs₂ ⊛ xs)                ∎

  -- _⊛_ does not distribute over _∣_ from the left.

  private

    not-left-distributive :
      let fs = id ∷ id ∷ []; xs₁ = true ∷ []; xs₂ = true ∷ false ∷ [] in
      (fs ⊛ (xs₁ ∣ xs₂)) ≢ (fs ⊛ xs₁ ∣ fs ⊛ xs₂)
    not-left-distributive ()

  -- Applicative functor laws.

  identity : ∀ {a} {A : Set a} (xs : List A) → (return id ⊛ xs) ≡ xs
  identity xs = begin
    return id ⊛ xs          ≡⟨⟩
    (return id >>= pam xs)  ≡⟨ MonadProperties.left-identity id (pam xs) ⟩
    (xs >>= return)         ≡⟨ MonadProperties.right-identity xs ⟩
    xs                      ∎

  private

    pam-lemma : ∀ {ℓ} {A B C : Set ℓ}
                (xs : List A) (f : A → B) (fs : B → List C) →
                (pam xs f >>= fs) ≡ (xs >>= λ x → fs (f x))
    pam-lemma xs f fs = begin
      (pam xs f >>= fs)                   ≡⟨ P.sym $ MP.associative xs (return ∘ f) fs ⟩
      (xs >>= λ x → return (f x) >>= fs)  ≡⟨ MP.cong (refl {x = xs}) (λ x → MP.left-identity (f x) fs) ⟩
      (xs >>= λ x → fs (f x))             ∎

  composition : ∀ {ℓ} {A B C : Set ℓ}
                (fs : List (B → C)) (gs : List (A → B)) xs →
                (return _∘′_ ⊛ fs ⊛ gs ⊛ xs) ≡ (fs ⊛ (gs ⊛ xs))
  composition {ℓ} fs gs xs = begin
    return _∘′_ ⊛ fs ⊛ gs ⊛ xs                      ≡⟨⟩
    (return _∘′_ >>= pam fs >>= pam gs >>= pam xs)  ≡⟨ MP.cong (MP.cong (MP.left-identity _∘′_ (pam fs))
                                                                              (λ f → refl {x = pam gs f}))
                                                                  (λ fg → refl {x = pam xs fg}) ⟩
    (pam fs _∘′_ >>= pam gs >>= pam xs)             ≡⟨ MP.cong (pam-lemma fs _∘′_ (pam gs)) (λ _ → refl) ⟩
    ((fs >>= λ f → pam gs (f ∘′_)) >>= pam xs)      ≡⟨ P.sym $ MP.associative fs (λ f → pam gs (_∘′_ f)) (pam xs) ⟩
    (fs >>= λ f → pam gs (f ∘′_) >>= pam xs)        ≡⟨ (MP.cong (refl {x = fs}) λ f →
                                                        pam-lemma gs (f ∘′_) (pam xs)) ⟩
    (fs >>= λ f → gs >>= λ g → pam xs (f ∘′ g))     ≡⟨ (MP.cong (refl {x = fs}) λ f →
                                                        MP.cong (refl {x = gs}) λ g →
                                                        P.sym $ pam-lemma xs g (return ∘ f)) ⟩
    (fs >>= λ f → gs >>= λ g → pam (pam xs g) f)    ≡⟨ (MP.cong (refl {x = fs}) λ f →
                                                        MP.associative gs (pam xs) (return ∘ f)) ⟩
    (fs >>= pam (gs >>= pam xs))                    ≡⟨⟩
    fs ⊛ (gs ⊛ xs)                                  ∎

  homomorphism : ∀ {ℓ} {A B : Set ℓ} (f : A → B) x →
                 (return f ⊛ return x) ≡ return (f x)
  homomorphism f x = begin
    return f ⊛ return x            ≡⟨⟩
    (return f >>= pam (return x))  ≡⟨ MP.left-identity f (pam (return x)) ⟩
    pam (return x) f               ≡⟨ MP.left-identity x (return ∘ f) ⟩
    return (f x)                   ∎

  interchange : ∀ {ℓ} {A B : Set ℓ} (fs : List (A → B)) {x} →
                (fs ⊛ return x) ≡ (return (λ f → f x) ⊛ fs)
  interchange fs {x} = begin
    fs ⊛ return x                    ≡⟨⟩
    (fs >>= pam (return x))          ≡⟨ (MP.cong (refl {x = fs}) λ f →
                                         MP.left-identity x (return ∘ f)) ⟩
    (fs >>= λ f → return (f x))      ≡⟨⟩
    (pam fs (λ f → f x))             ≡⟨ P.sym $ MP.left-identity (λ f → f x) (pam fs) ⟩
    (return (λ f → f x) >>= pam fs)  ≡⟨⟩
    return (λ f → f x) ⊛ fs          ∎
