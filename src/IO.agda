------------------------------------------------------------------------
-- The Agda standard library
--
-- IO
------------------------------------------------------------------------

module IO (PrimIO : ∀ {a} → Set a → Set a) where

open import Coinduction
open import Data.Unit
open import Data.String
open import Data.Colist
open import Function
open import Level

------------------------------------------------------------------------
-- The IO monad

-- One cannot write "infinitely large" computations with the
-- postulated IO monad in IO.Primitive without turning off the
-- termination checker (or going via the FFI, or perhaps abusing
-- something else). The following coinductive deep embedding is
-- introduced to avoid this problem. Possible non-termination is
-- isolated to the run function below.

infixl 1 _>>=_ _>>_

data IO {a} (A : Set a) : Set (suc a) where
  lift   : (m : PrimIO A) → IO A
  return : (x : A) → IO A
  _>>=_  : {B : Set a} (m : ∞ (IO B)) (f : (x : B) → ∞ (IO A)) → IO A
  _>>_   : {B : Set a} (m₁ : ∞ (IO B)) (m₂ : ∞ (IO A)) → IO A

------------------------------------------------------------------------
-- Utilities

sequence : ∀ {a} {A : Set a} → Colist (IO A) → IO (Colist A)
sequence []       = return []
sequence (c ∷ cs) = ♯ c                  >>= λ x  →
                    ♯ (♯ sequence (♭ cs) >>= λ xs →
                    ♯ return (x ∷ ♯ xs))

-- The reason for not defining sequence′ in terms of sequence is
-- efficiency (the unused results could cause unnecessary memory use).

sequence′ : ∀ {a} {A : Set a} → Colist (IO A) → IO (Lift ⊤)
sequence′ []       = return _
sequence′ (c ∷ cs) = ♯ c                   >>
                     ♯ (♯ sequence′ (♭ cs) >>
                     ♯ return _)

mapM : ∀ {a b} {A : Set a} {B : Set b} →
       (A → IO B) → Colist A → IO (Colist B)
mapM f = sequence ∘ map f

mapM′ : {A B : Set} → (A → IO B) → Colist A → IO (Lift ⊤)
mapM′ f = sequence′ ∘ map f
