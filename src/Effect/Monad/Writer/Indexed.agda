------------------------------------------------------------------------
-- The Agda standard library
--
-- The indexed writer monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Effect.Monad.Writer.Indexed (a : Level) where

open import Algebra using (RawMonoid)
open import Data.Product.Base using (_×_; _,_; map₁)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Effect.Applicative.Indexed
  using (IFun; RawIApplicative; RawIApplicativeZero; RawIAlternative)
open import Effect.Monad.Indexed
  using (RawIMonad; RawIMonadZero; RawIMonadPlus)
open import Function.Base using (_∘′_)
open import Function.Identity.Effectful as Id using (Identity)

private
  variable
    w ℓ : Level
    A B I : Set ℓ

------------------------------------------------------------------------
-- Indexed writer

IWriterT : (𝕎 : RawMonoid w ℓ) → IFun I (w ⊔ a) → IFun I (w ⊔ a)
IWriterT 𝕎 M i j A = M i j (RawMonoid.Carrier 𝕎 × A)

module _ {M : IFun I (w ⊔ a)} {𝕎 : RawMonoid w ℓ} where

  open RawMonoid 𝕎 renaming (Carrier to W)

  ----------------------------------------------------------------------
  -- Indexed writer applicative

  WriterTIApplicative : RawIApplicative M → RawIApplicative (IWriterT 𝕎 M)
  WriterTIApplicative App = record
    { pure = λ x → pure (ε , x)
    ; _⊛_ = λ m n → go <$> m ⊛ n
    } where
        open RawIApplicative App
        go : W × (A → B) → W × A → W × B
        go (w₁ , f) (w₂ , x) = w₁ ∙ w₂ , f x

  WriterTIApplicativeZero : RawIApplicativeZero M →
                            RawIApplicativeZero (IWriterT 𝕎 M)
  WriterTIApplicativeZero App = record
    { applicative = WriterTIApplicative applicative
    ; ∅ = ∅
    } where open RawIApplicativeZero App

  WriterTIAlternative : RawIAlternative M → RawIAlternative (IWriterT 𝕎 M)
  WriterTIAlternative Alt = record
    { applicativeZero = WriterTIApplicativeZero applicativeZero
    ; _∣_ = _∣_
    } where open RawIAlternative Alt

  ----------------------------------------------------------------------
  -- Indexed writer monad

  WriterTIMonad : RawIMonad M → RawIMonad (IWriterT 𝕎 M)
  WriterTIMonad Mon = record
    { return = λ x → return (ε , x)
    ; _>>=_ = λ m f → do
        w₁ , x  ← m
        w₂ , fx ← f x
        return (w₁ ∙ w₂ , fx)
    } where open RawIMonad Mon

  WriterTIMonadZero : RawIMonadZero M → RawIMonadZero (IWriterT 𝕎 M)
  WriterTIMonadZero Mon = record
    { monad = WriterTIMonad monad
    ; applicativeZero = WriterTIApplicativeZero applicativeZero
    } where open RawIMonadZero Mon

  WriterTIMonadPlus : RawIMonadPlus M → RawIMonadPlus (IWriterT 𝕎 M)
  WriterTIMonadPlus Mon = record
    { monad = WriterTIMonad monad
    ; alternative = WriterTIAlternative alternative
    } where open RawIMonadPlus Mon

------------------------------------------------------------------------
-- Writer monad operations

record RawIMonadWriter {I : Set ℓ} (𝕎 : RawMonoid w ℓ) (M : IFun I (w ⊔ a))
                       : Set (ℓ ⊔ suc (w ⊔ a)) where
  open RawMonoid 𝕎 renaming (Carrier to W)
  field
    monad  : RawIMonad M
    writer : ∀ {i} → (W × A) → M i i A
    listen : ∀ {i j} → M i j A → M i j (W × A)
    pass   : ∀ {i j} → M i j ((W → W) × A) → M i j A

  open RawIMonad monad public

  tell : ∀ {i} → W → M i i ⊤
  tell = writer ∘′ (_, tt)

  listens : ∀ {i j} {Z : Set w} → (W → Z) → M i j A → M i j (Z × A)
  listens f m = listen m >>= return ∘′ map₁ f

  censor : ∀ {i j} → (W → W) → M i j A → M i j A
  censor f m = pass (m >>= return ∘′ (f ,_))


WriterTIMonadWriter : {I : Set ℓ} {𝕎 : RawMonoid w ℓ} {M : IFun I (w ⊔ a)} →
                      RawIMonad M → RawIMonadWriter 𝕎 (IWriterT 𝕎 M)
WriterTIMonadWriter {𝕎 = 𝕎} Mon = record
  { monad = WriterTIMonad {𝕎 = 𝕎} Mon
  ; writer = return
  ; listen = λ m → do
      w , a ← m
      return (w , w , a)
  ; pass = λ m → do
      w , f , a ← m
      return (f w , a)
  } where open RawIMonad Mon
          open RawMonoid 𝕎 renaming (Carrier to W)
