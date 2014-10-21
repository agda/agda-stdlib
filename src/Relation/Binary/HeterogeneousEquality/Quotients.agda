------------------------------------------------------------------------
-- The Agda standard library
--
-- Quotients for Heterogeneous equality
------------------------------------------------------------------------

module Relation.Binary.HeterogeneousEquality.Quotients where

open import Function
open import Level hiding (lift)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning

record Quotient {c ℓ} (S : Setoid c ℓ) : Set (suc (c ⊔ ℓ)) where
  open Setoid S renaming (Carrier to A)
  field 
    Q   : Set c
    abs : A → Q 

  compat : {B : Q → Set c} → ((a : A) → B (abs a)) → Set (c ⊔ ℓ)
  compat f = {a a′ : A} → a ≈ a′ → f a ≅ f a′
     
  field 
    absCompat : compat abs
    lift      : {B : Q → Set c}(f : (a : A) → B (abs a)) → compat {B} f →
                (q : Q) → B q
    liftConv  : {B : Q → Set c}(f : (a : A) → B (abs a))(p : compat {B} f)
                (a : A) → lift {B} f p (abs a) ≅ f a

Quotients : ∀{c ℓ} → Set (suc  (c ⊔ ℓ))
Quotients {c}{ℓ} = (S : Setoid c ℓ) → Quotient S

module _ {c}{ℓ}(S : Setoid c ℓ)(Qu : Quotient S) where

  open Setoid S renaming (Carrier to A) hiding (refl; sym; trans)
  open Quotient Qu

  liftUniqueness : {B : Q → Set c}
                   (f : (a : A) → B (abs a)) → (p : compat {B} f)
                   (g : (x : Q) → B x) → ((a : A) → g (abs a) ≅ f a) → 
                   ∀ x → lift {B} f p x ≅ g x
  liftUniqueness f p g r = lift (λ x →  
    begin
    lift f p (abs x)
    ≅⟨ liftConv f p x ⟩
    f x
    ≅⟨ sym (r x) ⟩
    g (abs x)
    ∎) 
    λ p' → hir (cong (lift f p) (absCompat p'))

  liftAbs : ∀ x → lift {λ _ → Q} abs absCompat x ≅ x
  liftAbs = liftUniqueness abs absCompat id (λ _ → refl)

  liftCong : {B : Q → Set c}{f g : (a : A) → B (abs a)}
             {p : compat {B} f}{p' : compat {B} g} → (∀ x → f x ≅ g x) → 
             ∀ x → lift {B} f p x ≅ lift {B} g p' x
  liftCong {B}{f}{g}{p}{p'} h = 
    liftUniqueness f p (lift g p') (λ a → trans (liftConv g p' a) (sym (h a)))

  isLift : {B : Q → Set c}(f : (x : Q) → B x) → 
           ∀ x → lift (f ∘ abs) (cong f ∘ absCompat) x ≅ f x
  isLift f = 
    liftUniqueness (f ∘ abs) (cong f ∘ absCompat) f (λ _ → refl)

  absEpi : {B : Q → Set c}{f g : (x : Q) → B x} → 
           (∀ x → f (abs x) ≅ g (abs x)) → ∀ x → f x ≅ g x
  absEpi {f = f}{g = g} p x = 
    begin
    f x
    ≅⟨ sym (isLift f x) ⟩
    lift (f ∘ abs) (cong f ∘ absCompat) x
    ≅⟨ liftCong p x ⟩
    lift (g ∘ abs) (cong g ∘ absCompat) x
    ≅⟨ isLift g x ⟩
    g x
    ∎

