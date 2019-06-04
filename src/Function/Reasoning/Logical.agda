------------------------------------------------------------------------
-- The Agda standard library
--
-- A module used for creating function pipelines, see
-- README.Function.Reasoning for examples
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Reasoning.Logical where

open import Function using (id)

------------------------------------------------------------------------
-- Combinators

infix -1 begin⟨_⟩_
infixr 0 ⇒_∴⟨_⟩_
infix 1 ⇒_∎

begin⟨_⟩_ : ∀ {a b} {A : Set a} {B : A → Set b} →
            (a : A) → (∀ a → B a) → B a
begin⟨ x ⟩ f = f x

⇒_∴⟨_⟩_ : ∀ {a b c} (A : Set a) {B : A → Set b} {C : A → Set c} →
          (∀ a → B a) → (∀ {a} → B a → C a) → (∀ a → C a)
(⇒ A ∴⟨ f ⟩ g) x = g (f x)

⇒_∎ : ∀ {a} (A : Set a) → (A → A)
⇒ A ∎ = id
