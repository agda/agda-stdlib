------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for functional reasoning
------------------------------------------------------------------------

module Function.FunctionalReasoning where

-- Example use

-- 2*even : ∀ n → Even (2 * n)
-- 2*even zero    = ezero
-- 2*even (suc n) =
--  begin⟦ 2*even n ⟧
--    Even (2 * n)
--  ─ id ⟶
--    Even (n + (n + zero))
--  ─ esuc ⟶
--    Even (suc (suc (n + (n + zero))))
--  ─ id ⟶
--    Even (suc ((suc n) + (n + zero)))
--  ─ subst Even (cong (λ m → suc (m + (n + 0))) (+-comm 1 n)) ⟶
--    Even (suc ((n + 1) + (n + zero)))
--  ─ subst Even (cong suc (+-assoc n 1 _)) ⟶
--    Even (suc (n + suc (n + 0)))
--  ∎

open import Function

infix 4 _∎
infixr 3 _─_⟶_ _─_⟶'_
infix 2 begin⟦_⟧_

_∎ : ∀ {a} → (A : Set a) → A → A
_∎ _ = id

begin⟦_⟧_ : ∀ {a b} {A : Set a} → (a : A) → {B : A → Set b} →
            ((x : A) → B x) → B a
begin⟦ a ⟧ f = f a

_─_⟶_ : ∀ {a b c} (A : Set a) → {B : A → Set b} → (f : (a : A) → B a) →
        {C : {a : A} → (b : B a) → Set c} → (∀ {a} → (b : B a) → C b) →
        (a : A) → C (f a)
A ─ f ⟶ g = g ∘ f

_─_⟶'_ : ∀ {a b c} (A : Set a) {B : Set b} → (A → B) →
        {C : Set c} → (B → C) → (A → C)
A ─ f ⟶' g = g ∘ f
