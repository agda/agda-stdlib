------------------------------------------------------------------------
-- The Agda standard library
--
-- Helper function with regard to Instance arguments.
------------------------------------------------------------------------


module Instance where


it : ∀ {a} {A : Set a} {{x : A}} → A
it {{x}} = x
{-# INLINE it #-}

asInstance : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ {{x}} → B x) → B x
asInstance x f = f {{x}}
{-# INLINE asInstance #-}
