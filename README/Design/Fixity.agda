------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation describing some of the fixity choices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- There is no actual code in here, just design note.

module README.Design.Fixity where


-- binary relations of all kinds are infix 4
-- multiplication-like: infixl 7 _*_
-- addition-like  infixl 6 _+_
-- negation-like  infix  8 ¬_
-- and-like  infixr 7 _∧_
-- or-like  infixr 6 _∨_
-- post-fix inverse  infix  8 _⁻¹
-- bind infixl 1 _>>=_
-- list concat-like infixr 5 _∷_
-- ternary reasoning infix 1 _⊢_≈_
-- composition infixr 9 _∘_
-- application infixr -1 _$_ _$!_

-- Reasoning:
-- QED  infix  3 _∎
-- stepping  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
-- begin  infix  1 begin_

-- type formers:
-- product-like infixr 2 _×_ _-×-_ _-,-_
-- sum-like infixr 1 _⊎_
