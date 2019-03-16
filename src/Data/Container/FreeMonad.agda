------------------------------------------------------------------------
-- The Agda standard library
--
-- The free monad construction on containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.FreeMonad where

open import Level
open import Data.Sum using (inj₁; inj₂ ; [_,_]′)
open import Data.Product
open import Data.Container
open import Data.Container.Combinator using (const; _⊎_)
open import Data.W
open import Category.Monad

infixl 1 _⋆C_
infix  1 _⋆_

------------------------------------------------------------------------
-- The free monad construction over a container and a set is, in
-- universal algebra terminology, also known as the term algebra over a
-- signature (a container) and a set (of variable symbols). The return
-- of the free monad corresponds to variables and the bind operator
-- corresponds to (parallel) substitution.

-- A useful intuition is to think of containers describing single
-- operations and the free monad construction over a container and a set
-- describing a tree of operations as nodes and elements of the set as
-- leafs. If one starts at the root, then any path will pass finitely
-- many nodes (operations described by the container) and eventually end
-- up in a leaf (element of the set) -- hence the Kleene star notation
-- (the type can be read as a regular expression).

_⋆C_ : ∀ {x s p} → Container s p → Set x → Container (s ⊔ x) p
C ⋆C X = const X ⊎ C

_⋆_ : ∀ {x s p} → Container s p → Set x → Set (x ⊔ s ⊔ p)
C ⋆ X = μ (C ⋆C X)

module _ {s p} {C : Container s p} where

  inn : ∀ {x} {X : Set x} → ⟦ C ⟧ (C ⋆ X) → C ⋆ X
  inn (s , f) = sup (inj₂ s , f)

  rawMonad : ∀ {x} → RawMonad {s ⊔ p ⊔ x} (C ⋆_)
  rawMonad = record { return = return; _>>=_ = _>>=_ }
    where
    return : ∀ {X} → X → C ⋆ X
    return x = sup (inj₁ x , λ ())

    _>>=_ : ∀ {X Y} → C ⋆ X → (X → C ⋆ Y) → C ⋆ Y
    sup (inj₁ x , _) >>= k = k x
    sup (inj₂ s , f) >>= k = inn (s , λ p → f p >>= k)
