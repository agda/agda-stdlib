------------------------------------------------------------------------
-- The Agda standard library
--
-- The free monad construction on containers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Container.FreeMonad where

open import Level using (Level; _⊔_)
open import Data.Sum.Base using (inj₁; inj₂ ; [_,_]′)
open import Data.Product using (_,_; -,_)
open import Data.Container using (Container; ⟦_⟧; μ)
open import Data.Container.Relation.Unary.All using (□; all)
open import Data.Container.Combinator using (const; _⊎_)
open import Data.W as W using (sup)
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)
open import Function.Base as Function using (_$_; _∘_)

variable
  x y s p ℓ : Level
  C : Container s p
  X : Set x
  Y : Set y

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
-- leaves. If one starts at the root, then any path will pass finitely
-- many nodes (operations described by the container) and eventually end
-- up in a leaf (element of the set) -- hence the Kleene star notation
-- (the type can be read as a regular expression).

------------------------------------------------------------------------
-- Type definition

-- The free moand can be defined as the least fixpoint `μ (C ⋆C X)`

_⋆C_ : ∀ {x s p} → Container s p → Set x → Container (s ⊔ x) p
C ⋆C X = const X ⊎ C

-- However Agda's positivity checker is currently too weak to observe
-- that `X` is used in a strictly positive manner in `μ (C ⋆C X)` as
-- demonstrated in #693.
-- So we provide instead an inductive definition that we prove to be
-- equivalent to the μ-based one.

data _⋆_ (C : Container s p) (X : Set x) : Set (x ⊔ s ⊔ p) where
  pure : X → C ⋆ X
  impure : ⟦ C ⟧ (C ⋆ X) → C ⋆ X

------------------------------------------------------------------------
-- Equivalent types

-- We can prove that `C ⋆ X` is equivalent to one layer of `C ⋆C X` with
-- subterms of tyep `C ⋆ X`.

inj : {X : Set x} → ⟦ C ⋆C X ⟧ (C ⋆ X) → C ⋆ X
inj (inj₁ x , _) = pure x
inj (inj₂ c , r) = impure (c , r)

out : {X : Set x} → C ⋆ X → ⟦ C ⋆C X ⟧ (C ⋆ X)
out (pure x) = inj₁ x , λ ()
out (impure (c , r)) = inj₂ c , r

-- We can fully convert back and forth between `C ⋆ X` and `μ (C ⋆C X)`.

toμ : C ⋆ X → μ (C ⋆C X)
toμ (pure x) = sup (inj₁ x , λ ())
toμ (impure (c , r)) = sup (inj₂ c , toμ ∘ r)

fromμ : μ (C ⋆C X) → C ⋆ X
fromμ = W.foldr inj

-- We can recover an induction principle similar to the one given in `Data.W`.
-- We curry these ones by distinguishing the pure vs. impure case

module _ (P : C ⋆ X → Set ℓ)
         (algP : ∀ x → P (pure x))
         (algI : ∀ {t} → □ C P t → P (impure t)) where

 induction : (t : C ⋆ X) → P t
 induction (pure x) = algP x
 induction (impure (c , r)) = algI $ all (induction ∘ r)

module _ {P : Set ℓ}
         (algP : X → P)
         (algI : ⟦ C ⟧ P → P) where

 foldr : C ⋆ X → P
 foldr = induction (Function.const P) algP (algI ∘ -,_ ∘ □.proof)

infixr -1 _<$>_ _<*>_
infixl 1 _>>=_

_<$>_ : (X → Y) → C ⋆ X → C ⋆ Y
f <$> t = foldr (pure ∘ f) impure t

_<*>_ : C ⋆ (X → Y) → C ⋆ X → C ⋆ Y
pure f <*> t = f <$> t
impure (c , r) <*> t = impure (c , λ v → r v <*> t)

_>>=_ : C ⋆ X → (X → C ⋆ Y) → C ⋆ Y
pure x >>= f = f x
impure (c , r) >>= f = impure (c , λ v → r v >>= f)

------------------------------------------------------------------------
-- Structure

functor : RawFunctor (_⋆_ {x = x} C)
functor = record { _<$>_ = _<$>_ }

applicative : {C : Container s p} → RawApplicative (_⋆_ {x = x ⊔ s ⊔ p} C)
applicative = record
  { rawFunctor = functor
  ; pure = pure
  ; _<*>_ = _<*>_ }

monad : {C : Container s p} → RawMonad (_⋆_ {x = x ⊔ s ⊔ p} C)
monad {x = x} = record
  { rawApplicative = applicative {x = x}
  ; _>>=_ = _>>=_
  }

------------------------------------------------------------------------
-- DEPRECATIONS

rawFunctor = functor
{-# WARNING_ON_USAGE rawFunctor
"Warning: all rawFunctor deprecated in v2.0.
Please use functor instead."
#-}

rawApplicative = applicative
{-# WARNING_ON_USAGE rawApplicative
"Warning: rawApplicative was deprecated in v2.0.
Please use applicative instead."
#-}

rawMonad = monad
{-# WARNING_ON_USAGE rawMonad
"Warning: rawMonad was deprecated in v2.0.
Please use monad instead."
#-}
