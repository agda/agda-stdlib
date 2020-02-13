------------------------------------------------------------------------
-- The Agda standard library
--
-- The Cowriter type and some operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

-- Disabled to prevent warnings from BoundedVec
{-# OPTIONS --warn=noUserWarning #-}

module Codata.Cowriter where

open import Size
open import Level as L using (Level)
open import Codata.Thunk using (Thunk; force)
open import Codata.Conat
open import Codata.Delay using (Delay; later; now)
open import Codata.Stream as Stream using (Stream; _∷_)
open import Data.Unit
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Product as Prod using (_×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Vec.Bounded as Vec≤ using (Vec≤; _,_)
open import Function

private
  variable
    a b w x : Level
    A : Set a
    B : Set b
    W : Set w
    X : Set x

------------------------------------------------------------------------
-- Definition

data Cowriter (W : Set w) (A : Set a) (i : Size) : Set (a L.⊔ w) where
  [_] : A → Cowriter W A i
  _∷_ : W → Thunk (Cowriter W A) i → Cowriter W A i

------------------------------------------------------------------------
-- Relationship to Delay.

fromDelay : ∀ {i} → Delay A i → Cowriter ⊤ A i
fromDelay (now a)    = [ a ]
fromDelay (later da) = _ ∷ λ where .force → fromDelay (da .force)

toDelay : ∀ {i} → Cowriter W A i → Delay A i
toDelay [ a ]    = now a
toDelay (_ ∷ ca) = later λ where .force → toDelay (ca .force)

------------------------------------------------------------------------
-- Basic functions.

fromStream : ∀ {i} → Stream W i → Cowriter W A i
fromStream (w ∷ ws) = w ∷ λ where .force → fromStream (ws .force)

repeat : W → Cowriter W A ∞
repeat = fromStream ∘′ Stream.repeat

length : ∀ {i} → Cowriter W A i → Conat i
length [ _ ]    = zero
length (w ∷ cw) = suc λ where .force → length (cw .force)

splitAt : ∀ (n : ℕ) → Cowriter W A ∞ → (Vec W n × Cowriter W A ∞) ⊎ (Vec≤ W n × A)
splitAt zero    cw       = inj₁ ([] , cw)
splitAt (suc n) [ a ]    = inj₂ (Vec≤.[] , a)
splitAt (suc n) (w ∷ cw) = Sum.map (Prod.map₁ (w ∷_)) (Prod.map₁ (w Vec≤.∷_))
                         $ splitAt n (cw .force)

take : ∀ (n : ℕ) → Cowriter W A ∞ → Vec W n ⊎ (Vec≤ W n × A)
take n = Sum.map₁ Prod.proj₁ ∘′ splitAt n

infixr 5 _++_ _⁺++_
_++_ : ∀ {i} → List W → Cowriter W A i → Cowriter W A i
[]       ++ ca = ca
(w ∷ ws) ++ ca = w ∷ λ where .force → ws ++ ca

_⁺++_ : ∀ {i} → List⁺ W → Thunk (Cowriter W A) i → Cowriter W A i
(w ∷ ws) ⁺++ ca = w ∷ λ where .force → ws ++ ca .force

concat : ∀ {i} → Cowriter (List⁺ W) A i → Cowriter W A i
concat [ a ]    = [ a ]
concat (w ∷ ca) = w ⁺++ λ where .force → concat (ca .force)

------------------------------------------------------------------------
-- Functor, Applicative and Monad

map : ∀ {i} → (W → X) → (A → B) → Cowriter W A i → Cowriter X B i
map f g [ a ]    = [ g a ]
map f g (w ∷ cw) = f w ∷ λ where .force → map f g (cw .force)

map₁ : ∀ {i} → (W → X) → Cowriter W A i → Cowriter X A i
map₁ f = map f id

map₂ : ∀ {i} → (A → X) → Cowriter W A i → Cowriter W X i
map₂ = map id

ap : ∀ {i} → Cowriter W (A → X) i → Cowriter W A i → Cowriter W X i
ap [ f ]    ca = map₂ f ca
ap (w ∷ cf) ca = w ∷ λ where .force → ap (cf .force) ca

_>>=_ : ∀ {i} → Cowriter W A i → (A → Cowriter W X i) → Cowriter W X i
[ a ]    >>= f = f a
(w ∷ ca) >>= f = w ∷ λ where .force → ca .force >>= f

------------------------------------------------------------------------
-- Construction.

unfold : ∀ {i} → (X → (W × X) ⊎ A) → X → Cowriter W A i
unfold next seed with next seed
... | inj₁ (w , seed') = w ∷ λ where .force → unfold next seed'
... | inj₂ a           = [ a ]


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.3

open import Data.BoundedVec as BVec using (BoundedVec)

splitAt′ : ∀ (n : ℕ) → Cowriter W A ∞ → (Vec W n × Cowriter W A ∞) ⊎ (BoundedVec W n × A)
splitAt′ zero    cw       = inj₁ ([] , cw)
splitAt′ (suc n) [ a ]    = inj₂ (BVec.[] , a)
splitAt′ (suc n) (w ∷ cw) = Sum.map (Prod.map₁ (w ∷_)) (Prod.map₁ (w BVec.∷_))
                         $ splitAt′ n (cw .force)
{-# WARNING_ON_USAGE splitAt′
"Warning: splitAt′ (and Data.BoundedVec) was deprecated in v1.3.
Please use splitAt (and Data.Vec.Bounded) instead."
#-}

take′ : ∀ (n : ℕ) → Cowriter W A ∞ → Vec W n ⊎ (BoundedVec W n × A)
take′ n = Sum.map₁ Prod.proj₁ ∘′ splitAt′ n
{-# WARNING_ON_USAGE take′
"Warning: take′ (and Data.BoundedVec) was deprecated in v1.3.
Please use take (and Data.Vec.Bounded) instead."
#-}
