------------------------------------------------------------------------
-- The Agda standard library
--
-- The Cowriter type and some operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Cowriter where

open import Size
open import Level as L using (Level)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Conat
open import Codata.Sized.Delay using (Delay; later; now)
open import Codata.Sized.Stream as Stream using (Stream; _∷_)
open import Data.Unit.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty.Base using (List⁺; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Product.Base as Product using (_×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Vec.Bounded.Base as Vec≤ using (Vec≤; _,_)
open import Function.Base using (_$_; _∘′_; id)

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

infixr 5 _∷_

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
splitAt (suc n) (w ∷ cw) = Sum.map (Product.map₁ (w ∷_)) (Product.map₁ (w Vec≤.∷_))
                         $ splitAt n (cw .force)

take : ∀ (n : ℕ) → Cowriter W A ∞ → Vec W n ⊎ (Vec≤ W n × A)
take n = Sum.map₁ Product.proj₁ ∘′ splitAt n

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

infixl 1 _>>=_

_>>=_ : ∀ {i} → Cowriter W A i → (A → Cowriter W X i) → Cowriter W X i
[ a ]    >>= f = f a
(w ∷ ca) >>= f = w ∷ λ where .force → ca .force >>= f

------------------------------------------------------------------------
-- Construction.

unfold : ∀ {i} → (X → (W × X) ⊎ A) → X → Cowriter W A i
unfold next seed =
  Sum.[ (λ where (w , seed′) → w ∷ λ where .force → unfold next seed′)
      , [_]
      ] (next seed)
