------------------------------------------------------------------------
-- The Agda standard library
--
-- The Cowriter type and some operations
------------------------------------------------------------------------

module Codata.Cowriter where

open import Size
import Level as L
open import Codata.Thunk
open import Codata.Conat
open import Codata.Delay using (Delay; later; now)
open import Codata.Stream as Stream using (Stream; _∷_)

open import Data.Unit
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat.Base as Nat using (ℕ; zero; suc)
open import Data.Product as Prod using (_×_; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Data.BoundedVec as BVec using (BoundedVec)
open import Function

data Cowriter {w a} (W : Set w) (A : Set a) (i : Size) : Set (a L.⊔ w) where
  [_] : A → Cowriter W A i
  _∷_ : W → Thunk (Cowriter W A) i → Cowriter W A i

------------------------------------------------------------------------
-- Relationship to Delay.

module _ {a} {A : Set a} where

  fromDelay : ∀ {i} → Delay A i → Cowriter ⊤ A i
  fromDelay (now a)    = [ a ]
  fromDelay (later da) = _ ∷ λ where .force → fromDelay (da .force)

module _ {w a} {W : Set w} {A : Set a} where

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

  splitAt : ∀ (n : ℕ) → Cowriter W A ∞ → (Vec W n × Cowriter W A ∞) ⊎ (BoundedVec W n × A)
  splitAt zero    cw       = inj₁ ([] , cw)
  splitAt (suc n) [ a ]    = inj₂ (BVec.[] , a)
  splitAt (suc n) (w ∷ cw) = Sum.map (Prod.map₁ (w ∷_)) (Prod.map₁ (w BVec.∷_))
                           $ splitAt n (cw .force)

  take : ∀ (n : ℕ) → Cowriter W A ∞ → Vec W n ⊎ (BoundedVec W n × A)
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

module _ {w x a b} {W : Set w} {X : Set x} {A : Set a} {B : Set b} where

------------------------------------------------------------------------
-- Functor, Applicative and Monad

  map : ∀ {i} → (W → X) → (A → B) → Cowriter W A i → Cowriter X B i
  map f g [ a ]    = [ g a ]
  map f g (w ∷ cw) = f w ∷ λ where .force → map f g (cw .force)

module _ {w a r} {W : Set w} {A : Set a} {R : Set r} where

  map₁ : ∀ {i} → (W → R) → Cowriter W A i → Cowriter R A i
  map₁ f = map f id

  map₂ : ∀ {i} → (A → R) → Cowriter W A i → Cowriter W R i
  map₂ = map id

  ap : ∀ {i} → Cowriter W (A → R) i → Cowriter W A i → Cowriter W R i
  ap [ f ]    ca = map₂ f ca
  ap (w ∷ cf) ca = w ∷ λ where .force → ap (cf .force) ca

  _>>=_ : ∀ {i} → Cowriter W A i → (A → Cowriter W R i) → Cowriter W R i
  [ a ]    >>= f = f a
  (w ∷ ca) >>= f = w ∷ λ where .force → ca .force >>= f

------------------------------------------------------------------------
-- Construction.

module _ {w s a} {W : Set w} {S : Set s} {A : Set a} where

  unfold : ∀ {i} → (S → (W × S) ⊎ A) → S → Cowriter W A i
  unfold next seed with next seed
  ... | inj₁ (w , seed') = w ∷ λ where .force → unfold next seed'
  ... | inj₂ a           = [ a ]
