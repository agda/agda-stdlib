------------------------------------------------------------------------
-- The Agda standard library
--
-- Streams where every consecutive pair of elements is related
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Guarded.Stream.Relation.Unary.Linked {a} {A : Set a} where

open import Codata.Guarded.Stream as Stream using (Stream; head; tail)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Base using (id)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Binary.Construct.Intersection using () renaming (_∩_ to _∩ᵇ_)
open import Relation.Unary using (_⊆_) renaming (_∩_ to _∩ᵘ_)

private
  variable
    p q r ℓ : Level
    R : Rel A ℓ

infixr 5 _∷_

record Linked (R : Rel A ℓ) (xs : Stream A) : Set (a ⊔ ℓ) where
  coinductive
  constructor _∷_
  field
    head : R (head xs) (head (tail xs))
    tail : Linked R (tail xs)

open Linked public

map : {R : Rel A p} {S : Rel A q} → R ⇒ S → Linked R ⊆ Linked S
map R⇒S Rxs .head = R⇒S (head Rxs)
map R⇒S Rxs .tail = map R⇒S (tail Rxs)

module _ {P : Rel A p} {Q : Rel A q} {R : Rel A r} where

  zipWith : P ∩ᵇ Q ⇒ R → Linked P ∩ᵘ Linked Q ⊆ Linked R
  zipWith f (Pxs , Qxs) .head = f (head Pxs , head Qxs)
  zipWith f (Pxs , Qxs) .tail = zipWith f (tail Pxs , tail Qxs)

  unzipWith : R ⇒ P ∩ᵇ Q → Linked R ⊆ Linked P ∩ᵘ Linked Q
  unzipWith f Rxs .proj₁ .head = f (head Rxs) .proj₁
  unzipWith f Rxs .proj₁ .tail = unzipWith f (tail Rxs) .proj₁
  unzipWith f Rxs .proj₂ .head = f (head Rxs) .proj₂
  unzipWith f Rxs .proj₂ .tail = unzipWith f (tail Rxs) .proj₂

module _ {P : Rel A p} {Q : Rel A q} where

  zip : Linked P ∩ᵘ Linked Q ⊆ Linked (P ∩ᵇ Q)
  zip = zipWith id

  unzip : Linked (P ∩ᵇ Q) ⊆ Linked P ∩ᵘ Linked Q
  unzip = unzipWith id

lookup : ∀ {x xs} → Transitive R → Linked R xs
       → R x (head xs) → ∀ i → R x (Stream.lookup xs i)
lookup trans Rxs Rxh zero = Rxh
lookup trans Rxs Rxh (suc i) = lookup trans (tail Rxs) (trans Rxh (head Rxs)) i
