------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Pointwise.Base where

open import Data.Product.Base as Σ using (_×_; _,_; <_,_>; ∃-syntax)
open import Data.List.Base using (List; []; _∷_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (REL; _⇒_)

private
  variable
    a b c ℓ : Level
    A : Set a
    B : Set b
    C : Set c
    x y : A
    xs ys : List A
    R S : REL A B ℓ

------------------------------------------------------------------------
-- Definition
------------------------------------------------------------------------

infixr 5 _∷_

data Pointwise {A : Set a} {B : Set b} (R : REL A B ℓ)
               : List A → List B → Set (a ⊔ b ⊔ ℓ) where
  []  : Pointwise R [] []
  _∷_ : (x∼y : R x y) (xs∼ys : Pointwise R xs ys) →
        Pointwise R (x ∷ xs) (y ∷ ys)

------------------------------------------------------------------------
-- Operations
------------------------------------------------------------------------

head : Pointwise R (x ∷ xs) (y ∷ ys) → R x y
head (x∼y ∷ xs∼ys) = x∼y

tail : Pointwise R (x ∷ xs) (y ∷ ys) → Pointwise R xs ys
tail (x∼y ∷ xs∼ys) = xs∼ys

uncons : Pointwise R (x ∷ xs) (y ∷ ys) → R x y × Pointwise R xs ys
uncons = < head , tail >

rec : ∀ (P : ∀ {xs ys} → Pointwise R xs ys → Set c) →
      (∀ {x y xs ys} {Rxsys : Pointwise R xs ys} →
        (Rxy : R x y) → P Rxsys → P (Rxy ∷ Rxsys)) →
      P [] →
      ∀ {xs ys} (Rxsys : Pointwise R xs ys) → P Rxsys
rec P c n []            = n
rec P c n (Rxy ∷ Rxsys) = c Rxy (rec P c n Rxsys)

map : R ⇒ S → Pointwise R ⇒ Pointwise S
map R⇒S []            = []
map R⇒S (Rxy ∷ Rxsys) = R⇒S Rxy ∷ map R⇒S Rxsys

unzip : ∀ {r s} {R : REL A B r} {S : REL B C s} {xs zs} →
  Pointwise (λ x z → ∃[ y ] R x y × S y z) xs zs →
  ∃[ ys ] Pointwise R xs ys × Pointwise S ys zs
unzip [] = [] , [] , []
unzip ((y , r , s) ∷ xs∼zs) = Σ.map (y ∷_) (Σ.map (r ∷_) (s ∷_)) (unzip xs∼zs)
