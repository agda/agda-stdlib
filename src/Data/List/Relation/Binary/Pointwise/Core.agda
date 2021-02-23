------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Pointwise.Core where

open import Data.Product using (_×_; _,_; <_,_>)
open import Data.List.Base as List hiding (map; head; tail; uncons)
open import Level
open import Relation.Binary.Core using (REL; _⇒_)
open import Relation.Binary.Definitions

private
  variable
    a b c d p q ℓ ℓ₁ ℓ₂ : Level
    A B C D : Set d
    x y z : A
    ws xs ys zs : List A
    R S T : REL A B ℓ

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

------------------------------------------------------------------------
-- Relational properties
------------------------------------------------------------------------

reflexive : R ⇒ S → Pointwise R ⇒ Pointwise S
reflexive = map

refl : Reflexive R → Reflexive (Pointwise R)
refl rfl {[]}     = []
refl rfl {x ∷ xs} = rfl ∷ refl rfl

symmetric : Sym R S → Sym (Pointwise R) (Pointwise S)
symmetric sym []            = []
symmetric sym (x∼y ∷ xs∼ys) = sym x∼y ∷ symmetric sym xs∼ys

transitive : Trans R S T →
             Trans (Pointwise R) (Pointwise S) (Pointwise T)
transitive trans []            []            = []
transitive trans (x∼y ∷ xs∼ys) (y∼z ∷ ys∼zs) =
  trans x∼y y∼z ∷ transitive trans xs∼ys ys∼zs

antisymmetric : Antisym R S T →
                Antisym (Pointwise R) (Pointwise S) (Pointwise T)
antisymmetric antisym []            []            = []
antisymmetric antisym (x∼y ∷ xs∼ys) (y∼x ∷ ys∼xs) =
  antisym x∼y y∼x ∷ antisymmetric antisym xs∼ys ys∼xs

respʳ : R Respectsʳ S → (Pointwise R) Respectsʳ (Pointwise S)
respʳ resp []            []            = []
respʳ resp (x≈y ∷ xs≈ys) (z∼x ∷ zs∼xs) = resp x≈y z∼x ∷ respʳ resp xs≈ys zs∼xs

respˡ : R Respectsˡ S → (Pointwise R) Respectsˡ (Pointwise S)
respˡ resp []            []            = []
respˡ resp (x≈y ∷ xs≈ys) (x∼z ∷ xs∼zs) = resp x≈y x∼z ∷ respˡ resp xs≈ys xs∼zs

respects₂ : R Respects₂ S → (Pointwise R) Respects₂ (Pointwise S)
respects₂ (rʳ , rˡ) = respʳ rʳ , respˡ rˡ
