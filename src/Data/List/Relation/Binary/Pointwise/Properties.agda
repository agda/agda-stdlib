------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of pointwise lifting of relations to lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Pointwise.Properties where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (zero; suc; cast)
open import Data.Product.Base using (_,_; uncurry)
open import Data.List.Base using (List; []; _∷_; length; lookup)
open import Level
open import Relation.Binary.Core using (REL; _⇒_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Nullary using (yes; no; _×?_)
import Relation.Nullary.Decidable as Dec

open import Data.List.Relation.Binary.Pointwise.Base

private
  variable
    a b ℓ : Level
    A : Set a
    B : Set b
    R S T : REL A B ℓ

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
respects₂ (rˡ , rʳ) = respˡ rˡ , respʳ rʳ

decidable : Decidable R → Decidable (Pointwise R)
decidable _  []       []       = yes []
decidable _  []       (y ∷ ys) = no λ()
decidable _  (x ∷ xs) []       = no λ()
decidable R? (x ∷ xs) (y ∷ ys) = Dec.map′ (uncurry _∷_) uncons
  (R? x y ×? decidable R? xs ys)

irrelevant : Irrelevant R → Irrelevant (Pointwise R)
irrelevant irr []       []         = ≡.refl
irrelevant irr (r ∷ rs) (r₁ ∷ rs₁) =
  ≡.cong₂ _∷_ (irr r r₁) (irrelevant irr rs rs₁)

Pointwise-length : ∀ {xs ys} → Pointwise R xs ys → length xs ≡ length ys
Pointwise-length []            = ≡.refl
Pointwise-length (x∼y ∷ xs∼ys) = ≡.cong ℕ.suc (Pointwise-length xs∼ys)

lookup-cast : ∀ {xs ys} →
              Pointwise R xs ys →
              .(∣xs∣≡∣ys∣ : length xs ≡ length ys) →
              ∀ i →
              R (lookup xs i) (lookup ys (cast ∣xs∣≡∣ys∣ i))
lookup-cast (Rxy ∷ Rxsys) _ zero = Rxy
lookup-cast (Rxy ∷ Rxsys) _ (suc i) = lookup-cast Rxsys _ i
