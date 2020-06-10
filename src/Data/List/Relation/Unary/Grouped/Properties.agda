------------------------------------------------------------------------
-- The Agda standard library
--
-- Property related to Grouped
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.Grouped.Properties where

open import Data.Bool using (true; false)
open import Data.List
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Grouped
open import Function using (_∘_; _⇔_; Equivalence)
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary as B using (REL; Rel)
open import Relation.Unary as U using (Pred)
open import Relation.Nullary using (¬_; does; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Level

private
  variable
    a b c p q : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- map

module _ (P : Rel A p) (Q : Rel B q) where

  map⁺ : ∀ {f xs} → (∀ {x y} → P x y ⇔ Q (f x) (f y)) → Grouped P xs → Grouped Q (map f xs)
  map⁺ {f} {[]} P⇔Q [] = []
  map⁺ {f} {x ∷ xs} P⇔Q (all[¬Px,xs] ∷≉ g) = aux all[¬Px,xs] ∷≉ map⁺ P⇔Q g where
    aux : ∀ {ys} → All (λ y → ¬ P x y) ys → All (λ y → ¬ Q (f x) y) (map f ys)
    aux [] = []
    aux (py ∷ pys) = py ∘ Equivalence.g P⇔Q ∷ aux pys
  map⁺ {f} {x₁ ∷ x₂ ∷ xs} P⇔Q (Px₁x₂ ∷≈ g) = Equivalence.f P⇔Q Px₁x₂ ∷≈ map⁺ P⇔Q g

  map⁻ : ∀ {f xs} → (∀ {x y} → P x y ⇔ Q (f x) (f y)) → Grouped Q (map f xs) → Grouped P xs
  map⁻ {f} {[]} P⇔Q [] = []
  map⁻ {f} {x ∷ []} P⇔Q ([] ∷≉ []) = [] ∷≉ []
  map⁻ {f} {x₁ ∷ x₂ ∷ xs} P⇔Q (all[¬Qx,xs] ∷≉ g) = aux all[¬Qx,xs] ∷≉ map⁻ P⇔Q g where
    aux : ∀ {ys} → All (λ y → ¬ Q (f x₁) y) (map f ys) → All (λ y → ¬ P x₁ y) ys
    aux {[]} [] = []
    aux {y ∷ ys} (py ∷ pys) = py ∘ Equivalence.f P⇔Q ∷ aux pys
  map⁻ {f} {x₁ ∷ x₂ ∷ xs} P⇔Q (Qx₁x₂ ∷≈ g) = Equivalence.g P⇔Q Qx₁x₂ ∷≈ map⁻ P⇔Q g

------------------------------------------------------------------------
-- [_]

module _ (P : Rel A p) where

  [_]⁺ : ∀ x → Grouped P [ x ]
  [_]⁺ x = [] ∷≉ []

------------------------------------------------------------------------
-- derun

module _ {P : Rel A p} (P? : B.Decidable P) where

  grouped[xs]⇒unique[derun[xs]] : ∀ xs → Grouped P xs → AllPairs (λ x y → ¬ P x y) (derun P? xs)
  grouped[xs]⇒unique[derun[xs]] [] [] = []
  grouped[xs]⇒unique[derun[xs]] (x ∷ []) ([] ∷≉ []) = [] ∷ []
  grouped[xs]⇒unique[derun[xs]] (x ∷ y ∷ xs) (all[¬Px,y∷xs]@(¬Pxy ∷ _) ∷≉ grouped[y∷xs]) with P? x y
  ... | yes Pxy  = contradiction Pxy ¬Pxy
  ... | no  _    = All.derun⁺ P? all[¬Px,y∷xs] ∷ grouped[xs]⇒unique[derun[xs]] (y ∷ xs) grouped[y∷xs]
  grouped[xs]⇒unique[derun[xs]] (x ∷ y ∷ xs) (Pxy ∷≈ grouped[xs]) with P? x y
  ... | yes _    = grouped[xs]⇒unique[derun[xs]] (y ∷ xs) grouped[xs]
  ... | no  ¬Pxy = contradiction Pxy ¬Pxy
