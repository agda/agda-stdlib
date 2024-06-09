------------------------------------------------------------------------
-- The Agda standard library
--
-- Property related to Grouped
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Grouped.Properties where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using ([]; [_]; _∷_; map; derun)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Grouped
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_; _on_)
open import Level using (Level)
open import Relation.Binary.Definitions as B
open import Relation.Binary.Core using (_⇔_; REL; Rel)
open import Relation.Unary as U using (Pred)
open import Relation.Nullary.Decidable.Core using (does; yes; no)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

private
  variable
    a b c p q : Level
    A B C : Set a

------------------------------------------------------------------------
-- map

module _ (P : Rel A p) (Q : Rel B q) where

  map⁺ : ∀ {f xs} → P ⇔ (Q on f) → Grouped P xs → Grouped Q (map f xs)
  map⁺ P⇔Q            []                      = []
  map⁺ P⇔Q@(_ , Q⇒P) (all[¬Px,xs] ∷≉ g[xs]) = All.gmap⁺ (_∘ Q⇒P) all[¬Px,xs] ∷≉ map⁺ P⇔Q g[xs]
  map⁺ P⇔Q@(P⇒Q , _) (Px₁x₂ ∷≈ g[xs])       = P⇒Q Px₁x₂ ∷≈ map⁺ P⇔Q g[xs]

  map⁻ : ∀ {f xs} → P ⇔ (Q on f) → Grouped Q (map f xs) → Grouped P xs
  map⁻ {xs = []}          P⇔Q            []                  = []
  map⁻ {xs = _ ∷ []}     P⇔Q            ([] ∷≉ [])         = [] ∷≉ []
  map⁻ {xs = _ ∷ _ ∷ _} P⇔Q@(P⇒Q , _) (all[¬Qx,xs] ∷≉ g) = All.gmap⁻ (_∘ P⇒Q) all[¬Qx,xs] ∷≉ map⁻ P⇔Q g
  map⁻ {xs = _ ∷ _ ∷ _} P⇔Q@(_ , Q⇒P) (Qx₁x₂ ∷≈ g)       = Q⇒P Qx₁x₂ ∷≈ map⁻ P⇔Q g

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
