------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of First
------------------------------------------------------------------------

module Data.List.First.Properties where

open import Data.Empty
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.All as All using (All; []; _∷_)
open import Data.List.First
import Data.Sum as Sum
open import Function
open import Relation.Unary
open import Relation.Nullary.Negation

------------------------------------------------------------------------
-- map

module _ {a b p q} {A : Set a} {B : Set b} {P : Pred B p} {Q : Pred B q} where

  map⁺ : {f : A → B} → First (P ∘′ f) (Q ∘′ f) ⊆ First P Q ∘′ List.map f
  map⁺ [ qfx ]        = [ qfx ]
  map⁺ (pfxs ∷ pqfxs) = pfxs ∷ map⁺ pqfxs

  map⁻ : {f : A → B} → First P Q ∘′ List.map f ⊆ First (P ∘′ f) (Q ∘′ f)
  map⁻ {f} {[]}     ()
  map⁻ {f} {x ∷ xs} [ qfx ]       = [ qfx ]
  map⁻ {f} {x ∷ xs} (pfx ∷ pqfxs) = pfx ∷ map⁻ pqfxs

------------------------------------------------------------------------
-- (++)

module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where

  ++⁺ : ∀ {xs ys} → All P xs → First P Q ys → First P Q (xs List.++ ys)
  ++⁺ []         pqys = pqys
  ++⁺ (px ∷ pxs) pqys = px ∷ ++⁺ pxs pqys

  ⁺++ : ∀ {xs} → First P Q xs → ∀ ys → First P Q (xs List.++ ys)
  ⁺++ [ qx ]      ys = [ qx ]
  ⁺++ (px ∷ pqxs) ys = px ∷ ⁺++ pqxs ys

------------------------------------------------------------------------
-- Decidability result

module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where

  All⇒¬First : P ⊆ ∁ Q → All P ⊆ ∁ (First P Q)
  All⇒¬First p⇒¬q []         ()
  All⇒¬First p⇒¬q (px ∷ pxs) [ qx ]   = ⊥-elim (p⇒¬q px qx)
  All⇒¬First p⇒¬q (_ ∷ pxs)  (_ ∷ hf) = All⇒¬First p⇒¬q pxs hf

  First⇒¬All : Q ⊆ ∁ P → First P Q ⊆ ∁ (All P)
  First⇒¬All q⇒¬p [ qx ]     (px ∷ pxs) = q⇒¬p qx px
  First⇒¬All q⇒¬p (_ ∷ pqxs) (_ ∷ pxs)  = First⇒¬All q⇒¬p pqxs pxs

module _ {a p} {A : Set a} {P : Pred A p} where

  first? : Decidable P → Decidable (First P (∁ P))
  first? P? xs = Sum.toDec
               $ Sum.map₂ (All⇒¬First contradiction)
               $ first (Sum.fromDec ∘ P?) xs

