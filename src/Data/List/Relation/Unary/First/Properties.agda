------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of First
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.First.Properties where

open import Data.Fin.Base using (suc)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.List.Relation.Unary.First
import Data.Sum.Base as Sum
open import Function.Base using (_∘′_; _∘_; id)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; refl; _≗_)
import Relation.Nullary.Decidable.Core as Dec
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (Pred; _⊆_; ∁; Irrelevant; Decidable)

------------------------------------------------------------------------
-- map

module _ {a b p q} {A : Set a} {B : Set b} {P : Pred B p} {Q : Pred B q} where

  map⁺ : {f : A → B} → First (P ∘′ f) (Q ∘′ f) ⊆ First P Q ∘′ List.map f
  map⁺ [ qfx ]        = [ qfx ]
  map⁺ (pfxs ∷ pqfxs) = pfxs ∷ map⁺ pqfxs

  map⁻ : {f : A → B} → First P Q ∘′ List.map f ⊆ First (P ∘′ f) (Q ∘′ f)
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
-- Relationship to All

module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where

  All⇒¬First : P ⊆ ∁ Q → All P ⊆ ∁ (First P Q)
  All⇒¬First p⇒¬q (px ∷ pxs) [ qx ]   = contradiction qx (p⇒¬q px)
  All⇒¬First p⇒¬q (_ ∷ pxs)  (_ ∷ hf) = All⇒¬First p⇒¬q pxs hf

  First⇒¬All : Q ⊆ ∁ P → First P Q ⊆ ∁ (All P)
  First⇒¬All q⇒¬p [ qx ]     (px ∷ pxs) = q⇒¬p qx px
  First⇒¬All q⇒¬p (_ ∷ pqxs) (_ ∷ pxs)  = First⇒¬All q⇒¬p pqxs pxs

------------------------------------------------------------------------
-- Irrelevance

  unique-index : ∀ {xs} → P ⊆ ∁ Q → (f₁ f₂ : First P Q xs) → index f₁ ≡ index f₂
  unique-index p⇒¬q [ _ ]    [ _ ]    = refl
  unique-index p⇒¬q [ qx ]   (px ∷ _) = contradiction qx (p⇒¬q px)
  unique-index p⇒¬q (px ∷ _) [ qx ]   = contradiction qx (p⇒¬q px)
  unique-index p⇒¬q (_ ∷ f₁) (_ ∷ f₂) = ≡.cong suc (unique-index p⇒¬q f₁ f₂)

  irrelevant : P ⊆ ∁ Q → Irrelevant P → Irrelevant Q → Irrelevant (First P Q)
  irrelevant p⇒¬q p-irr q-irr [ px ]    [ qx ]    = ≡.cong [_] (q-irr px qx)
  irrelevant p⇒¬q p-irr q-irr [ qx ]    (px ∷ _)  = contradiction qx (p⇒¬q px)
  irrelevant p⇒¬q p-irr q-irr (px ∷ _)  [ qx ]    = contradiction qx (p⇒¬q px)
  irrelevant p⇒¬q p-irr q-irr (px ∷ f)  (qx ∷ g) =
    ≡.cong₂ _∷_ (p-irr px qx) (irrelevant p⇒¬q p-irr q-irr f g)

------------------------------------------------------------------------
-- Decidability

module _ {a p} {A : Set a} {P : Pred A p} where

  first? : Decidable P → Decidable (First P (∁ P))
  first? P? = Dec.fromSum
            ∘ Sum.map₂ (All⇒¬First contradiction)
            ∘ first (Dec.toSum ∘ P?)

  cofirst? : Decidable P → Decidable (First (∁ P) P)
  cofirst? P? = Dec.fromSum
              ∘ Sum.map₂ (All⇒¬First id)
              ∘ first (Sum.swap ∘ Dec.toSum ∘ P?)

------------------------------------------------------------------------
-- Conversion to Any

module _ {a p} {A : Set a} {P : Pred A p} where

  fromAny∘toAny≗id : ∀ {xs} → fromAny {Q = P} {x = xs} ∘′ toAny ≗ id
  fromAny∘toAny≗id [ qx ]      = refl
  fromAny∘toAny≗id (px ∷ pqxs) = ≡.cong (_ ∷_) (fromAny∘toAny≗id pqxs)

  toAny∘fromAny≗id : ∀ {xs} → toAny {Q = P} ∘′ fromAny {x = xs} ≗ id
  toAny∘fromAny≗id (here px) = refl
  toAny∘fromAny≗id (there v) = ≡.cong there (toAny∘fromAny≗id v)

------------------------------------------------------------------------
-- Equivalence between the inductive definition and the view

module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where

  toView : ∀ {as} → First P Q as → FirstView P Q as
  toView [ qx ] = [] ++ qx ∷ _
  toView (px ∷ pqxs) with toView pqxs
  ... | pxs ++  qy ∷ ys = (px ∷ pxs) ++ qy ∷ ys

  fromView : ∀ {as} → FirstView P Q as → First P Q as
  fromView (pxs ++ qy ∷ ys) = ++⁺ pxs [ qy ]
