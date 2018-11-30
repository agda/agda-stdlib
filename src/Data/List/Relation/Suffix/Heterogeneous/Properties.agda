------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous suffix relation
------------------------------------------------------------------------

module Data.List.Relation.Suffix.Heterogeneous.Properties where

open import Function using (_∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Unary as U using (Pred)
open import Relation.Binary using (REL; Rel; Trans; Antisym; _⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat as N using (_≤_)
open import Data.List as List using (List; []; _∷_; _++_; length; filter)
open import Data.List.Relation.Pointwise as Pw using (Pointwise; []; _∷_)
open import Data.List.Relation.Suffix.Heterogeneous using (Suffix; here; there; tail)
import Data.Nat.Properties as Natₚ

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  fromPointwise : Pointwise R ⇒ Suffix R
  fromPointwise = here

  -- toPointwise : ∀ {as bs} → length as ≡ length bs → Suffix R as bs → Pointwise R as bs

module _ {a b c r s t} {A : Set a} {B : Set b} {C : Set c}
         {R : REL A B r} {S : REL B C s} {T : REL A C t} where

  trans : Trans R S T → Trans (Suffix R) (Suffix S) (Suffix T)
  trans rs⇒t (here rs)    (here ss)       = here (Pw.transitive rs⇒t rs ss)
  trans rs⇒t (here rs)    (there ssuf)    = there (trans rs⇒t (here rs) ssuf)
  trans rs⇒t (there rsuf) ssuf            = trans rs⇒t rsuf (tail ssuf)

-- module _ {a b e r s t} {A : Set a} {B : Set b}
--          {R : REL A B r} {S : REL B A s} {E : REL A B e} where
--   antisym : Antisym R S E → Antisym (Suffix R) (Suffix S) (Pointwise E)

------------------------------------------------------------------------
-- length

module _ {a r} {A : Set a} {R : Rel A r} {as} where

  length-mono-Suffix-≤ : ∀ {bs} → Suffix R as bs → length as ≤ length bs
  length-mono-Suffix-≤ (here rs)   = Natₚ.≤-reflexive (Pw.Pointwise-length rs)
  length-mono-Suffix-≤ (there suf) = Natₚ.≤-step (length-mono-Suffix-≤ suf)

------------------------------------------------------------------------
-- _++_

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  ++⁺ : ∀ {as bs cs ds} → Suffix R as bs → Pointwise R cs ds →
        Suffix R (as ++ cs) (bs ++ ds)
  ++⁺ (here rs)   rs′ = here (Pw.++⁺ rs rs′)
  ++⁺ (there suf) rs′ = there (++⁺ suf rs′)

  -- ++⁻ : ∀ {as bs cs ds} → Suffix R (as ++ cs) (bs ++ ds) →
  --       length cs ≡ length ds →
  --       Pointwise R cs ds

------------------------------------------------------------------------
-- map

module _ {a b c d r} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {R : REL C D r} where

  -- TODO: move this lemma into Pointwise?
  private
    pw-map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
              Pointwise (λ a b → R (f a) (g b)) as bs →
              Pointwise R (List.map f as) (List.map g bs)
    pw-map⁺ f g []       = []
    pw-map⁺ f g (r ∷ rs) = r ∷ pw-map⁺ f g rs

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Suffix (λ a b → R (f a) (g b)) as bs →
         Suffix R (List.map f as) (List.map g bs)
  map⁺ f g (here rs)   = here (pw-map⁺ f g rs)
  map⁺ f g (there suf) = there (map⁺ f g suf)

  -- map⁻ : ∀ {as bs} → Suffix R (List.map f as) (List.map g bs)
  --        length cs ≡ length ds →
  --        Pointwise (λ a b → R (f a) (g b)) cs ds

------------------------------------------------------------------------
-- filter

module _ {a b r p q} {A : Set a} {B : Set b} {R : REL A B r}
         {P : Pred A p} {Q : Pred B q} (P? : U.Decidable P) (Q? : U.Decidable Q)
         (P⇒Q : ∀ {a b} → R a b → P a → Q b) (Q⇒P : ∀ {a b} → R a b → Q b → P a)
         where

  private
    pw-filter⁺ : ∀ {as bs} → Pointwise R as bs → Pointwise R (filter P? as) (filter Q? bs)
    pw-filter⁺ []       = []
    pw-filter⁺ {a ∷ _} {b ∷ _} (r ∷ rs) with P? a | Q? b
    ... | yes p | yes q = r ∷ pw-filter⁺ rs
    ... | yes p | no ¬q = ⊥-elim (¬q (P⇒Q r p))
    ... | no ¬p | yes q = ⊥-elim (¬p (Q⇒P r q))
    ... | no ¬p | no ¬q = pw-filter⁺ rs

  filter⁺ : ∀ {as bs} → Suffix R as bs → Suffix R (filter P? as) (filter Q? bs)
  filter⁺ (here rs) = here (pw-filter⁺ rs)
  filter⁺ (there {a} suf) with Q? a
  ... | yes q = there (filter⁺ suf)
  ... | no ¬q = filter⁺ suf

------------------------------------------------------------------------
-- TODO: take, drop
