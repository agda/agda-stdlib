------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous suffix relation
------------------------------------------------------------------------

module Data.List.Relation.Suffix.Heterogeneous.Properties where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Unary as U using (Pred)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (REL; Rel; Trans; Antisym; _⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Data.Nat as N using (suc; _+_; _≤_; _<_)
open import Data.List as List using (List; []; _∷_; _++_; length; filter; replicate)
open import Data.List.Relation.Pointwise as Pw using (Pointwise; []; _∷_)
open import Data.List.Relation.Suffix.Heterogeneous using (Suffix; here; there; tail)
import Data.Nat.Properties as ℕₚ
import Data.List.Properties as Listₚ

------------------------------------------------------------------------
-- length

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} {as} where

  length-mono-Suffix-≤ : ∀ {bs} → Suffix R as bs → length as ≤ length bs
  length-mono-Suffix-≤ (here rs)   = ℕₚ.≤-reflexive (Pw.Pointwise-length rs)
  length-mono-Suffix-≤ (there suf) = ℕₚ.≤-step (length-mono-Suffix-≤ suf)

------------------------------------------------------------------------
-- Pointwise conversion

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  fromPointwise : Pointwise R ⇒ Suffix R
  fromPointwise = here

  toPointwise : ∀ {as bs} → length as ≡ length bs → Suffix R as bs → Pointwise R as bs
  toPointwise eq (here rs) = rs
  toPointwise eq (there suf) =
    let as≤bs = length-mono-Suffix-≤ suf
        as>bs = ℕₚ.≤-reflexive (P.sym eq)
    in contradiction as≤bs (ℕₚ.<⇒≱ as>bs)

------------------------------------------------------------------------
-- Suffix as a partial order

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
-- _++_

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  ++⁺ : ∀ {as bs cs ds} → Suffix R as bs → Pointwise R cs ds →
        Suffix R (as ++ cs) (bs ++ ds)
  ++⁺ (here rs)   rs′ = here (Pw.++⁺ rs rs′)
  ++⁺ (there suf) rs′ = there (++⁺ suf rs′)

  ++⁻ : ∀ {as bs cs ds} → length cs ≡ length ds →
        Suffix R (as ++ cs) (bs ++ ds) → Pointwise R cs ds
  ++⁻ {_ ∷ _} {_}      eq suf         = ++⁻ eq (tail suf)
  ++⁻ {[]}    {[]}     eq suf         = toPointwise eq suf
  ++⁻ {[]}    {b ∷ bs} eq (there suf) = ++⁻ eq suf
  ++⁻ {[]}    {b ∷ bs} {cs} {ds} eq (here rs) = contradiction (P.sym eq) (ℕₚ.<⇒≢ ds<cs)
    where
    open ℕₚ.≤-Reasoning
    ds<cs : length ds < length cs
    ds<cs = begin suc (length ds)             ≤⟨ N.s≤s (ℕₚ.n≤m+n (length bs) (length ds)) ⟩
                  suc (length bs + length ds) ≡⟨ P.sym (Listₚ.length-++ (b ∷ bs)) ⟩
                  length (b ∷ bs ++ ds)       ≡⟨ P.sym (Pw.Pointwise-length rs) ⟩
                  length cs                    ∎

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

    pw-map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
              Pointwise R (List.map f as) (List.map g bs) →
              Pointwise (λ a b → R (f a) (g b)) as bs
    pw-map⁻ {[]} {[]} f g [] = []
    pw-map⁻ {[]} {b ∷ bs} f g rs with Pw.Pointwise-length rs
    ... | ()
    pw-map⁻ {a ∷ as} {[]} f g rs with Pw.Pointwise-length rs
    ... | ()
    pw-map⁻ {a ∷ as} {b ∷ bs} f g (r ∷ rs) = r ∷ pw-map⁻ f g rs

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Suffix (λ a b → R (f a) (g b)) as bs →
         Suffix R (List.map f as) (List.map g bs)
  map⁺ f g (here rs)   = here (pw-map⁺ f g rs)
  map⁺ f g (there suf) = there (map⁺ f g suf)

  map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
         Suffix R (List.map f as) (List.map g bs) →
         Suffix (λ a b → R (f a) (g b)) as bs
  map⁻ {as} {b ∷ bs} f g (here rs) = here (pw-map⁻ f g rs)
  map⁻ {as} {b ∷ bs} f g (there suf) = there (map⁻ f g suf)
  map⁻ {x ∷ as} {[]} f g suf with length-mono-Suffix-≤ suf
  ... | ()
  map⁻ {[]} {[]} f g suf = here []

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
    ... | yes p | no ¬q = contradiction (P⇒Q r p) ¬q
    ... | no ¬p | yes q = contradiction (Q⇒P r q) ¬p
    ... | no ¬p | no ¬q = pw-filter⁺ rs

  filter⁺ : ∀ {as bs} → Suffix R as bs → Suffix R (filter P? as) (filter Q? bs)
  filter⁺ (here rs) = here (pw-filter⁺ rs)
  filter⁺ (there {a} suf) with Q? a
  ... | yes q = there (filter⁺ suf)
  ... | no ¬q = filter⁺ suf

------------------------------------------------------------------------
-- replicate

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  private
    pw-replicate : ∀ {a b} → R a b → ∀ n → Pointwise R (replicate n a) (replicate n b)
    pw-replicate r 0       = []
    pw-replicate r (suc n) = r ∷ pw-replicate r n

  replicate⁺ : ∀ {m n a b} → m ≤ n → R a b → Suffix R (replicate m a) (replicate n b)
  replicate⁺ {a = a} {b = b} m≤n r = repl (ℕₚ.≤⇒≤′ m≤n)
    where
    repl : ∀ {m n} → m N.≤′ n → Suffix R (replicate m a) (replicate n b)
    repl N.≤′-refl       = here (pw-replicate r _)
    repl (N.≤′-step m≤n) = there (repl m≤n)
