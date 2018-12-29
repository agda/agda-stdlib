------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous suffix relation
------------------------------------------------------------------------

module Data.List.Relation.Suffix.Heterogeneous.Properties where

open import Function using (_$_; flip)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Unary as U using (Pred)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary as B using (REL; Rel; Trans; Antisym; Irrelevant; _⇒_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; subst)
open import Data.Nat as N using (suc; _+_; _≤_; _<_)
open import Data.List as List
  using (List; []; _∷_; _++_; length; filter; replicate; reverse; reverseAcc)
open import Data.List.Relation.Pointwise as Pw using (Pointwise; []; _∷_; Pointwise-length)
open import Data.List.Relation.Suffix.Heterogeneous as Suffix using (Suffix; here; there; tail)
open import Data.List.Relation.Prefix.Heterogeneous as Prefix using (Prefix)
import Data.Nat.Properties as ℕₚ
import Data.List.Properties as Listₚ
import Data.List.Relation.Prefix.Heterogeneous.Properties as Prefixₚ

------------------------------------------------------------------------
-- reverse (convert to and from Prefix)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  fromPrefix⁺ : ∀ {as bs} → Prefix R as bs → Suffix R (reverse as) (reverse bs)
  fromPrefix⁺ {as} {bs} p with Prefix.toView p
  ... | Prefix._++_ {cs} rs ds = subst (Suffix R (reverse as))
                                       (sym (Listₚ.reverse-++-commute cs ds))
                               $ Suffix.fromView (reverse ds Suffix.++ Pw.reverse⁺ rs)

  fromPrefix⁻ : ∀ {as bs} → Prefix R (reverse as) (reverse bs) → Suffix R as bs
  fromPrefix⁻ pre = P.subst₂ (Suffix R) (Listₚ.reverse-involutive _) (Listₚ.reverse-involutive _)
                  $ fromPrefix⁺ pre

  toPrefix⁺ : ∀ {as bs} → Suffix R as bs → Prefix R (reverse as) (reverse bs)
  toPrefix⁺ {as} {bs} s with Suffix.toView s
  ... | Suffix._++_ cs {ds} rs = subst (Prefix R (reverse as))
                                       (sym (Listₚ.reverse-++-commute cs ds))
                               $ Prefix.fromView (Pw.reverse⁺ rs Prefix.++ reverse cs)

  toPrefix⁻ : ∀ {as bs} → Suffix R (reverse as) (reverse bs) → Prefix R as bs
  toPrefix⁻ suf = P.subst₂ (Prefix R) (Listₚ.reverse-involutive _) (Listₚ.reverse-involutive _)
                $ toPrefix⁺ suf

------------------------------------------------------------------------
-- length

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} {as} where

  length-mono-Suffix-≤ : ∀ {bs} → Suffix R as bs → length as ≤ length bs
  length-mono-Suffix-≤ (here rs)   = ℕₚ.≤-reflexive (Pointwise-length rs)
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
        as>bs = ℕₚ.≤-reflexive (sym eq)
    in contradiction as≤bs (ℕₚ.<⇒≱ as>bs)

------------------------------------------------------------------------
-- Suffix as a partial order

module _ {a b c r s t} {A : Set a} {B : Set b} {C : Set c}
         {R : REL A B r} {S : REL B C s} {T : REL A C t} where

  trans : Trans R S T → Trans (Suffix R) (Suffix S) (Suffix T)
  trans rs⇒t (here rs)    (here ss)       = here (Pw.transitive rs⇒t rs ss)
  trans rs⇒t (here rs)    (there ssuf)    = there (trans rs⇒t (here rs) ssuf)
  trans rs⇒t (there rsuf) ssuf            = trans rs⇒t rsuf (tail ssuf)

module _ {a b e r s} {A : Set a} {B : Set b}
         {R : REL A B r} {S : REL B A s} {E : REL A B e} where

  antisym : Antisym R S E → Antisym (Suffix R) (Suffix S) (Pointwise E)
  antisym rs⇒e rsuf ssuf = Pw.antisymmetric
                             rs⇒e
                             (toPointwise eq rsuf)
                             (toPointwise (sym eq) ssuf)
    where eq = ℕₚ.≤-antisym (length-mono-Suffix-≤ rsuf) (length-mono-Suffix-≤ ssuf)

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
  ++⁻ {[]}    {b ∷ bs} {cs} {ds} eq (here rs) = contradiction (sym eq) (ℕₚ.<⇒≢ ds<cs)
    where
    open ℕₚ.≤-Reasoning
    ds<cs : length ds < length cs
    ds<cs = begin suc (length ds)             ≤⟨ N.s≤s (ℕₚ.n≤m+n (length bs) (length ds)) ⟩
                  suc (length bs + length ds) ≡⟨ sym $ Listₚ.length-++ (b ∷ bs) ⟩
                  length (b ∷ bs ++ ds)       ≡⟨ sym $ Pointwise-length rs ⟩
                  length cs                    ∎

------------------------------------------------------------------------
-- map

module _ {a b c d r} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {R : REL C D r} where

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Suffix (λ a b → R (f a) (g b)) as bs →
         Suffix R (List.map f as) (List.map g bs)
  map⁺ f g (here rs)   = here (Pw.map⁺ f g rs)
  map⁺ f g (there suf) = there (map⁺ f g suf)

  map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
         Suffix R (List.map f as) (List.map g bs) →
         Suffix (λ a b → R (f a) (g b)) as bs
  map⁻ {as} {b ∷ bs} f g (here rs) = here (Pw.map⁻ f g rs)
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

  filter⁺ : ∀ {as bs} → Suffix R as bs → Suffix R (filter P? as) (filter Q? bs)
  filter⁺ (here rs) = here (Pw.filter⁺ P? Q? P⇒Q Q⇒P rs)
  filter⁺ (there {a} suf) with Q? a
  ... | yes q = there (filter⁺ suf)
  ... | no ¬q = filter⁺ suf

------------------------------------------------------------------------
-- replicate

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  replicate⁺ : ∀ {m n a b} → m ≤ n → R a b → Suffix R (replicate m a) (replicate n b)
  replicate⁺ {a = a} {b = b} m≤n r = repl (ℕₚ.≤⇒≤′ m≤n)
    where
    repl : ∀ {m n} → m N.≤′ n → Suffix R (replicate m a) (replicate n b)
    repl N.≤′-refl       = here (Pw.replicate⁺ r _)
    repl (N.≤′-step m≤n) = there (repl m≤n)

------------------------------------------------------------------------
-- Irrelevant

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  irrelevant : Irrelevant R → Irrelevant (Suffix R)
  irrelevant R-irr (here rs)    (here rs₁)    = P.cong here $ Pw.irrelevant R-irr rs rs₁
  irrelevant R-irr (here rs)    (there rsuf)  = contradiction (length-mono-Suffix-≤ rsuf)
                                                              (ℕₚ.<⇒≱ (ℕₚ.≤-reflexive (sym (Pointwise-length rs))))
  irrelevant R-irr (there rsuf) (here rs)     = contradiction (length-mono-Suffix-≤ rsuf)
                                                              (ℕₚ.<⇒≱ (ℕₚ.≤-reflexive (sym (Pointwise-length rs))))
  irrelevant R-irr (there rsuf) (there rsuf₁) = P.cong there $ irrelevant R-irr rsuf rsuf₁

------------------------------------------------------------------------
-- Decidability

  suffix? : B.Decidable R → B.Decidable (Suffix R)
  suffix? R? as bs = Dec.map′ fromPrefix⁻ toPrefix⁺
                   $ Prefixₚ.prefix? R? (reverse as) (reverse bs)
