------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous infix relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Infix.Heterogeneous.Properties where

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base as List using (List; []; _∷_; length; map; filter; replicate)
open import Data.List.Relation.Binary.Infix.Heterogeneous
open import Data.List.Relation.Binary.Prefix.Heterogeneous as Prefix
  using (Prefix; []; _∷_)
import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties as Prefix
open import Data.List.Relation.Binary.Suffix.Heterogeneous as Suffix
  using (Suffix; here; there)
open import Data.Nat.Base using (zero; suc; _≤_)
import Data.Nat.Properties as ℕ
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (case_of_; _$′_)
open import Relation.Nullary.Decidable using (yes; no; does; map′; _⊎-dec_)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Unary as U using (Pred)
open import Relation.Binary.Core using (REL; _⇒_)
open import Relation.Binary.Definitions using (Decidable; Trans; Antisym)
open import Relation.Binary.PropositionalEquality.Core using (_≢_; refl; cong)
open import Data.List.Relation.Binary.Pointwise.Base as Pointwise
  using (Pointwise)


private
  variable
    a b r s : Level
    A : Set a
    B : Set b
    R : REL A B r
    S : REL A B s

------------------------------------------------------------------------
-- Conversion functions

fromPointwise : ∀ {as bs} → Pointwise R as bs → Infix R as bs
fromPointwise pw = here (Prefix.fromPointwise pw)

fromSuffix : ∀ {as bs} → Suffix R as bs → Infix R as bs
fromSuffix (here pw) = fromPointwise pw
fromSuffix (there p) = there (fromSuffix p)

module _ {c t} {C : Set c} {T : REL A C t} where

  fromPrefixSuffix : Trans R S T → Trans (Prefix R) (Suffix S) (Infix T)
  fromPrefixSuffix tr p (here q)  = here (Prefix.trans tr p (Prefix.fromPointwise q))
  fromPrefixSuffix tr p (there q) = there (fromPrefixSuffix tr p q)

  fromSuffixPrefix : Trans R S T → Trans (Suffix R) (Prefix S) (Infix T)
  fromSuffixPrefix tr (here p)  q       = here (Prefix.trans tr (Prefix.fromPointwise p) q)
  fromSuffixPrefix tr (there p) (_ ∷ q) = there (fromSuffixPrefix tr p q)

∷⁻ : ∀ {as b bs} → Infix R as (b ∷ bs) → Prefix R as (b ∷ bs) ⊎ Infix R as bs
∷⁻ (here pref) = inj₁ pref
∷⁻ (there inf) = inj₂ inf

------------------------------------------------------------------------
-- length

length-mono : ∀ {as bs} → Infix R as bs → length as ≤ length bs
length-mono (here pref) = Prefix.length-mono pref
length-mono (there p)   = ℕ.m≤n⇒m≤1+n (length-mono p)

------------------------------------------------------------------------
-- As an order

module _ {c t} {C : Set c} {T : REL A C t} where

  Prefix-Infix-trans : Trans R S T → Trans (Prefix R) (Infix S) (Infix T)
  Prefix-Infix-trans tr p (here q)  = here (Prefix.trans tr p q)
  Prefix-Infix-trans tr p (there q) = there (Prefix-Infix-trans tr p q)

  Infix-Prefix-trans : Trans R S T → Trans (Infix R) (Prefix S) (Infix T)
  Infix-Prefix-trans tr (here p)  q       = here (Prefix.trans tr p q)
  Infix-Prefix-trans tr (there p) (_ ∷ q) = there (Infix-Prefix-trans tr p q)

  Suffix-Infix-trans : Trans R S T → Trans (Suffix R) (Infix S) (Infix T)
  Suffix-Infix-trans tr p (here q)  = fromSuffixPrefix tr p q
  Suffix-Infix-trans tr p (there q) = there (Suffix-Infix-trans tr p q)

  Infix-Suffix-trans : Trans R S T → Trans (Infix R) (Suffix S) (Infix T)
  Infix-Suffix-trans tr p (here q)  = Infix-Prefix-trans tr p (Prefix.fromPointwise q)
  Infix-Suffix-trans tr p (there q) = there (Infix-Suffix-trans tr p q)

  trans : Trans R S T → Trans (Infix R) (Infix S) (Infix T)
  trans tr p (here q)  = Infix-Prefix-trans tr p q
  trans tr p (there q) = there (trans tr p q)

  antisym : Antisym R S T → Antisym (Infix R) (Infix S) (Pointwise T)
  antisym asym (here p) (here q) = Prefix.antisym asym p q
  antisym asym {x = a ∷ as} {y = bs} p@(here _) (there q)
    = ⊥-elim $′ ℕ.<-irrefl refl $′ begin-strict
      length as <⟨ length-mono p ⟩
      length bs ≤⟨ length-mono q ⟩
      length as ∎ where open ℕ.≤-Reasoning
  antisym asym {x = as} {y = b ∷ bs} (there p) q@(here _)
    = ⊥-elim $′ ℕ.<-irrefl refl $′ begin-strict
      length bs <⟨ length-mono q ⟩
      length as ≤⟨ length-mono p ⟩
      length bs ∎ where open ℕ.≤-Reasoning
  antisym asym {x = a ∷ as} {y = b ∷ bs} (there p) (there q)
    = ⊥-elim $′ ℕ.<-irrefl refl $′ begin-strict
      length as <⟨ length-mono p ⟩
      length bs <⟨ length-mono q ⟩
      length as ∎ where open ℕ.≤-Reasoning

------------------------------------------------------------------------
-- map

module _ {c d r} {C : Set c} {D : Set d} {R : REL C D r} where

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Infix (λ a b → R (f a) (g b)) as bs →
         Infix R (List.map f as) (List.map g bs)
  map⁺ f g (here p)  = here (Prefix.map⁺ f g p)
  map⁺ f g (there p) = there (map⁺ f g p)

  map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
         Infix R (List.map f as) (List.map g bs) →
         Infix (λ a b → R (f a) (g b)) as bs
  map⁻ {bs = []}     f g (here p)  = here (Prefix.map⁻ f g p)
  map⁻ {bs = b ∷ bs} f g (here p)  = here (Prefix.map⁻ f g p)
  map⁻ {bs = b ∷ bs} f g (there p) = there (map⁻ f g p)

------------------------------------------------------------------------
-- filter

module _ {p q} {P : Pred A p} {Q : Pred B q} (P? : U.Decidable P) (Q? : U.Decidable Q)
         (P⇒Q : ∀ {a b} → P a → Q b) (Q⇒P : ∀ {a b} → Q b → P a)
         where

  filter⁺ : ∀ {as bs} → Infix R as bs → Infix R (filter P? as) (filter Q? bs)
  filter⁺ (here p) = here (Prefix.filter⁺ P? Q? (λ _ → P⇒Q) (λ _ → Q⇒P) p)
  filter⁺ {bs = b ∷ bs} (there p) with does (Q? b)
  ... | true = there (filter⁺ p)
  ... | false = filter⁺ p

------------------------------------------------------------------------
-- replicate

replicate⁺ : ∀ {m n a b} → m ≤ n → R a b →
             Infix R (replicate m a) (replicate n b)
replicate⁺ m≤n r = here (Prefix.replicate⁺ m≤n r)

replicate⁻ : ∀ {m n a b} → m ≢ 0 →
             Infix R (replicate m a) (replicate n b) → R a b
replicate⁻ {m = m} {n = zero}  m≢0 (here p)  = Prefix.replicate⁻ m≢0 p
replicate⁻ {m = m} {n = suc n} m≢0 (here p)  = Prefix.replicate⁻ m≢0 p
replicate⁻ {m = m} {n = suc n} m≢0 (there p) = replicate⁻ m≢0 p

------------------------------------------------------------------------
-- decidability

infix? : Decidable R → Decidable (Infix R)
infix? R? [] [] = yes (here [])
infix? R? (a ∷ as) [] = no (λ where (here ()))
infix? R? as bbs@(_ ∷ bs) =
  map′ [ here , there ]′ ∷⁻
  (Prefix.prefix? R? as bbs ⊎-dec infix? R? as bs)
