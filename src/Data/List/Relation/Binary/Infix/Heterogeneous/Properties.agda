------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous infix relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Infix.Heterogeneous.Properties where

open import Level
open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base as List using (List; []; _∷_; length; map; filter; replicate)
open import Data.Nat.Base using (zero; suc; _≤_; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (case_of_)

open import Relation.Nullary using (¬_; yes; no; does)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary as U using (Pred)
open import Relation.Binary using (REL; _⇒_; Decidable)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Infix.Heterogeneous
open import Data.List.Relation.Binary.Prefix.Heterogeneous
  as Prefix using (Prefix; []; _∷_)
import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties as Prefixₚ
open import Data.List.Relation.Binary.Suffix.Heterogeneous
  as Suffix using (Suffix; here; there)

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
fromPointwise pw = here (Prefixₚ.fromPointwise pw)

fromSuffix : ∀ {as bs} → Suffix R as bs → Infix R as bs
fromSuffix (here pw) = fromPointwise pw
fromSuffix (there p) = there (fromSuffix p)

∷⁻ : ∀ {as b bs} → Infix R as (b ∷ bs) → Prefix R as (b ∷ bs) ⊎ Infix R as bs
∷⁻ (here pref) = inj₁ pref
∷⁻ (there inf) = inj₂ inf

------------------------------------------------------------------------
-- length

length-mono : ∀ {as bs} → Infix R as bs → length as ≤ length bs
length-mono (here pref) = Prefixₚ.length-mono pref
length-mono (there p)   = ℕₚ.≤-step (length-mono p)

------------------------------------------------------------------------
-- map

module _ {c d r} {C : Set c} {D : Set d} {R : REL C D r} where

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Infix (λ a b → R (f a) (g b)) as bs →
         Infix R (List.map f as) (List.map g bs)
  map⁺ f g (here p)  = here (Prefixₚ.map⁺ f g p)
  map⁺ f g (there p) = there (map⁺ f g p)

  map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
         Infix R (List.map f as) (List.map g bs) →
         Infix (λ a b → R (f a) (g b)) as bs
  map⁻ {bs = []}     f g (here p)  = here (Prefixₚ.map⁻ f g p)
  map⁻ {bs = b ∷ bs} f g (here p)  = here (Prefixₚ.map⁻ f g p)
  map⁻ {bs = b ∷ bs} f g (there p) = there (map⁻ f g p)

------------------------------------------------------------------------
-- filter

module _ {p q} {P : Pred A p} {Q : Pred B q} (P? : U.Decidable P) (Q? : U.Decidable Q)
         (P⇒Q : ∀ {a b} → P a → Q b) (Q⇒P : ∀ {a b} → Q b → P a)
         where

  filter⁺ : ∀ {as bs} → Infix R as bs → Infix R (filter P? as) (filter Q? bs)
  filter⁺ (here p) = here (Prefixₚ.filter⁺ P? Q? (λ _ → P⇒Q) (λ _ → Q⇒P) p)
  filter⁺ {bs = b ∷ bs} (there p) with does (Q? b)
  ... | true = there (filter⁺ p)
  ... | false = filter⁺ p

------------------------------------------------------------------------
-- replicate

replicate⁺ : ∀ {m n a b} → m ≤ n → R a b →
             Infix R (replicate m a) (replicate n b)
replicate⁺ m≤n r = here (Prefixₚ.replicate⁺ m≤n r)

replicate⁻ : ∀ {m n a b} → m ≢ 0 →
             Infix R (replicate m a) (replicate n b) → R a b
replicate⁻ {m = m} {n = zero}  m≢0 (here p)  = Prefixₚ.replicate⁻ m≢0 p
replicate⁻ {m = m} {n = suc n} m≢0 (here p)  = Prefixₚ.replicate⁻ m≢0 p
replicate⁻ {m = m} {n = suc n} m≢0 (there p) = replicate⁻ m≢0 p

------------------------------------------------------------------------
-- decidability

infix? : Decidable R → Decidable (Infix R)
infix? R? [] [] = yes (here [])
infix? R? (a ∷ as) [] = no (λ where (here ()))
infix? R? as bbs@(_ ∷ bs) =
  map′ [ here , there ]′ ∷⁻
  (Prefixₚ.prefix? R? as bbs ⊎-dec infix? R? as bs)
