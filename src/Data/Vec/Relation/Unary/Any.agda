------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Relation.Unary.Any {a} {A : Set a} where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc; NonZero)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec.Base as Vec using (Vec; []; [_]; _∷_)
open import Data.Product.Base as Product using (∃; _,_)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Nullary.Decidable as Dec using (no; _⊎?_)
open import Relation.Unary

private
  variable
    p q : Level
    P : Pred A p
    Q : Pred A q
    n : ℕ
    xs : Vec A n

------------------------------------------------------------------------
-- Any P xs means that at least one element in xs satisfies P.

data Any (P : Pred A p) : ∀ {n} → Vec A n → Set (a ⊔ p) where
  here  : ∀ {n x} {xs : Vec A n} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {n x} {xs : Vec A n} (pxs : Any P xs) → Any P (x ∷ xs)

------------------------------------------------------------------------
-- Operations on Any

-- If the tail does not satisfy the predicate, then the head will.
head : ∀ {x} → ¬ Any P xs → Any P (x ∷ xs) → P x
head ¬pxs (here px)   = px
head ¬pxs (there pxs) = contradiction pxs ¬pxs

-- If the head does not satisfy the predicate, then the tail will.
tail : ∀ {x} → ¬ P x → Any P (x ∷ xs) → Any P xs
tail ¬px (here  px)  = contradiction px ¬px
tail ¬px (there pxs) = pxs

-- Convert back and forth with sum
toSum : ∀ {x} → Any P (x ∷ xs) → P x ⊎ Any P xs
toSum (here px)   = inj₁ px
toSum (there pxs) = inj₂ pxs

fromSum : ∀ {x} → P x ⊎ Any P xs → Any P (x ∷ xs)
fromSum = [ here , there ]′

map : P ⊆ Q → ∀ {n} → Any P {n} ⊆ Any Q {n}
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

index : Any P {n} xs → Fin n
index (here  px)  = zero
index (there pxs) = suc (index pxs)

lookup : Any P xs → A
lookup {xs = xs} p = Vec.lookup xs (index p)

-- If any element satisfies P, then P is satisfied.
satisfied : Any P xs → Satisfiable P
satisfied (here px)   = _ , px
satisfied (there pxs) = satisfied pxs

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

any? : Decidable P → ∀ {n} → Decidable (Any P {n})
any? P? []       = no λ()
any? P? (x ∷ xs) = Dec.map′ fromSum toSum (P? x ⊎? any? P? xs)

satisfiable⁺ : Satisfiable P → ∀ {n} → Satisfiable (Any P {suc n})
satisfiable⁺ (x , p) {zero}  = x ∷ [] , here p
satisfiable⁺ (x , p) {suc n} = Product.map (x ∷_) there (satisfiable⁺ (x , p))


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

any = any?
{-# WARNING_ON_USAGE any
"Warning: any was deprecated in v1.4.
Please use any? instead."
#-}

-- Version 2.4

satisfiable = satisfiable⁺
{-# WARNING_ON_USAGE satisfiable
"Warning: satisfiable was deprecated in v2.4.
Please use satisfiable⁺ instead. Moreover,
the name satisfied will be renamed in v3.0
to satisfiable, so users should refactor
as soon as they can."
#-}
