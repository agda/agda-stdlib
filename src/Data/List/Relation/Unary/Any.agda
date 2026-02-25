------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Any where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base as List using (List; []; [_]; _∷_; removeAt)
open import Data.Product.Base as Product using (∃; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Decidable.Core as Dec using (no; _⊎?_)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; _⊆_; Decidable; Satisfiable)

private
  variable
    a p q : Level
    A : Set a
    P Q : Pred A p
    x : A
    xs : List A

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, then Any P xs means that at least one element
-- in xs satisfies P. See `Relation.Unary` for an explanation of
-- predicates.

data Any {A : Set a} (P : Pred A p) : Pred (List A) (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

------------------------------------------------------------------------
-- Operations on Any

head : ¬ Any P xs → Any P (x ∷ xs) → P x
head ¬pxs (here px)   = px
head ¬pxs (there pxs) = contradiction pxs ¬pxs

tail : ¬ P x → Any P (x ∷ xs) → Any P xs
tail ¬px (here  px)  = contradiction px ¬px
tail ¬px (there pxs) = pxs

map : P ⊆ Q → Any P ⊆ Any Q
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

-- `index x∈xs` is the list position (zero-based) which `x∈xs` points to.

index : Any P xs → Fin (List.length xs)
index (here  px)  = zero
index (there pxs) = suc (index pxs)

lookup : {P : Pred A p} → Any P xs → A
lookup {xs = xs} p = List.lookup xs (index p)

infixr 5 _∷=_

_∷=_ : {P : Pred A p} → Any P xs → A → List A
_∷=_ {xs = xs} x∈xs v = xs List.[ index x∈xs ]∷= v

infixl 4 _─_
_─_ : {P : Pred A p} → ∀ xs → Any P xs → List A
xs ─ x∈xs = removeAt xs (index x∈xs)

-- If any element satisfies P, then P is satisfied.

any⇒satisfiable : Any P xs → Satisfiable P
any⇒satisfiable (here px)   = _ , px
any⇒satisfiable (there pxs) = any⇒satisfiable pxs

toSum : Any P (x ∷ xs) → P x ⊎ Any P xs
toSum (here px)   = inj₁ px
toSum (there pxs) = inj₂ pxs

fromSum : P x ⊎ Any P xs → Any P (x ∷ xs)
fromSum (inj₁ px)  = here px
fromSum (inj₂ pxs) = there pxs

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

any? : Decidable P → Decidable (Any P)
any? P? []       = no λ()
any? P? (x ∷ xs) = Dec.map′ fromSum toSum (P? x ⊎? any? P? xs)

satisfiable⁺ : Satisfiable P → Satisfiable (Any P)
satisfiable⁺ (x , Px) = [ x ] , here Px

satisfiable⁻ : Satisfiable (Any P) → Satisfiable P
satisfiable⁻ (x ∷ _  , here px)   = x , px
satisfiable⁻ (_ ∷ xs , there pxs) = satisfiable⁻ (xs , pxs)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.4

any = any?
{-# WARNING_ON_USAGE any
"Warning: any was deprecated in v1.4.
Please use any? instead."
#-}

-- Version 2.4

satisfied = any⇒satisfiable
{-# WARNING_ON_USAGE satisfied
"Warning: satisfied was deprecated in v2.4.
Please use any⇒satisfiable instead."
#-}

satisfiable = satisfiable⁺
{-# WARNING_ON_USAGE satisfiable
"Warning: satisfiable was deprecated in v2.4.
Please use satisfiable⁺ instead."
#-}
