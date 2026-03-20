------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; ∃; -,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (_∘′_; _∘_)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Decidable.Core using (Dec; no; map′; _⊎?_)
open import Relation.Unary using (Pred; _⊆_; Satisfiable; Decidable)

open StrictTotalOrder strictTotalOrder using () renaming (Carrier to Key)
open import Data.Tree.AVL.Indexed strictTotalOrder
  using (Tree; Value; Key⁺; [_]; _<⁺_; K&_; _,_; key; _∼_⊔_; ∼0; leaf; node)


private
  variable
    v p q : Level
    V : Value v
    P : Pred (K& V) p
    Q : Pred (K& V) q
    k : Key
    l u : Key⁺
    n : ℕ
    hˡ hʳ h : ℕ
    t : Tree V l u h


------------------------------------------------------------------------
-- Definition

-- Given a predicate P, Any P t describes a path in t to an element that
-- satisfies P. There may be others.
-- See `Relation.Unary` for an explanation of predicates.

data Any {V : Value v} (P : Pred (K& V) p)
     : Tree V l u n → Set (p ⊔ a ⊔ v ⊔ ℓ₂) where
  here  : ∀ {kv : K& V} → P kv →
          {lk : Tree V l [ kv .key ] hˡ}
          {ku : Tree V [ kv .key ] u hʳ}
          {bal : hˡ ∼ hʳ ⊔ h} →
          Any P (node kv lk ku bal)
  left  : ∀ {kv : K& V}
          {lk : Tree V l [ kv .key ] hˡ} →
          Any P lk →
          {ku : Tree V [ kv .key ] u hʳ}
          {bal : hˡ ∼ hʳ ⊔ h} →
          Any P (node kv lk ku bal)
  right : ∀ {kv : K& V}
          {lk : Tree V l [ kv .key ] hˡ}
          {ku : Tree V [ kv .key ] u hʳ} →
          Any P ku →
          {bal : hˡ ∼ hʳ ⊔ h} →
          Any P (node kv lk ku bal)

------------------------------------------------------------------------
-- Operations on Any

map : P ⊆ Q → Any P t → Any Q t
map f (here  p) = here (f p)
map f (left  p) = left (map f p)
map f (right p) = right (map f p)

lookup : Any {V = V} P t → K& V
lookup (here {kv = kv} _) = kv
lookup (left  p)          = lookup p
lookup (right p)          = lookup p

lookupKey : Any P t → Key
lookupKey = key ∘′ lookup

-- If any element satisfies P, then P is satisfiable.

satisfied : Any P t → Satisfiable P
satisfied (here  p) = -, p
satisfied (left  p) = satisfied p
satisfied (right p) = satisfied p

module _ {kv : K& V}
  {lk : Tree V l [ kv .key ] hˡ}
  {ku : Tree V [ kv .key ] u hʳ}
  {bal : hˡ ∼ hʳ ⊔ h}
  where

  toSum : Any P (node kv lk ku bal) → P kv ⊎ Any P lk ⊎ Any P ku
  toSum (here p)  = inj₁ p
  toSum (left p)  = inj₂ (inj₁ p)
  toSum (right p) = inj₂ (inj₂ p)

  fromSum : P kv ⊎ Any P lk ⊎ Any P ku → Any P (node kv lk ku bal)
  fromSum (inj₁ p)        = here p
  fromSum (inj₂ (inj₁ p)) = left p
  fromSum (inj₂ (inj₂ p)) = right p

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

any? : Decidable P → Decidable {A = Tree V l u h} (Any P)
any? P? (leaf _)        = no λ()
any? P? (node kv l r _) = map′ fromSum toSum (P? kv ⊎? any? P? l ⊎? any? P? r)

satisfiable : l <⁺ [ k ] → [ k ] <⁺ u →
              Satisfiable (P ∘ (k ,_)) →
              Satisfiable {A = Tree V l u 1} (Any P)
satisfiable {k = k} lb ub (v , pv) = node (k , v) (leaf lb) (leaf ub) ∼0 , here pv
