------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_; ∃₂; -,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base
open import Level using (Level; _⊔_)

open import Relation.Nullary using (Dec; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
open import Data.Tree.AVL.Indexed strictTotalOrder as AVL
  using (Tree; Value; Key⁺; [_]; _<⁺_; K&_; _∼_⊔_; ∼0; leaf; node)


private
  variable
    v p q : Level
    V : Value v
    l u : Key⁺
    n : ℕ

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, Any P t is a path to one element in t that satisfies P.
-- There may be others.
-- See `Relation.Unary` for an explanation of predicates.

data Any {V : Value v} (P : ∀ k → Value.family V k → Set p) {l u}
     : ∀ {n} → Tree V l u n → Set (p ⊔ a ⊔ v ⊔ ℓ₂) where
  here  : ∀ {hˡ hʳ h} {kv@(k , v) : K& V} → P k v →
          {lk : Tree V l [ k ] hˡ}
          {ku : Tree V [ k ] u hʳ}
          {bal : hˡ ∼ hʳ ⊔ h} →
          Any P (node kv lk ku bal)
  left  : ∀ {hˡ hʳ h} {kv : K& V}
          {lk : Tree V l [ proj₁ kv ] hˡ} →
          Any P lk →
          {ku : Tree V [ proj₁ kv ] u hʳ}
          {bal : hˡ ∼ hʳ ⊔ h} →
          Any P (node kv lk ku bal)
  right : ∀ {hˡ hʳ h} {kv : K& V}
          {lk : Tree V l [ proj₁ kv ] hˡ}
          {ku : Tree V [ proj₁ kv ] u hʳ} →
          Any P ku →
          {bal : hˡ ∼ hʳ ⊔ h} →
          Any P (node kv lk ku bal)

------------------------------------------------------------------------
-- Operations on Any

module _ {V : Value v}
  {P : ∀ k → Value.family V k → Set p}
  {Q : ∀ k → Value.family V k → Set q}
  where

  map : ∀ {t : Tree V l u n} → (∀ {k} → P k ⊆ Q k) → Any P t → Any Q t
  map f (here  p) = here (f p)
  map f (left  p) = left (map f p)
  map f (right p) = right (map f p)

module _ {V : Value v}
  {P : ∀ k → Value.family V k → Set p}
  where

  lookup : ∀ {t : Tree V l u n} → Any P t → Key
  lookup (here {kv = kv} _) = proj₁ kv
  lookup (left  p)          = lookup p
  lookup (right p)          = lookup p

-- If any element satisfies P, then P is satisfied.

  satisfied : ∀ {t : Tree V l u n} → Any P t → ∃₂ P
  satisfied (here  p) = -, -, p
  satisfied (left  p) = satisfied p
  satisfied (right p) = satisfied p

  module _ {hˡ hʳ h} {kv@(k , v) : K& V}
    {lk : Tree V l [ k ] hˡ} {ku : Tree V [ k ] u hʳ} {bal : hˡ ∼ hʳ ⊔ h}
    where

    toSum : Any P (node kv lk ku bal) →
            P k v ⊎ Any P lk ⊎ Any P ku
    toSum (here p)  = inj₁ p
    toSum (left p)  = inj₂ (inj₁ p)
    toSum (right p) = inj₂ (inj₂ p)

    fromSum : P k v ⊎ Any P lk ⊎ Any P ku →
              Any P (node kv lk ku bal)
    fromSum (inj₁ p)        = here p
    fromSum (inj₂ (inj₁ p)) = left p
    fromSum (inj₂ (inj₂ p)) = right p

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

  any? : (∀ {k} → Decidable (P k)) →
         ∀ (t : Tree V l u n) → Dec (Any P t)
  any? P? (leaf _)          = no λ ()
  any? P? (node kv l r bal) = map′ fromSum toSum
    (P? (proj₂ kv) ⊎-dec any? P? l ⊎-dec any? P? r)

  satisfiable : (∀ {k} → Satisfiable (P k)) →
                ∀ {k l u} → l <⁺ [ k ] → [ k ] <⁺ u →
                Satisfiable {A = Tree V l u 1} (Any P)
  satisfiable sat {k} lb ub = node (k , proj₁ sat) (leaf lb) (leaf ub) ∼0
                            , here (proj₂ sat)
