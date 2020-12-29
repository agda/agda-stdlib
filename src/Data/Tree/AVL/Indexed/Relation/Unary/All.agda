------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.All
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_; _×_)
open import Data.Product.Nary.NonDependent
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base
open import Function.Nary.NonDependent using (congₙ)
open import Level using (Level; _⊔_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary using (Decidable; Universal; Irrelevant; _⊆_)

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
open import Data.Tree.AVL.Indexed strictTotalOrder as AVL
  using (Tree; Value; Key⁺; [_]; _<⁺_; K&_; _∼_⊔_; ∼0; leaf; node)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any strictTotalOrder
  using (Any; here; left; right)

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

data All {V : Value v} (P : ∀ k → Value.family V k → Set p) {l u}
     : ∀ {n} → Tree V l u n → Set (p ⊔ a ⊔ v ⊔ ℓ₂) where
  leaf  : {p : l <⁺ u} → All P (leaf p)
  node  : ∀ {hˡ hʳ h} {kv@(k , v) : K& V}
          {lk : Tree V l [ k ] hˡ}
          {ku : Tree V [ k ] u hʳ} →
          {bal : hˡ ∼ hʳ ⊔ h} →
          P k v → All P lk → All P ku → All P (node kv lk ku bal)

------------------------------------------------------------------------
-- Operations on All

module _ {V : Value v}
  {P : ∀ k → Value.family V k → Set p}
  {Q : ∀ k → Value.family V k → Set q}
  where

  map : ∀ {t : Tree V l u n} → (∀ {k} → P k ⊆ Q k) → All P t → All Q t
  map f leaf         = leaf
  map f (node p l r) = node (f p) (map f l) (map f r)

  decide : (∀ {k} v → P k v ⊎ Q k v) →
           ∀ {h} (t : Tree V l u h) → All P t ⊎ Any Q t
  decide p⊎q (leaf l<u)                = inj₁ leaf
  decide p⊎q (node kv@(k , v) l r bal) with p⊎q v | decide p⊎q l | decide p⊎q r
  ... | inj₂ q | _ | _ = inj₂ (here q)
  ... | _ | inj₂ q | _ = inj₂ (left q)
  ... | _ | _ | inj₂ q = inj₂ (right q)
  ... | inj₁ pv | inj₁ pl | inj₁ pr = inj₁ (node pv pl pr)

module _ {V : Value v}
  {P : ∀ k → Value.family V k → Set p}
  where

  unnode : ∀ {hˡ hʳ h} {kv@(k , v) : K& V}
    {lk : Tree V l [ k ] hˡ} {ku : Tree V [ k ] u hʳ} {bal : hˡ ∼ hʳ ⊔ h} →
    All P (node kv lk ku bal) → P k v × All P lk × All P ku
  unnode (node p l r) = p , l , r

  all? : (∀ {k} → Decidable (P k)) →
         ∀ {h} (t : Tree V l u h) → Dec (All P t)
  all? p? (leaf l<u)             = yes leaf
  all? p? (node (k , v) l r bal) = map′ (uncurryₙ 3 node) unnode
                                   (p? v ×-dec all? p? l ×-dec all? p? r)

  universal : (∀ {k} → Universal (P k)) →
              ∀ {h} (t : Tree V l u h) → All P t
  universal u (leaf l<u)             = leaf
  universal u (node (k , v) l r bal) = node (u v) (universal u l) (universal u r)

  irrelevant : (∀ {k} → Irrelevant (P k)) →
               ∀ {h} {t : Tree V l u h} → (p q : All P t) → p ≡ q
  irrelevant irr leaf           leaf           = refl
  irrelevant irr (node p l₁ r₁) (node q l₂ r₂) =
    congₙ 3 node (irr p q) (irrelevant irr l₁ l₂) (irrelevant irr r₁ r₂)
