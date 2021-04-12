------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees whose elements satisfy a given property
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
open import Relation.Unary using (Pred; Decidable; Universal; Irrelevant; _⊆_; _∪_)

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key)
open import Data.Tree.AVL.Indexed strictTotalOrder
  using (Tree; Value; Key⁺; [_]; _<⁺_; K&_; key; _∼_⊔_; ∼0; leaf; node)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any strictTotalOrder
  using (Any; here; left; right)

private
  variable
    v p q : Level
    V : Value v
    P : Pred (K& V) p
    Q : Pred (K& V) q
    l u : Key⁺
    n : ℕ
    t : Tree V l u n

------------------------------------------------------------------------
-- Definition

-- Given a predicate P, All P t is a proof that all of the elements in t
-- satisfy P.
-- See `Relation.Unary` for an explanation of predicates.

data All {V : Value v} (P : Pred (K& V) p) {l u}
     : ∀ {n} → Tree V l u n → Set (p ⊔ a ⊔ v ⊔ ℓ₂) where
  leaf  : {p : l <⁺ u} → All P (leaf p)
  node  : ∀ {hˡ hʳ h} {kv : K& V}
          {lk : Tree V l [ kv .key ] hˡ}
          {ku : Tree V [ kv .key ] u hʳ} →
          {bal : hˡ ∼ hʳ ⊔ h} →
          P kv → All P lk → All P ku → All P (node kv lk ku bal)

------------------------------------------------------------------------
-- Operations on All

map : P ⊆ Q → All P t → All Q t
map f leaf         = leaf
map f (node p l r) = node (f p) (map f l) (map f r)

decide : Π[ P ∪ Q ] → (t : Tree V l u n) → All P t ⊎ Any Q t
decide p⊎q (leaf l<u)        = inj₁ leaf
decide p⊎q (node kv l r bal) with p⊎q kv | decide p⊎q l | decide p⊎q r
... | inj₂ q | _ | _ = inj₂ (here q)
... | _ | inj₂ q | _ = inj₂ (left q)
... | _ | _ | inj₂ q = inj₂ (right q)
... | inj₁ pv | inj₁ pl | inj₁ pr = inj₁ (node pv pl pr)

unnode : ∀ {hˡ hʳ h} {kv : K& V}
         {lk : Tree V l [ kv .key ] hˡ}
         {ku : Tree V [ kv .key ] u hʳ}
         {bal : hˡ ∼ hʳ ⊔ h} →
         All P (node kv lk ku bal) → P kv × All P lk × All P ku
unnode (node p l r) = p , l , r

all? : Decidable P → ∀ (t : Tree V l u n) → Dec (All P t)
all? p? (leaf l<u)        = yes leaf
all? p? (node kv l r bal) = map′ (uncurryₙ 3 node) unnode
                                 (p? kv ×-dec all? p? l ×-dec all? p? r)

universal : Universal P → (t : Tree V l u n) → All P t
universal u (leaf l<u)        = leaf
universal u (node kv l r bal) = node (u kv) (universal u l) (universal u r)

irrelevant : Irrelevant P → (p q : All P t) → p ≡ q
irrelevant irr leaf           leaf           = refl
irrelevant irr (node p l₁ r₁) (node q l₂ r₂) =
  congₙ 3 node (irr p q) (irrelevant irr l₁ l₂) (irrelevant irr r₁ r₂)
