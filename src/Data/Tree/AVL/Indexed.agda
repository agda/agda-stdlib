------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees where the stored values may depend on their key
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where

open import Level using (Level; _⊔_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product.Base using (Σ; ∃; _×_; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.List.Base as List using (List)
open import Data.DifferenceList as DiffList using (DiffList; []; _∷_; _++_)
open import Function.Base as Function hiding (const)
open import Relation.Unary
open import Relation.Binary.Definitions using (_Respects_; Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open StrictTotalOrder strictTotalOrder
  using (module Eq; compare) renaming (Carrier to Key)

------------------------------------------------------------------------
-- Re-export core definitions publicly

open import Data.Tree.AVL.Key strictTotalOrder public
open import Data.Tree.AVL.Value Eq.setoid public
open import Data.Tree.AVL.Height public

------------------------------------------------------------------------
-- Now we have vocabulary in which to state things more cleanly

private
  variable
    ℓ v w : Level
    A : Set ℓ
    l m u : Key⁺
    hˡ hʳ h : ℕ


------------------------------------------------------------------------
-- Definitions of the tree types

-- The trees have three parameters/indices: a lower bound on the
-- keys, an upper bound, and a height.
--
-- (The bal argument is the balance factor.)

data Tree (V : Value v) (l u : Key⁺) : ℕ → Set (a ⊔ v ⊔ ℓ₂) where
  leaf : (l<u : l <⁺ u) → Tree V l u 0
  node : (kv : K& V)
         (lk : Tree V l [ kv .key ] hˡ)
         (ku : Tree V [ kv .key ] u hʳ)
         (bal : hˡ ∼ hʳ ⊔ h) →
         Tree V l u (suc h)

-- Auxiliary type definitions for the types of insert, delete etc.

module _ (V : Value v) (l u : Key⁺) where

  Tree⁺ Tree⁻ : (h : ℕ) → Set (a ⊔ v ⊔ ℓ₂)
  Tree⁺ h = ∃ λ i → Tree V l u (i ⊕ h)
  Tree⁻ h = ∃ λ i → Tree V l u pred[ i ⊕ h ]

  pattern leaf⁻ l<u = _ , leaf l<u  -- empty trees when passed as Tree⁻ V l u 0

------------------------------------------------------------------------
-- Functorial map over all values in the tree.

module _ {V : Value v} {W : Value w}
         (open Value using (family))
         (f : family V ⊆ family W) where

  map : Tree V l u h → Tree W l u h
  map (leaf l<u)             = leaf l<u
  map (node (k , v) l r bal) = node (k , f v) (map l) (map r) bal

------------------------------------------------------------------------
-- Properties relative to a fixed Value type family

module _ {V : Value v} (open Value V using (respects) renaming (family to Val)) where

  ordered : Tree V l u h → l <⁺ u
  ordered (leaf l<u)          = l<u
  ordered (node kv lk ku bal) = trans⁺ _ (ordered lk) (ordered ku)

  private

  -- Lemmas justifying the use of `leaf`/`leaf⁻` pattern matches in code below

    tree0 : (t : Tree V l u 0) → t ≡ leaf (ordered t)
    tree0 t@(leaf _) = refl

    tree⁻0 : (t⁻ : Tree⁻ V l u 0) →
             ∃ λ i → ∃ λ t → t⁻ ≡ (i , t) × t ≡ leaf (ordered t)
    tree⁻0 t⁻@(leaf⁻ _) = _ , _ , refl , refl

  -- Injectivity of constructors

  leaf-injective : ∀ {p q : l <⁺ u} → (Tree V l u 0 ∋ leaf p) ≡ leaf q → p ≡ q
  leaf-injective refl = refl

  node-injective-key :
    ∀ {hˡ₁ hˡ₂ hʳ₁ hʳ₂ h l u k₁ k₂}
      {lk₁ : Tree V l [ k₁ .key ] hˡ₁} {lk₂ : Tree V l [ k₂ .key ] hˡ₂}
      {ku₁ : Tree V [ k₁ .key ] u hʳ₁} {ku₂ : Tree V [ k₂ .key ] u hʳ₂}
      {bal₁ : hˡ₁ ∼ hʳ₁ ⊔ h} {bal₂ : hˡ₂ ∼ hʳ₂ ⊔ h} →
    node k₁ lk₁ ku₁ bal₁ ≡ node k₂ lk₂ ku₂ bal₂ → k₁ ≡ k₂
  node-injective-key refl = refl

  -- See also node-injectiveˡ, node-injectiveʳ, and node-injective-bal
  -- in Data.Tree.AVL.Indexed.WithK.

------------------------------------------------------------------------
-- Constructions on trees

  -- An empty tree.

  empty : l <⁺ u → Tree V l u 0
  empty = leaf

  -- A singleton tree.

  singleton : ∀ k → Val k → l < k < u → Tree V l u 1
  singleton k v (l<k , k<u) = node (k , v) (leaf l<k) (leaf k<u) ∼0

  -- Cast operations. Logarithmic in the size of the tree, if we don't
  -- count the time needed to construct the new proofs in the leaf
  -- cases. (The same kind of caveat applies to other operations
  -- below.)
  --
  -- Perhaps it would be worthwhile changing the data structure so
  -- that the casts could be implemented in constant time (excluding
  -- proof manipulation). However, note that this would not change the
  -- worst-case time complexity of the operations below (up to Θ).

  castˡ : l <⁺ m → Tree V m u h → Tree V l u h
  castˡ l<m (leaf m<u)         = leaf (trans⁺ _ l<m m<u)
  castˡ l<m (node k mk ku bal) = node k (castˡ l<m mk) ku bal

  castʳ : Tree V l m h → m <⁺ u → Tree V l u h
  castʳ (leaf l<m)         m<u = leaf (trans⁺ _ l<m m<u)
  castʳ (node k lk km bal) m<u = node k lk (castʳ km m<u) bal

  -- Various constant-time functions which construct trees out of
  -- smaller pieces, sometimes using rotation.

  pattern node⁰ʳ k₁ t₁ k₂ t₂ t₃ = node k₁ t₁ (node k₂ t₂ t₃ ∼0) ∼0
  pattern node⁰ˡ k₁ k₂ t₁ t₂ t₃ = node k₁ (node k₂ t₁ t₂ ∼0) t₃ ∼0

  pattern node⁺ k₁ t₁ k₂ t₂ t₃ bal = node k₁ t₁ (node k₂ t₂ t₃ bal) ∼+

  joinˡ⁺ : ∀ kv → let k = [ kv . key ] in
           Tree⁺ V l k hˡ → Tree V k u hʳ → hˡ ∼ hʳ ⊔ h →
           Tree⁺ V l u (suc h)
  joinˡ⁺ k₂ (0# , t₁)                t₃ bal = 0# , node k₂ t₁ t₃ bal
  joinˡ⁺ k₂ (1# , t₁)                t₃ ∼0  = 1# , node k₂ t₁ t₃ ∼-
  joinˡ⁺ k₂ (1# , t₁)                t₃ ∼+  = 0# , node k₂ t₁ t₃ ∼0
  joinˡ⁺ k₄ (1# , node  k₂ t₁ t₃ ∼-) t₅ ∼-  = 0# , node⁰ʳ k₂ t₁ k₄ t₃ t₅
  joinˡ⁺ k₄ (1# , node  k₂ t₁ t₃ ∼0) t₅ ∼-  = 1# , node⁺ k₂ t₁ k₄ t₃ t₅ ∼-
  joinˡ⁺ k₆ (1# , node⁺ k₂ t₁ k₄ t₃ t₅ bal) t₇ ∼-
    = 0# , node k₄ (node k₂ t₁ t₃ (max∼ bal)) (node k₆ t₅ t₇ (∼max bal)) ∼0

  pattern node⁻ k₁ k₂ t₁ t₂ bal t₃ = node k₁ (node k₂ t₁ t₂ bal) t₃ ∼-

  joinʳ⁺ : ∀ kv → let k = [ kv . key ] in
           Tree V l k hˡ → Tree⁺ V k u hʳ → hˡ ∼ hʳ ⊔ h →
           Tree⁺ V l u (suc h)
  joinʳ⁺ k₂ t₁ (0# , t₃)               bal = 0# , node k₂ t₁ t₃ bal
  joinʳ⁺ k₂ t₁ (1# , t₃)               ∼0  = 1# , node k₂ t₁ t₃ ∼+
  joinʳ⁺ k₂ t₁ (1# , t₃)               ∼-  = 0# , node k₂ t₁ t₃ ∼0
  joinʳ⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼+) ∼+  = 0# , node⁰ˡ k₄ k₂ t₁ t₃ t₅
  joinʳ⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼0) ∼+  = 1# , node⁻ k₄ k₂ t₁ t₃ ∼+ t₅
  joinʳ⁺ k₂ t₁ (1# , node⁻ k₆ k₄ t₃ t₅ bal t₇) ∼+
    = 0# , node k₄ (node k₂ t₁ t₃ (max∼ bal)) (node k₆ t₅ t₇ (∼max bal)) ∼0

  joinˡ⁻ : ∀ hˡ (kv : K& V) → let k = [ kv . key ] in
           Tree⁻ V l k hˡ → Tree V k u hʳ → hˡ ∼ hʳ ⊔ h →
           Tree⁺ V l u h
  joinˡ⁻ zero    k₂ (leaf⁻ l<k) t₃ bal = 1# , node k₂ (leaf l<k) t₃ bal
  joinˡ⁻ (suc _) k₂ (0# , t₁)   t₃ ∼+  = joinʳ⁺ k₂ t₁ (1# , t₃) ∼+
  joinˡ⁻ (suc _) k₂ (0# , t₁)   t₃ ∼0  = 1# , node k₂ t₁ t₃ ∼+
  joinˡ⁻ (suc _) k₂ (0# , t₁)   t₃ ∼-  = 0# , node k₂ t₁ t₃ ∼0
  joinˡ⁻ (suc _) k₂ (1# , t₁)   t₃ bal = 1# , node k₂ t₁ t₃ bal

  joinʳ⁻ : ∀ hʳ (kv : K& V) → let k = [ kv . key ] in
           Tree V l k hˡ → Tree⁻ V k u hʳ → hˡ ∼ hʳ ⊔ h →
           Tree⁺ V l u h
  joinʳ⁻ zero    k₂ t₁ (leaf⁻ k<u) bal = 1# , node k₂ t₁ (leaf k<u) bal
  joinʳ⁻ (suc _) k₂ t₁ (0# , t₃)   ∼-  = joinˡ⁺ k₂ (1# , t₁) t₃ ∼-
  joinʳ⁻ (suc _) k₂ t₁ (0# , t₃)   ∼0  = 1# , node k₂ t₁ t₃ ∼-
  joinʳ⁻ (suc _) k₂ t₁ (0# , t₃)   ∼+  = 0# , node k₂ t₁ t₃ ∼0
  joinʳ⁻ (suc _) k₂ t₁ (1# , t₃)   bal = 1# , node k₂ t₁ t₃ bal

  -- Extracts the smallest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  headTail : Tree V l u (suc h) →
             ∃ λ kv → let k = [ kv . key ] in l <⁺ k × Tree⁺ V k u h
  headTail (node k₁ (leaf l<k₁) t₂ bal)
    with refl ← 0∼⊔ bal                 = k₁ , l<k₁ , 0# , t₂
  headTail (node k₃ t₁₂@(node _ _ _ _) t₄ bal)
    using k₁ , l<k₁ , t₂ ← headTail t₁₂ = k₁ , l<k₁ , joinˡ⁻ _ k₃ t₂ t₄ bal

  -- Extracts the largest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  initLast : Tree V l u (suc h) →
             ∃ λ kv → let k = [ kv . key ] in k <⁺ u × Tree⁺ V l k h
  initLast (node k₂ t₁ (leaf k₂<u) bal)
    with refl ← ∼0⊔ bal                 = k₂ , k₂<u , 0# , t₁
  initLast (node k₂ t₁ t₃₄@(node _ _ _ _) bal)
    using k₄ , k₄<u , t₃ ← initLast t₃₄ = k₄ , k₄<u , joinʳ⁻ _ k₂ t₁ t₃ bal

  -- Another joining function. Logarithmic in the size of either of
  -- the input trees (which need to have almost equal heights).

  join : Tree V l m hˡ → Tree V m u hʳ → hˡ ∼ hʳ ⊔ h → Tree⁺ V l u h
  join t₁ (leaf m<u) bal
    with refl ← ∼0⊔ bal                 = 0# , castʳ t₁ m<u
  join t₁ t₂₃@(node _ _ _ _) bal
    using k₂ , m<k₂ , t₃ ← headTail t₂₃ = joinʳ⁻ _ k₂ (castʳ t₁ m<k₂) t₃ bal

  -- Inserts a key into the tree, using a function to combine any
  -- existing value with the new value. Logarithmic in the size of the
  -- tree (assuming constant-time comparisons and a constant-time
  -- combining function).

  insertWith : ∀ k → (Maybe (Val k) → Val k) →  -- Maybe old → result.
               Tree V l u h → l < k < u → Tree⁺ V l u h
  insertWith k f (leaf _) l<k<u = 1# , singleton k (f nothing) l<k<u
  insertWith k f (node kv@(k′ , v) lk ku bal) (l<k , k<u) with compare k k′
  ... | tri< k<k′ _ _ = joinˡ⁺ kv (insertWith k f lk (l<k , [ k<k′ ]ᴿ)) ku bal
  ... | tri> _ _ k′<k = joinʳ⁺ kv lk (insertWith k f ku ([ k′<k ]ᴿ , k<u)) bal
  ... | tri≈ _ k≈k′ _ = 0# , node (k′ , v′) lk ku bal
        where v′ = respects k≈k′ (f (just (respects (Eq.sym k≈k′) v)))

  -- Inserts a key into the tree. If the key already exists, then it
  -- is replaced. Logarithmic in the size of the tree (assuming
  -- constant-time comparisons).

  insert : ∀ k → Val k → Tree V l u h → l < k < u → Tree⁺ V l u h
  insert k v = insertWith k (Function.const v)

  -- Deletes the key/value pair containing the given key, if any.
  -- Logarithmic in the size of the tree (assuming constant-time
  -- comparisons).

  delete : ∀ k → Tree V l u h → l < k < u → Tree⁻ V l u h
  delete k t@(leaf _) _ = 0# , t
  delete k (node kv@(k′ , v) lk ku bal) (l<k , k<u) with compare k′ k
  ... | tri< k′<k _ _ = joinʳ⁻ _ kv lk (delete k ku ([ k′<k ]ᴿ , k<u)) bal
  ... | tri> _ _ k′>k = joinˡ⁻ _ kv (delete k lk (l<k , [ k′>k ]ᴿ)) ku bal
  ... | tri≈ _ k′≈k _ = join lk ku bal

  -- Looks up a key. Logarithmic in the size of the tree (assuming
  -- constant-time comparisons).

  lookup : Tree V l u h → ∀ k → l < k < u → Maybe (Val k)
  lookup (leaf _)                _ _           = nothing
  lookup (node (k′ , v) lk ku _) k (l<k , k<u) with compare k′ k
  ... | tri< k′<k _ _ = lookup ku k ([ k′<k ]ᴿ , k<u)
  ... | tri> _ _ k′>k = lookup lk k (l<k , [ k′>k ]ᴿ)
  ... | tri≈ _ k′≈k _ = just (respects k′≈k v)

  -- Converts the tree to an ordered list. Linear in the size of the
  -- tree.

  foldr : (∀ {k} → Val k → A → A) → A → Tree V l u h → A
  foldr cons nil (leaf l<u)             = nil
  foldr cons nil (node (_ , v) l r bal) = foldr cons (cons v (foldr cons nil r)) l

  toDiffList : Tree V l u h → DiffList (K& V)
  toDiffList (leaf _)       = []
  toDiffList (node k l r _) = toDiffList l ++ k ∷ toDiffList r

  toList : Tree V l u h → List (K& V)
  toList = DiffList.toList ∘ toDiffList

  size : Tree V l u h → ℕ
  size = List.length ∘′ toList
