------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of insert related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Insert
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base as F using (_∘′_)
open import Level using (Level)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto as AVL
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.AnyLookup sto
  using (lookup-result; lookup-bounded; lookup-rebuild-accum)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.JoinConstFuns sto
  using (joinˡ⁺-left⁺; joinʳ⁺-right⁺; joinˡ⁺-here⁺; joinʳ⁺-here⁺;
         joinʳ⁺-left⁺; joinˡ⁺-right⁺; joinˡ⁺⁻; joinʳ⁺⁻)
open StrictTotalOrder sto renaming (Carrier to Key; trans to <-trans); open Eq using (sym; trans)

open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

import Relation.Binary.Reasoning.StrictPartialOrder as <-Reasoning


private
  variable
    v p : Level
    V : Value v
    l u : Key⁺
    n : ℕ
    P : Pred (K& V) p

module _ {V : Value v} where

  private
    Val  = Value.family V
    Val≈ = Value.respects V

  module _ (k : Key) (f : Maybe (Val k) → Val k) where

    open <-Reasoning AVL.strictPartialOrder

    Any-insertWith-nothing : (t : Tree V l u n) (seg : l < k < u) →
                             P (k , f nothing) →
                             ¬ (Any ((k ≈_) ∘′ key) t) → Any P (proj₂ (insertWith k f t seg))
    Any-insertWith-nothing (leaf l<u)                   seg         pr ¬p = here pr
    Any-insertWith-nothing (node kv@(k′ , v) lk ku bal) (l<k , k<u) pr ¬p
      with compare k k′
    ... | tri≈ _ k≈k′ _ = contradiction (here k≈k′) ¬p
    ... | tri< k<k′ _ _ = joinˡ⁺-left⁺ kv lk′ ku bal ih
      where
      seg′ = l<k , [ k<k′ ]ᴿ
      lk′ = insertWith k f lk seg′
      ih = Any-insertWith-nothing lk seg′ pr (λ p → ¬p (left p))
    ... | tri> _ _ k>k′ = joinʳ⁺-right⁺ kv lk ku′ bal ih
      where
      seg′ = [ k>k′ ]ᴿ , k<u
      ku′ = insertWith k f ku seg′
      ih = Any-insertWith-nothing ku seg′ pr (λ p → ¬p (right p))

    Any-insertWith-just : (t : Tree V l u n) (seg : l < k < u) →
                          (pr : ∀ k′ v → (eq : k ≈ k′) → P (k′ , Val≈ eq (f (just (Val≈ (sym eq) v))))) →
                          Any ((k ≈_) ∘′ key) t → Any P (proj₂ (insertWith k f t seg))
    Any-insertWith-just (node kv@(k′ , v) lk ku bal) (l<k , k<u) pr p
      with p | compare k k′
    -- happy paths
    ... | here _   | tri≈ _ k≈k′ _ = here (pr k′ v k≈k′)
    ... | left lp  | tri< k<k′ _ _ =
      joinˡ⁺-left⁺ kv lk′ ku bal (Any-insertWith-just lk seg′ pr lp)
      where
      seg′ = l<k , [ k<k′ ]ᴿ
      lk′ = insertWith k f lk seg′
    ... | right rp | tri> _ _ k>k′ =
      joinʳ⁺-right⁺ kv lk ku′ bal (Any-insertWith-just ku seg′ pr rp)
      where
      seg′ = [ k>k′ ]ᴿ , k<u
      ku′ = insertWith k f ku seg′

    -- impossible cases
    ... | here eq  | tri< k<k′ _ _ = begin-contradiction
      [ k  ] <⟨ [ k<k′ ]ᴿ ⟩
      [ k′ ] ≈⟨ [ sym eq ]ᴱ ⟩
      [ k  ] ∎
    ... | here eq  | tri> _ _ k>k′ = begin-contradiction
      [ k  ] ≈⟨ [ eq ]ᴱ ⟩
      [ k′ ] <⟨ [ k>k′ ]ᴿ ⟩
      [ k  ] ∎
    ... | left lp  | tri≈ _ k≈k′ _ = begin-contradiction
      let k″ = Any.lookup lp .key; k≈k″ = lookup-result lp; (_ , k″<k′) = lookup-bounded lp in
      [ k  ] ≈⟨ [ k≈k″ ]ᴱ ⟩
      [ k″ ] <⟨ k″<k′ ⟩
      [ k′ ] ≈⟨ [ sym k≈k′ ]ᴱ ⟩
      [ k  ] ∎
    ... | left lp  | tri> _ _ k>k′ = begin-contradiction
      let k″ = Any.lookup lp .key; k≈k″ = lookup-result lp; (_ , k″<k′) = lookup-bounded lp in
      [ k  ] ≈⟨ [ k≈k″ ]ᴱ ⟩
      [ k″ ] <⟨ k″<k′ ⟩
      [ k′ ] <⟨ [ k>k′ ]ᴿ ⟩
      [ k  ] ∎
    ... | right rp | tri< k<k′ _ _ = begin-contradiction
      let k″ = Any.lookup rp .key; k≈k″ = lookup-result rp; (k′<k″ , _) = lookup-bounded rp in
      [ k  ] <⟨ [ k<k′ ]ᴿ ⟩
      [ k′ ] <⟨ k′<k″ ⟩
      [ k″ ] ≈⟨ [ sym k≈k″ ]ᴱ ⟩
      [ k  ] ∎
    ... | right rp | tri≈ _ k≈k′ _ = begin-contradiction
      let k″ = Any.lookup rp .key; k≈k″ = lookup-result rp; (k′<k″ , _) = lookup-bounded rp in
      [ k  ] ≈⟨ [ k≈k′ ]ᴱ ⟩
      [ k′ ] <⟨ k′<k″ ⟩
      [ k″ ] ≈⟨ [ sym k≈k″ ]ᴱ ⟩
      [ k  ] ∎

  module _ (k : Key) (v : Val k) (t : Tree V l u n) (seg : l < k < u) where

    Any-insert-nothing : P (k , v) → ¬ (Any ((k ≈_) ∘′ key) t) → Any P (proj₂ (insert k v t seg))
    Any-insert-nothing = Any-insertWith-nothing k (F.const v) t seg

    Any-insert-just : (pr : ∀ k′ → (eq : k ≈ k′) → P (k′ , Val≈ eq v)) →
                      Any ((k ≈_) ∘′ key) t → Any P (proj₂ (insert k v t seg))
    Any-insert-just pr = Any-insertWith-just k (F.const v) t seg (λ k′ _ eq → pr k′ eq)

  module _ (k : Key) (f : Maybe (Val k) → Val k) where

    insertWith⁺ : (t : Tree V l u n) (seg : l < k < u) →
                  (p : Any P t) → k ≉ Any.lookupKey p →
                  Any P (proj₂ (insertWith k f t seg))
    insertWith⁺ (node kv@(k′ , v′) l r bal) (l<k , k<u) (here p) k≉
      with compare k k′
    ... | tri< k<k′ _ _ = let l′ = insertWith k f l (l<k , [ k<k′ ]ᴿ)
                          in joinˡ⁺-here⁺ kv l′ r bal p
    ... | tri≈ _ k≈k′ _ = contradiction k≈k′ k≉
    ... | tri> _ _ k′<k = let r′ = insertWith k f r ([ k′<k ]ᴿ , k<u)
                          in joinʳ⁺-here⁺ kv l r′ bal p
    insertWith⁺ (node kv@(k′ , v′) l r bal) (l<k , k<u) (left p) k≉
      with compare k k′
    ... | tri< k<k′ _ _ = let l′ = insertWith k f l (l<k , [ k<k′ ]ᴿ)
                              ih = insertWith⁺ l (l<k , [ k<k′ ]ᴿ) p k≉
                          in joinˡ⁺-left⁺ kv l′ r bal ih
    ... | tri≈ _ k≈k′ _ = left p
    ... | tri> _ _ k′<k = let r′ = insertWith k f r ([ k′<k ]ᴿ , k<u)
                          in joinʳ⁺-left⁺ kv l r′ bal p
    insertWith⁺ (node kv@(k′ , v′) l r bal) (l<k , k<u) (right p) k≉
      with compare k k′
    ... | tri< k<k′ _ _ = let l′ = insertWith k f l (l<k , [ k<k′ ]ᴿ)
                          in joinˡ⁺-right⁺ kv l′ r bal p
    ... | tri≈ _ k≈k′ _ = right p
    ... | tri> _ _ k′<k = let r′ = insertWith k f r ([ k′<k ]ᴿ , k<u)
                              ih = insertWith⁺ r ([ k′<k ]ᴿ , k<u) p k≉
                          in joinʳ⁺-right⁺ kv l r′ bal ih

  insert⁺ : (k : Key) (v : Val k) (t : Tree V l u n) (seg : l < k < u) →
            (p : Any P t) → k ≉ Any.lookupKey p →
            Any P (proj₂ (insert k v t seg))
  insert⁺ k v = insertWith⁺ k (F.const v)

  module _
    {P : Pred (K& V) p}
    (P-Resp : ∀ {k k′ v} → (k≈k′ : k ≈ k′) → P (k′ , Val≈ k≈k′ v) → P (k , v))
    (k : Key) (v : Val k)
    where

    insert⁻ : (t : Tree V l u n) (seg : l < k < u) →
              Any P (proj₂ (insert k v t seg)) →
              P (k , v) ⊎ Any (λ{ (k′ , v′) → k ≉ k′ × P (k′ , v′)}) t
    insert⁻ (leaf l<u) seg (here p) = inj₁ p
    insert⁻ (node kv′@(k′ , v′) l r bal) (l<k , k<u) p with compare k k′
    insert⁻ (node kv′@(k′ , v′) l r bal) (l<k , k<u) p | tri< k<k′ k≉k′ _
        with joinˡ⁺⁻ kv′ (insert k v l (l<k , [ k<k′ ]ᴿ)) r bal p
    ... | inj₁ p        = inj₂ (here (k≉k′ , p))
    ... | inj₂ (inj₂ p) = inj₂ (right (lookup-rebuild-accum p k≉p))
      where
      k′<p = [<]-injective (proj₁ (lookup-bounded p))
      k≉p = λ k≈p → irrefl k≈p (<-trans k<k′ k′<p)
    ... | inj₂ (inj₁ p) = Sum.map₂ (λ q → left q) (insert⁻ l (l<k , [ k<k′ ]ᴿ) p)
    insert⁻ (node kv′@(k′ , v′) l r bal) (l<k , k<u) p | tri> _ k≉k′ k′<k
        with joinʳ⁺⁻ kv′ l (insert k v r ([ k′<k ]ᴿ , k<u)) bal p
    ... | inj₁ p        = inj₂ (here (k≉k′ , p))
    ... | inj₂ (inj₁ p) = inj₂ (left (lookup-rebuild-accum p k≉p))
      where
      p<k′ = [<]-injective (proj₂ (lookup-bounded p))
      k≉p = λ k≈p → irrefl (sym k≈p) (<-trans p<k′ k′<k)
    ... | inj₂ (inj₂ p) = Sum.map₂ (λ q → right q) (insert⁻ r ([ k′<k ]ᴿ , k<u) p)
    insert⁻ (node kv′@(k′ , v′) l r bal) (l<k , k<u) p | tri≈ _ k≈k′ _
        with p
    ... | left p  = inj₂ (left (lookup-rebuild-accum p k≉p))
      where
      p<k′ = [<]-injective (proj₂ (lookup-bounded p))
      k≉p = λ k≈p → irrefl (trans (sym k≈p) k≈k′) p<k′
    ... | here p  = inj₁ (P-Resp k≈k′ p)
    ... | right p = inj₂ (right (lookup-rebuild-accum p k≉p))
      where
      k′<p = [<]-injective (proj₁ (lookup-bounded p))
      k≉p = λ k≈p → irrefl (trans (sym k≈k′) k≈p) k′<p
