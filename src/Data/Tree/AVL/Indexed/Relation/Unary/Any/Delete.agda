------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of delete related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Delete
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Level using (Level)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto as AVL
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.AnyLookup sto
  using (lookup-bounded; lookup-result; lookup-rebuild)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Join sto
  using (join-left⁺; join-right⁺; join-node⁻; join⁻)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.JoinConstFuns sto
  using (joinʳ⁻-here⁺; joinʳ⁻-left⁺; joinʳ⁻-right⁺; joinˡ⁻-here⁺;
         joinˡ⁻-left⁺; joinˡ⁻-right⁺; joinʳ⁻⁻; joinˡ⁻⁻)
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

  module _ (k : Key) where

    delete⁺ : (t : Tree V l u n) (seg : l < k < u) →
              (p : Any P t) → lookupKey p ≉ k →
              Any P (proj₂ (delete k t seg))
    delete⁺ (leaf _) _ p _ = p
    delete⁺ (node (k′ , v) lk′ k′u bal) (l<k , k<u) p p≉k
      with compare k′ k
    delete⁺ (node kv@(k′ , v) lk′ k′u bal) (l<k , k<u) p p≉k
      | tri< k′<k _ _ with p
    ... | here pk =
      joinʳ⁻-here⁺ kv lk′ (delete k k′u ([ k′<k ]ᴿ , k<u)) bal pk
    ... | left pl =
      joinʳ⁻-left⁺ kv lk′ (delete k k′u ([ k′<k ]ᴿ , k<u)) bal pl
    ... | right pr =
      joinʳ⁻-right⁺ kv lk′ (delete k k′u ([ k′<k ]ᴿ , k<u)) bal
        (delete⁺ k′u ([ k′<k ]ᴿ , k<u) pr p≉k)
    delete⁺ (node kv@(k′ , v) lk′ k′u bal) (l<k , k<u) p p≉k
      | tri> _ _ k′>k with p
    ... | here pk =
      joinˡ⁻-here⁺ kv (delete k lk′ (l<k , [ k′>k ]ᴿ)) k′u bal pk
    ... | left pl =
      joinˡ⁻-left⁺ kv (delete k lk′ (l<k , [ k′>k ]ᴿ)) k′u bal
        ((delete⁺ lk′ (l<k , [ k′>k ]ᴿ)) pl p≉k)
    ... | right pr =
      joinˡ⁻-right⁺ kv (delete k lk′ (l<k , [ k′>k ]ᴿ)) k′u bal pr
    delete⁺ (node (k′ , v) lk′ k′u bal) (l<k , k<u) p p≉k
      | tri≈ _ k′≈k _ with p
    ... | here pk = contradiction k′≈k p≉k
    ... | left pl = join-left⁺ lk′ k′u bal pl
    ... | right pr = join-right⁺ lk′ k′u bal pr

    delete-tree⁻ : (t : Tree V l u n) (seg : l < k < u) →
                   Any P (proj₂ (delete k t seg)) →
                   Any P t
    delete-tree⁻ (node (k′ , v) lk′ k′u bal) (l<k , k<u) p
      with compare k′ k
    delete-tree⁻ (node kv@(k′ , v) lk′ k′u bal) (l<k , k<u) p
      | tri< k′<k _ _
      with joinʳ⁻⁻ kv lk′ (delete k k′u ([ k′<k ]ᴿ , k<u)) bal p
    ... | inj₁ pk = here pk
    ... | inj₂ (inj₁ pl) = left pl
    ... | inj₂ (inj₂ pr) = right (delete-tree⁻ k′u ([ k′<k ]ᴿ , k<u) pr)
    delete-tree⁻ (node kv@(k′ , v) lk′ k′u bal) (l<k , k<u) p
      | tri> _ _ k′>k
      with joinˡ⁻⁻ kv (delete k lk′ (l<k , [ k′>k ]ᴿ)) k′u bal p
    ... | inj₁ pk = here pk
    ... | inj₂ (inj₁ pl) = left (delete-tree⁻ lk′ (l<k , [ k′>k ]ᴿ) pl)
    ... | inj₂ (inj₂ pr) = right pr
    delete-tree⁻ (node (k′ , v) lk′ k′u bal) (l<k , k<u) p
      | tri≈ _ _ _ =
      join-node⁻ v lk′ k′u bal p


  module _ (k : Key) where

    open <-Reasoning AVL.strictPartialOrder

    delete-key-∈⁻ : (t : Tree V l u n) (seg : l < k < u) →
                    {kp : Key} →
                    Any ((kp ≈_) ∘′ key) (proj₂ (delete k t seg)) →
                    kp ≉ k
    delete-key-∈⁻ (node (k′ , v) lk′ k′u bal) (l<k , k<u) p kp≈k
      with compare k′ k
    delete-key-∈⁻ (node kv@(k′ , v) lk′ k′u bal) (l<k , k<u) {kp} p kp≈k
      | tri< k′<k k′≉k _
      with joinʳ⁻⁻ kv lk′ (delete k k′u ([ k′<k ]ᴿ , k<u)) bal p
    ... | inj₁ kp≈k′ = contradiction (trans (sym kp≈k′) kp≈k) k′≉k
    ... | inj₂ (inj₁ pl) = begin-contradiction
      [ k  ]                ≈⟨ [ sym kp≈k ]ᴱ ⟩
      [ kp ]                ≈⟨ [ lookup-result pl ]ᴱ ⟩
      [ Any.lookupKey pl ]  <⟨ proj₂ (lookup-bounded pl) ⟩
      [ k′ ]                <⟨ [ k′<k ]ᴿ ⟩
      [ k  ]                ∎
    ... | inj₂ (inj₂ pr) = delete-key-∈⁻ k′u ([ k′<k ]ᴿ , k<u) pr kp≈k
    delete-key-∈⁻ (node kv@(k′ , v) lk′ k′u bal) (l<k , k<u) {kp} p kp≈k
      | tri> _ k′≉k k′>k
      with joinˡ⁻⁻ kv (delete k lk′ (l<k , [ k′>k ]ᴿ)) k′u bal p
    ... | inj₁ kp≈k′ = contradiction (trans (sym kp≈k′) kp≈k) k′≉k
    ... | inj₂ (inj₁ pl) = delete-key-∈⁻ lk′ (l<k , [ k′>k ]ᴿ) pl kp≈k
    ... | inj₂ (inj₂ pr) = begin-contradiction
      [ k  ]                <⟨ [ k′>k ]ᴿ ⟩
      [ k′ ]                <⟨ proj₁ (lookup-bounded pr) ⟩
      [ Any.lookupKey pr ]  ≈⟨ [ sym (lookup-result pr) ]ᴱ ⟩
      [ kp ]                ≈⟨ [ kp≈k ]ᴱ ⟩
      [ k  ]                ∎
    delete-key-∈⁻ (node (k′ , v) lk′ k′u bal) (l<k , k<u) {kp} p kp≈k
      | tri≈ k′≮k _ k′≯k
      with join⁻ lk′ k′u bal p
    ... | inj₁ p₁ = contradiction
      (begin-strict
        [ k  ]                ≈⟨ [ sym kp≈k ]ᴱ ⟩
        [ kp ]                ≈⟨ [ lookup-result p₁ ]ᴱ ⟩
        [ Any.lookupKey p₁ ]  <⟨ proj₂ (lookup-bounded p₁) ⟩
        [ k′ ]                ∎)
      (k′≯k ∘′ [<]-injective)
    ... | inj₂ p₂ = contradiction
      (begin-strict
        [ k′  ]               <⟨ proj₁ (lookup-bounded p₂) ⟩
        [ Any.lookupKey p₂ ]  ≈⟨ [ sym (lookup-result p₂) ]ᴱ ⟩
        [ kp ]                ≈⟨ [ kp≈k ]ᴱ ⟩
        [ k ]                 ∎)
      (k′≮k ∘′ [<]-injective)


  module _ (k : Key) where

    delete-key⁻ : (t : Tree V l u n) (seg : l < k < u) →
                  (p : Any P (proj₂ (delete k t seg))) →
                  Any.lookupKey p ≉ k
    delete-key⁻ t seg p kp≈k =
      delete-key-∈⁻ k t seg (lookup-rebuild p Eq.refl) kp≈k
