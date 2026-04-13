------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of delete related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Delete
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Level using (Level)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto as AVL
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Lookup sto
  using (lookup-bounded; lookup-result; lookup-rebuild)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Join sto
  using (join-left⁺; join-right⁺; join⁻)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.JoinLemmas sto
  using (joinʳ⁻-here⁺; joinʳ⁻-left⁺; joinʳ⁻-right⁺; joinˡ⁻-here⁺;
         joinˡ⁻-left⁺; joinˡ⁻-right⁺; joinʳ⁻⁻; joinˡ⁻⁻)
open StrictTotalOrder sto
  using (_<_; _≈_; module Eq; compare)
  renaming (Carrier to Key; trans to <-trans)
open Eq using (_≉_; sym; trans)

open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

import Relation.Binary.Reasoning.StrictPartialOrder as <-Reasoning

private
  variable
    v p : Level
    V : Value v
    l u : Key⁺
    h : ℕ
    P : Pred (K& V) p


module _ (k : Key) where

  delete⁺ : (t : Tree V l u h) (seg : l < k < u) →
            (p : Any P t) → k # p →
            Any P (proj₂ (delete k t seg))
  delete⁺ (node (k′ , _) _ _ bal) _ (here pk) p≉k
    with compare k′ k
  ... | tri< _ _ _    = joinʳ⁻-here⁺ _ _ _ bal pk
  ... | tri> _ _ _    = joinˡ⁻-here⁺ _ _ _ bal pk
  ... | tri≈ _ k′≈k _ = contradiction k′≈k p≉k
  delete⁺ (node (k′ , _) lk′ k′u bal) (l<k , _) (left pl) p≉k
    with compare k′ k
  ... | tri< _ _ _    = joinʳ⁻-left⁺ _ _ _ bal pl
  ... | tri> _ _ k′>k = joinˡ⁻-left⁺ _ _ _ bal
                          (delete⁺ lk′ (l<k , [ k′>k ]ᴿ) pl p≉k)
  ... | tri≈ _ _ _    = join-left⁺ _ k′u bal pl
  delete⁺ (node (k′ , _) _ k′u bal) (_ , k<u) (right pr) p≉k
    with compare k′ k
  ... | tri< k′<k _ _ = joinʳ⁻-right⁺ _ _ _ bal
                          (delete⁺ k′u ([ k′<k ]ᴿ , k<u) pr p≉k)
  ... | tri> _ _ k′>k = joinˡ⁻-right⁺ _ _ _ bal pr
  ... | tri≈ _ _ _    = join-right⁺ _ _ bal pr

  delete-tree⁻ : (t : Tree V l u h) (seg : l < k < u) →
                 Any P (proj₂ (delete k t seg)) →
                 Any P t
  delete-tree⁻ (node (k′ , _) _ _ _) _ _ with compare k′ k
  delete-tree⁻ (node kv _ k′u bal) (_ , k<u) p | tri< k′<k _ _
    with joinʳ⁻⁻ _ _ _ bal p
  ... | inj₁ pk        = here pk
  ... | inj₂ (inj₁ pl) = left pl
  ... | inj₂ (inj₂ pr) = right (delete-tree⁻ k′u ([ k′<k ]ᴿ , k<u) pr)
  delete-tree⁻ (node kv lk′ _ bal) (l<k , _) p | tri> _ _ k′>k
    with joinˡ⁻⁻ _ _ _ bal p
  ... | inj₁ pk        = here pk
  ... | inj₂ (inj₁ pl) = left (delete-tree⁻ lk′ (l<k , [ k′>k ]ᴿ) pl)
  ... | inj₂ (inj₂ pr) = right pr
  delete-tree⁻ (node _ lk′ k′u bal) _ p | tri≈ _ _ _ =
    Sum.[ (λ p → left p) , (λ p → right p) ]′ (join⁻ lk′ k′u bal p)


module _ (k : Key) where

  open <-Reasoning AVL.strictPartialOrder

  delete-key-∈⁻ : (t : Tree V l u h) (seg : l < k < u) →
                  {kp : Key} →
                  Any ((kp ≈_) ∘′ key) (proj₂ (delete k t seg)) →
                  kp ≉ k
  delete-key-∈⁻ (node (k′ , _) _ _ _) _ _ _
    with compare k′ k
  delete-key-∈⁻ (node (k′ , _) _ k′u bal) (_ , k<u) {kp} p kp≈k
    | tri< k′<k k′≉k _
    with joinʳ⁻⁻ _ _ _ bal p
  ... | inj₁ kp≈k′     = contradiction (trans (sym kp≈k′) kp≈k) k′≉k
  ... | inj₂ (inj₁ pl) = begin-contradiction
    [ k  ]            ≈⟨ [ kp≈k ]ᴱ ⟨
    [ kp ]            ≈⟨ [ lookup-result pl ]ᴱ ⟩
    [ lookupKey pl ]  <⟨ proj₂ (lookup-bounded pl) ⟩
    [ k′ ]            <⟨ [ k′<k ]ᴿ ⟩
    [ k  ]            ∎
  ... | inj₂ (inj₂ pr) = delete-key-∈⁻ k′u ([ k′<k ]ᴿ , k<u) pr kp≈k
  delete-key-∈⁻ (node (k′ , _) lk′ _ bal) (l<k , _) {kp} p kp≈k
    | tri> _ k′≉k k′>k
    with joinˡ⁻⁻ _ _ _ bal p
  ... | inj₁ kp≈k′     = contradiction (trans (sym kp≈k′) kp≈k) k′≉k
  ... | inj₂ (inj₁ pl) = delete-key-∈⁻ lk′ (l<k , [ k′>k ]ᴿ) pl kp≈k
  ... | inj₂ (inj₂ pr) = begin-contradiction
    [ k  ]            <⟨ [ k′>k ]ᴿ ⟩
    [ k′ ]            <⟨ proj₁ (lookup-bounded pr) ⟩
    [ lookupKey pr ]  ≈⟨ [ lookup-result pr ]ᴱ ⟨
    [ kp ]            ≈⟨ [ kp≈k ]ᴱ ⟩
    [ k  ]            ∎
  delete-key-∈⁻ (node (k′ , _) _ k′u bal) _ {kp} p kp≈k
    | tri≈ k′≮k _ k′≯k
    with join⁻ _ k′u bal p
  ... | inj₁ p₁ = contradiction
    (begin-strict
      [ k  ]            ≈⟨ [ kp≈k ]ᴱ ⟨
      [ kp ]            ≈⟨ [ lookup-result p₁ ]ᴱ ⟩
      [ lookupKey p₁ ]  <⟨ proj₂ (lookup-bounded p₁) ⟩
      [ k′ ]            ∎)
    (k′≯k ∘′ [<]-injective)
  ... | inj₂ p₂ = contradiction
    (begin-strict
      [ k′  ]           <⟨ proj₁ (lookup-bounded p₂) ⟩
      [ lookupKey p₂ ]  ≈⟨ [ lookup-result p₂ ]ᴱ ⟨
      [ kp ]            ≈⟨ [ kp≈k ]ᴱ ⟩
      [ k ]             ∎)
    (k′≮k ∘′ [<]-injective)


module _ (k : Key) where

  delete-key⁻ : (t : Tree V l u h) (seg : l < k < u) →
                (p : Any P (proj₂ (delete k t seg))) →
                k # p
  delete-key⁻ t seg p kp≈k =
    delete-key-∈⁻ k t seg (lookup-rebuild p Eq.refl) kp≈k
