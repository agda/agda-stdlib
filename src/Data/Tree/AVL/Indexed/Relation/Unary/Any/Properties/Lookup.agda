------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of lookup related to Any
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Lookup
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Maybe.Base using (Maybe; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base as Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (flip)
open import Level using (Level)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Unary using (Pred; _∩_)

open import Data.Tree.AVL.Indexed sto as AVL hiding (lookup)
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any

open StrictTotalOrder sto
  using (_<_; module Eq; compare; irrefl)
  renaming (Carrier to Key; trans to <-trans)
open Eq using (sym; trans)

open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

private
  variable
    v p : Level
    V : Value v
    l u : Key⁺
    h : ℕ
    P Q : Pred (K& V) p
    t : Tree V l u h


----------------------------------------------------------------------
-- lookup

lookup-result : (p : Any P t) → P (lookup p)
lookup-result (here p)  = p
lookup-result (left p)  = lookup-result p
lookup-result (right p) = lookup-result p

lookup-bounded : (p : Any P {l = l} {u = u} t) → l < lookupKey p < u
lookup-bounded {t = node _ lk ku _} (here p) = ordered lk , ordered ku
lookup-bounded {t = node _ _  ku _} (left p) =
  Product.map₂ (flip (trans⁺ _) (ordered ku)) (lookup-bounded p)
lookup-bounded {t = node _ lk _ _} (right p) =
  Product.map₁ (trans⁺ _ (ordered lk)) (lookup-bounded p)

lookup-rebuild : (p : Any P t) → Q (lookup p) → Any Q t
lookup-rebuild (here _)  q = here q
lookup-rebuild (left p)  q = left (lookup-rebuild p q)
lookup-rebuild (right p) q = right (lookup-rebuild p q)

lookup-rebuild-accum : (p : Any P t) → Q (lookup p) → Any (Q ∩ P) t
lookup-rebuild-accum p q = lookup-rebuild p (q , lookup-result p)


----------------------------------------------------------------------
-- Relating Any.lookup to AVL.lookup

module _ {V : Value v} (open Value V using (respects) renaming (family to Val)) where

  lookup⁺ : (t : Tree V l u h) (k : Key) (l<k<u : l < k < u) →
            (p : Any P t) →
            k # p
            ⊎ ∃[ p≈k ] AVL.lookup t k l<k<u ≡ just (respects p≈k (value (lookup p)))
  lookup⁺ (node (k′ , v′) l r bal) k (l<k , k<u) p
      with compare k′ k | p
  ... | tri< k′<k _ _ | right p = lookup⁺ r k ([ k′<k ]ᴿ , k<u) p
  ... | tri≈ _ k′≈k _ | here p = inj₂ (k′≈k , refl)
  ... | tri> _ _ k<k′ | left p = lookup⁺ l k (l<k , [ k<k′ ]ᴿ) p
  ... | tri< k′<k _ _ | left p = inj₁ (λ p≈k → irrefl p≈k (<-trans p<k′ k′<k))
    where p<k′ = [<]-injective (proj₂ (lookup-bounded p))
  ... | tri< k′<k _ _ | here p = inj₁ (λ p≈k → irrefl p≈k k′<k)
  ... | tri≈ _ k′≈k _ | left p = inj₁ (λ p≈k → irrefl (trans p≈k (sym k′≈k)) p<k′)
    where p<k′ = [<]-injective (proj₂ (lookup-bounded p))
  ... | tri≈ _ k′≈k _ | right p = inj₁ (λ p≈k → irrefl (trans k′≈k (sym p≈k)) k′<p)
    where k′<p = [<]-injective (proj₁ (lookup-bounded p))
  ... | tri> _ _ k<k′ | here p = inj₁ (λ p≈k → irrefl (sym p≈k) k<k′)
  ... | tri> _ _ k<k′ | right p = inj₁ (λ p≈k → irrefl (sym p≈k) (<-trans k<k′ k′<p))
    where k′<p = [<]-injective (proj₁ (lookup-bounded p))

  lookup⁻ : (t : Tree V l u h) (k : Key) (v : Val k) (seg : l < k < u) →
            AVL.lookup t k seg ≡ just v →
            Any (λ{ (k′ , v′) → ∃ λ k′≈k → respects k′≈k v′ ≡ v}) t
  lookup⁻ (node (k′ , v′) l r bal) k v (l<k , k<u) eq with compare k′ k
  ... | tri< k′<k _ _ = right (lookup⁻ r k v ([ k′<k ]ᴿ , k<u) eq)
  ... | tri≈ _ k′≈k _ = here (k′≈k , just-injective eq)
  ... | tri> _ _ k<k′ = left (lookup⁻ l k v (l<k , [ k<k′ ]ᴿ) eq)
