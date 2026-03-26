------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of lookup related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.LookupFun
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Maybe.Base using (Maybe; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to ≡-refl)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto as AVL
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open StrictTotalOrder sto renaming (Carrier to Key; trans to <-trans); open Eq using (sym; trans)

open import Relation.Binary.Construct.Add.Extrema.Strict _<_ using ([<]-injective)

private
  variable
    v p : Level
    V : Value v
    l u : Key⁺
    n : ℕ
    P : Pred (K& V) p

open import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties.Lookup sto
  using (lookup-bounded)

module _ {V : Value v} where

  private
    Val  = Value.family V
    Val≈ = Value.respects V

  lookup⁺ : (t : Tree V l u n) (k : Key) (seg : l < k < u) →
            (p : Any P t) →
            (key (Any.lookup p) ≉ k)
            ⊎ (∃[ p≈k ] AVL.lookup t k seg
               ≡ just (Val≈ p≈k (value (Any.lookup p))))
  lookup⁺ (node (k′ , v′) l r bal) k (l<k , k<u) p
      with compare k′ k | p
  ... | tri< k′<k _ _ | right p = lookup⁺ r k ([ k′<k ]ᴿ , k<u) p
  ... | tri≈ _ k′≈k _ | here p = inj₂ (k′≈k , ≡-refl)
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

  lookup⁻ : (t : Tree V l u n) (k : Key) (v : Val k) (seg : l < k < u) →
            AVL.lookup t k seg ≡ just v →
            Any (λ{ (k′ , v′) → ∃ λ k′≈k → Val≈ k′≈k v′ ≡ v}) t
  lookup⁻ (node (k′ , v′) l r bal) k v (l<k , k<u) eq with compare k′ k
  ... | tri< k′<k _ _ = right (lookup⁻ r k v ([ k′<k ]ᴿ , k<u) eq)
  ... | tri≈ _ k′≈k _ = here (k′≈k , just-injective eq)
  ... | tri> _ _ k<k′ = left (lookup⁻ l k v (l<k , [ k<k′ ]ᴿ) eq)
