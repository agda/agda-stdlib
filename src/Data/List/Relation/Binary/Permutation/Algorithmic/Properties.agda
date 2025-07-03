-------------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the `Algorithmic` definition of the permutation relation.
-------------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Permutation.Algorithmic.Properties
  {s ℓ} (S : Setoid s ℓ) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
import Relation.Binary.PropositionalEquality as ≡
  using (sym)

open import Data.List.Relation.Binary.Equality.Setoid S as ≋
  using (≋-reflexive)
open import Data.List.Relation.Binary.Permutation.Algorithmic S
import Data.List.Relation.Binary.Permutation.Setoid S as ↭ₛ
  using (_↭_; refl; prep; swap; trans; ↭-refl; ↭-prep; ↭-swap; ↭-trans)

open Setoid S
  renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

private
  variable
    a b c d : A
    as bs cs ds : List A


-------------------------------------------------------------------------------
-- Properties

↭-swap : a ≈ c → b ≈ d → cs ↭ ds → a ∷ b ∷ cs ↭ d ∷ c ∷ ds
↭-swap a≈c b≈d cs≈ds = (b≈d ∷ cs≈ds) ⋎ (a≈c ∷ ↭-refl _)

↭-swap-++ : (as bs : List A) → as ++ bs ↭ bs ++ as
↭-swap-++ [] bs = ↭-reflexive (≋-reflexive (≡.sym (++-identityʳ bs)))
↭-swap-++ (a ∷ as) bs = lemma bs (↭-swap-++ as bs)
  where
  lemma : ∀ bs → cs ↭ bs ++ as → a ∷ cs ↭ bs ++ a ∷ as
  lemma []        cs↭as
    = a ≡∷ cs↭as
  lemma (b ∷ bs) (a≈b ∷ cs↭bs++as)
    = (a≈b ∷ ↭-refl _) ⋎ lemma bs cs↭bs++as
  lemma (b ∷ bs) (cs↭b∷ds ⋎ a∷ds↭bs++as)
    = (cs↭b∷ds ⋎ (↭-refl _)) ⋎ (lemma bs a∷ds↭bs++as)

↭-congʳ : ∀ cs → as ↭ bs → cs ++ as ↭ cs ++ bs
↭-congʳ {as = as} {bs = bs} cs as↭bs = lemma cs
  where
  lemma : ∀ cs → cs ++ as ↭ cs ++ bs
  lemma []       = as↭bs
  lemma (c ∷ cs) = c ≡∷ lemma cs

↭-congˡ : as ↭ bs → ∀ cs → as ++ cs ↭ bs ++ cs
↭-congˡ as↭bs cs = lemma as↭bs
  where
  lemma : as ↭ bs → as ++ cs ↭ bs ++ cs
  lemma []                  = ↭-refl cs
  lemma (a≈b ∷ as↭bs)       = a≈b ∷ lemma as↭bs
  lemma (as↭b∷xs ⋎ bs↭a∷xs) = lemma as↭b∷xs ⋎ lemma bs↭a∷xs

↭-cong : as ↭ bs → cs ↭ ds → as ++ cs ↭ bs ++ ds
↭-cong as↭bs cs↭ds = ↭-trans (↭-congˡ as↭bs _) (↭-congʳ _ cs↭ds)

-------------------------------------------------------------------------------
-- Equivalence with `Setoid` definition of _↭_

↭ₛ⇒↭ : as ↭ₛ.↭ bs → as ↭ bs
↭ₛ⇒↭ (↭ₛ.refl as≋bs)         = ↭-reflexive as≋bs
↭ₛ⇒↭ (↭ₛ.prep a≈b as↭bs)     = a≈b ∷ ↭ₛ⇒↭ as↭bs
↭ₛ⇒↭ (↭ₛ.swap a≈c b≈d cs↭ds) = ↭-swap a≈c b≈d (↭ₛ⇒↭ cs↭ds)
↭ₛ⇒↭ (↭ₛ.trans as↭bs bs↭cs)  = ↭-trans (↭ₛ⇒↭ as↭bs) (↭ₛ⇒↭ bs↭cs)

↭⇒↭ₛ : as ↭ bs → as ↭ₛ.↭ bs
↭⇒↭ₛ []                  = ↭ₛ.↭-refl
↭⇒↭ₛ (a≈b ∷ as↭bs)       = ↭ₛ.prep a≈b (↭⇒↭ₛ as↭bs)
↭⇒↭ₛ (as↭b∷cs ⋎ a∷cs↭bs) = ↭ₛ.↭-trans (↭ₛ.↭-prep _ (↭⇒↭ₛ as↭b∷cs))
                            (↭ₛ.↭-trans (↭ₛ.↭-swap _ _ ↭ₛ.↭-refl)
                               (↭ₛ.↭-prep _ (↭⇒↭ₛ a∷cs↭bs)))
