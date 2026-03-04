------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties constant-time join functions related to Any
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.JoinConstFuns
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (∃; _,_; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed sto
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any

private
  variable
    v p : Level
    V : Value v
    P : Pred (K& V) p

----------------------------------------------------------------------
-- joinˡ⁺

joinˡ⁺-here⁺ : ∀ {l u hˡ hʳ h} →
             (kv : K& V) →
             (l : ∃ λ i → Tree V l [ kv .key ] (i ⊕ hˡ)) →
             (r : Tree V [ kv .key ] u hʳ) →
             (bal : hˡ ∼ hʳ ⊔ h) →
             P kv → Any P (proj₂ (joinˡ⁺ kv l r bal))
joinˡ⁺-here⁺ k₂ (0# , t₁)                       t₃ bal p = here p
joinˡ⁺-here⁺ k₂ (1# , t₁)                       t₃ ∼0  p = here p
joinˡ⁺-here⁺ k₂ (1# , t₁)                       t₃ ∼+  p = here p
joinˡ⁺-here⁺ k₄ (1# , node k₂ t₁ t₃ ∼-)         t₅ ∼-  p = right (here p)
joinˡ⁺-here⁺ k₄ (1# , node k₂ t₁ t₃ ∼0)         t₅ ∼-  p = right (here p)
joinˡ⁺-here⁺ k₆ (1# , node⁺ k₂ t₁ k₄ t₃ t₅ bal) t₇ ∼-  p = right (here p)

joinˡ⁺-left⁺ : ∀ {l u hˡ hʳ h} →
             (k : K& V) →
             (l : ∃ λ i → Tree V l [ k .key ] (i ⊕ hˡ)) →
             (r : Tree V [ k .key ] u hʳ) →
             (bal : hˡ ∼ hʳ ⊔ h) →
             Any P (proj₂ l) → Any P (proj₂ (joinˡ⁺ k l r bal))
joinˡ⁺-left⁺ k₂ (0# , t₁)                       t₃ bal p                 = left p
joinˡ⁺-left⁺ k₂ (1# , t₁)                       t₃ ∼0  p                 = left p
joinˡ⁺-left⁺ k₂ (1# , t₁)                       t₃ ∼+  p                 = left p
joinˡ⁺-left⁺ k₄ (1# , node k₂ t₁ t₃ ∼-)         t₅ ∼-  (here p)          = here p
joinˡ⁺-left⁺ k₄ (1# , node k₂ t₁ t₃ ∼-)         t₅ ∼-  (left p)          = left p
joinˡ⁺-left⁺ k₄ (1# , node k₂ t₁ t₃ ∼-)         t₅ ∼-  (right p)         = right (left p)
joinˡ⁺-left⁺ k₄ (1# , node k₂ t₁ t₃ ∼0)         t₅ ∼-  (here p)          = here p
joinˡ⁺-left⁺ k₄ (1# , node k₂ t₁ t₃ ∼0)         t₅ ∼-  (left p)          = left p
joinˡ⁺-left⁺ k₄ (1# , node k₂ t₁ t₃ ∼0)         t₅ ∼-  (right p)         = right (left p)
joinˡ⁺-left⁺ k₆ (1# , node⁺ k₂ t₁ k₄ t₃ t₅ bal) t₇ ∼-  (here p)          = left (here p)
joinˡ⁺-left⁺ k₆ (1# , node⁺ k₂ t₁ k₄ t₃ t₅ bal) t₇ ∼-  (left p)          = left (left p)
joinˡ⁺-left⁺ k₆ (1# , node⁺ k₂ t₁ k₄ t₃ t₅ bal) t₇ ∼-  (right (here p))  = here p
joinˡ⁺-left⁺ k₆ (1# , node⁺ k₂ t₁ k₄ t₃ t₅ bal) t₇ ∼-  (right (left p))  = left (right p)
joinˡ⁺-left⁺ k₆ (1# , node⁺ k₂ t₁ k₄ t₃ t₅ bal) t₇ ∼-  (right (right p)) = right (left p)

joinˡ⁺-right⁺ : ∀ {l u hˡ hʳ h} →
                (kv@(k , v) : K& V) →
                (l : ∃ λ i → Tree V l [ k ] (i ⊕ hˡ)) →
                (r : Tree V [ k ] u hʳ) →
                (bal : hˡ ∼ hʳ ⊔ h) →
                Any P r → Any P (proj₂ (joinˡ⁺ kv l r bal))
joinˡ⁺-right⁺ k₂ (0# , t₁)                       t₃ bal p = right p
joinˡ⁺-right⁺ k₂ (1# , t₁)                       t₃ ∼0  p = right p
joinˡ⁺-right⁺ k₂ (1# , t₁)                       t₃ ∼+  p = right p
joinˡ⁺-right⁺ k₄ (1# , node k₂ t₁ t₃ ∼-)         t₅ ∼-  p = right (right p)
joinˡ⁺-right⁺ k₄ (1# , node k₂ t₁ t₃ ∼0)         t₅ ∼-  p = right (right p)
joinˡ⁺-right⁺ k₆ (1# , node⁺ k₂ t₁ k₄ t₃ t₅ bal) t₇ ∼-  p = right (right p)

joinˡ⁺⁻ : ∀ {l u hˡ hʳ h} →
            (kv@(k , v) : K& V) →
            (l : ∃ λ i → Tree V l [ k ] (i ⊕ hˡ)) →
            (r : Tree V [ k ] u hʳ) →
            (bal : hˡ ∼ hʳ ⊔ h) →
            Any P (proj₂ (joinˡ⁺ kv l r bal)) →
            P kv ⊎ Any P (proj₂ l) ⊎ Any P r
joinˡ⁺⁻ k₂ (0# , t₁)                       t₃ ba = Any.toSum
joinˡ⁺⁻ k₂ (1# , t₁)                       t₃ ∼0 = Any.toSum
joinˡ⁺⁻ k₂ (1# , t₁)                       t₃ ∼+ = Any.toSum
joinˡ⁺⁻ k₄ (1# , node k₂ t₁ t₃ ∼-)         t₅ ∼- = λ where
  (left p)          → inj₂ (inj₁ (left p))
  (here p)          → inj₂ (inj₁ (here p))
  (right (left p))  → inj₂ (inj₁ (right p))
  (right (here p))  → inj₁ p
  (right (right p)) → inj₂ (inj₂ p)
joinˡ⁺⁻ k₄ (1# , node k₂ t₁ t₃ ∼0)         t₅ ∼- = λ where
  (left p)          → inj₂ (inj₁ (left p))
  (here p)          → inj₂ (inj₁ (here p))
  (right (left p))  → inj₂ (inj₁ (right p))
  (right (here p))  → inj₁ p
  (right (right p)) → inj₂ (inj₂ p)
joinˡ⁺⁻ k₆ (1# , node⁺ k₂ t₁ k₄ t₃ t₅ bal) t₇ ∼- = λ where
  (left (left p))   → inj₂ (inj₁ (left p))
  (left (here p))   → inj₂ (inj₁ (here p))
  (left (right p))  → inj₂ (inj₁ (right (left p)))
  (here p)          → inj₂ (inj₁ (right (here p)))
  (right (left p))  → inj₂ (inj₁ (right (right p)))
  (right (here p))  → inj₁ p
  (right (right p)) → inj₂ (inj₂ p)

----------------------------------------------------------------------
-- joinʳ⁺

joinʳ⁺-here⁺ : ∀ {l u hˡ hʳ h} →
               (kv : K& V) →
               (l : Tree V l [ kv .key ] hˡ) →
               (r : ∃ λ i → Tree V [ kv .key ] u (i ⊕ hʳ)) →
               (bal : hˡ ∼ hʳ ⊔ h) →
               P kv → Any P (proj₂ (joinʳ⁺ kv l r bal))
joinʳ⁺-here⁺ k₂ t₁ (0# , t₃)                       bal p = here p
joinʳ⁺-here⁺ k₂ t₁ (1# , t₃)                       ∼0  p = here p
joinʳ⁺-here⁺ k₂ t₁ (1# , t₃)                       ∼-  p = here p
joinʳ⁺-here⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼+)         ∼+  p = left (here p)
joinʳ⁺-here⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼0)         ∼+  p = left (here p)
joinʳ⁺-here⁺ k₂ t₁ (1# , node⁻ k₆ k₄ t₃ t₅ bal t₇) ∼+  p = left (here p)

joinʳ⁺-left⁺ : ∀ {l u hˡ hʳ h} →
              (kv : K& V) →
              (l : Tree V l [ kv .key ] hˡ) →
              (r : ∃ λ i → Tree V [ kv .key ] u (i ⊕ hʳ)) →
              (bal : hˡ ∼ hʳ ⊔ h) →
              Any P l → Any P (proj₂ (joinʳ⁺ kv l r bal))
joinʳ⁺-left⁺ k₂ t₁ (0# , t₃)                       bal p = left p
joinʳ⁺-left⁺ k₂ t₁ (1# , t₃)                       ∼0  p = left p
joinʳ⁺-left⁺ k₂ t₁ (1# , t₃)                       ∼-  p = left p
joinʳ⁺-left⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼+)         ∼+  p = left (left p)
joinʳ⁺-left⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼0)         ∼+  p = left (left p)
joinʳ⁺-left⁺ k₂ t₁ (1# , node⁻ k₆ k₄ t₃ t₅ bal t₇) ∼+  p = left (left p)

joinʳ⁺-right⁺ : ∀ {l u hˡ hʳ h} →
                (kv : K& V) →
                (l : Tree V l [ kv .key ] hˡ) →
                (r : ∃ λ i → Tree V [ kv .key ] u (i ⊕ hʳ)) →
                (bal : hˡ ∼ hʳ ⊔ h) →
                Any P (proj₂ r) → Any P (proj₂ (joinʳ⁺ kv l r bal))
joinʳ⁺-right⁺ k₂ t₁ (0# , t₃)                       bal p                = right p
joinʳ⁺-right⁺ k₂ t₁ (1# , t₃)                       ∼0  p                = right p
joinʳ⁺-right⁺ k₂ t₁ (1# , t₃)                       ∼-  p                = right p
joinʳ⁺-right⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼+)         ∼+  (here p)         = here p
joinʳ⁺-right⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼+)         ∼+  (left p)         = left (right p)
joinʳ⁺-right⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼+)         ∼+  (right p)        = right p
joinʳ⁺-right⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼0)         ∼+  (here p)         = here p
joinʳ⁺-right⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼0)         ∼+  (left p)         = left (right p)
joinʳ⁺-right⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼0)         ∼+  (right p)        = right p
joinʳ⁺-right⁺ k₂ t₁ (1# , node⁻ k₆ k₄ t₃ t₅ bal t₇) ∼+  (here p)         = right (here p)
joinʳ⁺-right⁺ k₂ t₁ (1# , node⁻ k₆ k₄ t₃ t₅ bal t₇) ∼+  (left (here p))  = here p
joinʳ⁺-right⁺ k₂ t₁ (1# , node⁻ k₆ k₄ t₃ t₅ bal t₇) ∼+  (left (left p))  = left (right p)
joinʳ⁺-right⁺ k₂ t₁ (1# , node⁻ k₆ k₄ t₃ t₅ bal t₇) ∼+  (left (right p)) = right (left p)
joinʳ⁺-right⁺ k₂ t₁ (1# , node⁻ k₆ k₄ t₃ t₅ bal t₇) ∼+  (right p)        = right (right p)

joinʳ⁺⁻ : ∀ {l u hˡ hʳ h} →
            (kv : K& V) →
            (l : Tree V l [ kv .key ] hˡ) →
            (r : ∃ λ i → Tree V [ kv .key ] u (i ⊕ hʳ)) →
            (bal : hˡ ∼ hʳ ⊔ h) →
            Any P (proj₂ (joinʳ⁺ kv l r bal)) →
            P kv ⊎ Any P l ⊎ Any P (proj₂ r)
joinʳ⁺⁻ k₂ t₁ (0# , t₃)                       bal = Any.toSum
joinʳ⁺⁻ k₂ t₁ (1# , t₃)                       ∼0  = Any.toSum
joinʳ⁺⁻ k₂ t₁ (1# , t₃)                       ∼-  = Any.toSum
joinʳ⁺⁻ k₂ t₁ (1# , node k₄ t₃ t₅ ∼+)         ∼+  = λ where
  (left (left p))  → inj₂ (inj₁ p)
  (left (here p))  → inj₁ p
  (left (right p)) → inj₂ (inj₂ (left p))
  (here p)         → inj₂ (inj₂ (here p))
  (right p)        → inj₂ (inj₂ (right p))
joinʳ⁺⁻ k₂ t₁ (1# , node k₄ t₃ t₅ ∼0)         ∼+  = λ where
  (left (left p))  → inj₂ (inj₁ p)
  (left (here p))  → inj₁ p
  (left (right p)) → inj₂ (inj₂ (left p))
  (here p)         → inj₂ (inj₂ (here p))
  (right p)        → inj₂ (inj₂ (right p))
joinʳ⁺⁻ k₂ t₁ (1# , node⁻ k₆ k₄ t₃ t₅ bal t₇) ∼+  = λ where
  (left (left p))   → inj₂ (inj₁ p)
  (left (here p))   → inj₁ p
  (left (right p))  → inj₂ (inj₂ (left (left p)))
  (here p)          → inj₂ (inj₂ (left (here p)))
  (right (left p))  → inj₂ (inj₂ (left (right p)))
  (right (here p))  → inj₂ (inj₂ (here p))
  (right (right p)) → inj₂ (inj₂ (right p))

----------------------------------------------------------------------
-- joinˡ⁻

joinˡ⁻-here⁺ : ∀ {l u hˡ hʳ h} →
             (kv : K& V) →
             (l : ∃ λ i → Tree V l [ kv .key ] pred[ i ⊕ hˡ ]) →
             (r : Tree V [ kv .key ] u hʳ) →
             (bal : hˡ ∼ hʳ ⊔ h) →
             P kv →
             Any P (proj₂ (joinˡ⁻ hˡ kv l r bal))
joinˡ⁻-here⁺ {hˡ = zero}  k₂ (0# , t₁) t₃ bal p = here p
joinˡ⁻-here⁺ {hˡ = zero}  k₂ (1# , t₁) t₃ bal p = here p
joinˡ⁻-here⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼+  p =
  joinʳ⁺-here⁺ k₂ t₁ (1# , t₃) ∼+ p
joinˡ⁻-here⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0  p = here p
joinˡ⁻-here⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼-  p = here p
joinˡ⁻-here⁺ {hˡ = suc _} k₂ (1# , t₁) t₃ bal p = here p

joinˡ⁻-left⁺ : ∀ {l u hˡ hʳ h} →
             (kv : K& V) →
             (l : ∃ λ i → Tree V l [ kv .key ] pred[ i ⊕ hˡ ]) →
             (r : Tree V [ kv .key ] u hʳ) →
             (bal : hˡ ∼ hʳ ⊔ h) →
             Any P (proj₂ l) → Any P (proj₂ (joinˡ⁻ hˡ kv l r bal))
joinˡ⁻-left⁺ {hˡ = zero}  k₂ (0# , t₁) t₃ bal p = left p
joinˡ⁻-left⁺ {hˡ = zero}  k₂ (1# , t₁) t₃ bal p = left p
joinˡ⁻-left⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼+  p =
  joinʳ⁺-left⁺ k₂ t₁ (1# , t₃) ∼+ p
joinˡ⁻-left⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0  p = left p
joinˡ⁻-left⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼-  p = left p
joinˡ⁻-left⁺ {hˡ = suc _} k₂ (1# , t₁) t₃ bal p = left p

joinˡ⁻-right⁺ : ∀ {l u hˡ hʳ h} →
              (kv : K& V) →
              (l : ∃ λ i → Tree V l [ kv .key ] pred[ i ⊕ hˡ ]) →
              (r : Tree V [ kv .key ] u hʳ) →
              (bal : hˡ ∼ hʳ ⊔ h) →
              Any P r → Any P (proj₂ (joinˡ⁻ hˡ kv l r bal))
joinˡ⁻-right⁺ {hˡ = zero}  k₂ (0# , t₁) t₃ bal p = right p
joinˡ⁻-right⁺ {hˡ = zero}  k₂ (1# , t₁) t₃ bal p = right p
joinˡ⁻-right⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼+  p =
  joinʳ⁺-right⁺ k₂ t₁ (1# , t₃) ∼+ p
joinˡ⁻-right⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0  p = right p
joinˡ⁻-right⁺ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼-  p = right p
joinˡ⁻-right⁺ {hˡ = suc _} k₂ (1# , t₁) t₃ bal p = right p

joinˡ⁻⁻ : ∀ {l u hˡ hʳ h} →
        (kv : K& V) →
        (l : ∃ λ i → Tree V l [ kv .key ] pred[ i ⊕ hˡ ]) →
        (r : Tree V [ kv .key ] u hʳ) →
        (bal : hˡ ∼ hʳ ⊔ h) →
        Any P (proj₂ (joinˡ⁻ hˡ kv l r bal)) →
        P kv ⊎ Any P (proj₂ l) ⊎ Any P r
joinˡ⁻⁻ {hˡ = zero} k₂ (0# , t₁) t₃ bal (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = zero} k₂ (0# , t₁) t₃ bal (right p) = inj₂ (inj₂ p)
joinˡ⁻⁻ {hˡ = zero} k₂ (1# , t₁) t₃ bal (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = zero} k₂ (1# , t₁) t₃ bal (right p) = inj₂ (inj₂ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼+  p =
  joinʳ⁺⁻ k₂ t₁ (1# , t₃) ∼+ p
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0 (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0 (left p) = inj₂ (inj₁ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼0 (right p) = inj₂ (inj₂ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼- (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼- (left p) = inj₂ (inj₁ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (0# , t₁) t₃ ∼- (right p) = inj₂ (inj₂ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (1# , t₁) t₃ bal (here p) = inj₁ p
joinˡ⁻⁻ {hˡ = suc _} k₂ (1# , t₁) t₃ bal (left p) = inj₂ (inj₁ p)
joinˡ⁻⁻ {hˡ = suc _} k₂ (1# , t₁) t₃ bal (right p) = inj₂ (inj₂ p)

----------------------------------------------------------------------
-- joinʳ⁻

joinʳ⁻-here⁺ : ∀ {l u hˡ hʳ h} →
             (kv : K& V) →
             (l : Tree V l [ kv .key ] hˡ) →
             (r : ∃ λ i → Tree V [ kv .key ] u pred[ i ⊕ hʳ ]) →
             (bal : hˡ ∼ hʳ ⊔ h) →
             P kv → Any P (proj₂ (joinʳ⁻ hʳ kv l r bal))
joinʳ⁻-here⁺ {hʳ = zero}  k₂ t₁ (0# , t₃) bal p = here p
joinʳ⁻-here⁺ {hʳ = zero}  k₂ t₁ (1# , t₃) bal p = here p
joinʳ⁻-here⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼-  p =
  joinˡ⁺-here⁺ k₂ (1# , t₁) t₃ ∼- p
joinʳ⁻-here⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  p = here p
joinʳ⁻-here⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  p = here p
joinʳ⁻-here⁺ {hʳ = suc _} k₂ t₁ (1# , t₃) bal p = here p

joinʳ⁻-left⁺ : ∀ {l u hˡ hʳ h} →
             (kv : K& V) →
             (l : Tree V l [ kv .key ] hˡ) →
             (r : ∃ λ i → Tree V [ kv .key ] u pred[ i ⊕ hʳ ]) →
             (bal : hˡ ∼ hʳ ⊔ h) →
             Any P l → Any P (proj₂ (joinʳ⁻ hʳ kv l r bal))
joinʳ⁻-left⁺ {hʳ = zero}  k₂ t₁ (0# , t₃) bal p = left p
joinʳ⁻-left⁺ {hʳ = zero}  k₂ t₁ (1# , t₃) bal p = left p
joinʳ⁻-left⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼-  p =
  joinˡ⁺-left⁺ k₂ (1# , t₁) t₃ ∼- p
joinʳ⁻-left⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  p = left p
joinʳ⁻-left⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  p = left p
joinʳ⁻-left⁺ {hʳ = suc _} k₂ t₁ (1# , t₃) bal p = left p

joinʳ⁻-right⁺ : ∀ {l u hˡ hʳ h} →
              (kv : K& V) →
              (l : Tree V l [ kv .key ] hˡ) →
              (r : ∃ λ i → Tree V [ kv .key ] u pred[ i ⊕ hʳ ]) →
              (bal : hˡ ∼ hʳ ⊔ h) →
              Any P (proj₂ r) → Any P (proj₂ (joinʳ⁻ hʳ kv l r bal))
joinʳ⁻-right⁺ {hʳ = zero}  k₂ t₁ (0# , t₃) bal p = right p
joinʳ⁻-right⁺ {hʳ = zero}  k₂ t₁ (1# , t₃) bal p = right p
joinʳ⁻-right⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼-  p =
  joinˡ⁺-right⁺ k₂ (1# , t₁) t₃ ∼- p
joinʳ⁻-right⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  p = right p
joinʳ⁻-right⁺ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  p = right p
joinʳ⁻-right⁺ {hʳ = suc _} k₂ t₁ (1# , t₃) bal p = right p

joinʳ⁻⁻ : ∀ {l u hˡ hʳ h} →
        (kv : K& V) →
        (l : Tree V l [ kv .key ] hˡ) →
        (r : ∃ λ i → Tree V [ kv .key ] u pred[ i ⊕ hʳ ]) →
        (bal : hˡ ∼ hʳ ⊔ h) →
        Any P (proj₂ (joinʳ⁻ hʳ kv l r bal)) →
        P kv ⊎ Any P l ⊎ Any P (proj₂ r)
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (0# , t₃) bal (here p) = inj₁ p
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (0# , t₃) bal (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (0# , t₃) bal (right p) = inj₂ (inj₂ p)
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (1# , t₃) bal (here p) = inj₁ p
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (1# , t₃) bal (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = zero}  k₂ t₁ (1# , t₃) bal (right p) = inj₂ (inj₂ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼-  p =
  joinˡ⁺⁻ k₂ (1# , t₁) t₃ ∼- p
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  (here p) = inj₁ p
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼0  (right p) = inj₂ (inj₂ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  (here p) = inj₁ p
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (0# , t₃) ∼+  (right p) = inj₂ (inj₂ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (1# , t₃) bal (here p) = inj₁ p
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (1# , t₃) bal (left p) = inj₂ (inj₁ p)
joinʳ⁻⁻ {hʳ = suc _} k₂ t₁ (1# , t₃) bal (right p) = inj₂ (inj₂ p)
