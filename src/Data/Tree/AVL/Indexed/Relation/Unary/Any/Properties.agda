------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Any
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Maybe.Relation.Unary.All as Maybe using (nothing; just)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Function.Base as F
open import Level using (Level)

open import Relation.Binary using (_Respects_; tri<; tri≈; tri>)
open import Relation.Unary using (Pred)

open import Data.Tree.AVL.Indexed strictTotalOrder as AVL
open import Data.Tree.AVL.Indexed.Relation.Unary.Any strictTotalOrder as Any
open StrictTotalOrder strictTotalOrder renaming (Carrier to Key); open Eq using (_≉_; sym; refl)


private
  variable
    v p q : Level
    V : Value v
    l u : Key⁺
    n : ℕ
    P : Pred (K& V) p

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

------------------------------------------------------------------------
-- insert

module _ {V : Value v} where

  private Val = Value.family V

  Any-insertWith :
    ∀ {l u h} (k : Key) →
    (f : Maybe (Val k) → Val k) →
    (Pf : ∀ {k′} → (eq : k ≈ k′) (mk′ : Maybe (Val k′)) →
          maybe′ (λ v → P (k′ , Value.respects V eq (f (just (Value.respects V (sym eq) v)))))
                 (P (k , f nothing)) mk′)
    (t : Tree V l u h) (seg : l < k < u) →
    Any P (proj₂ (insertWith k f t seg))
  Any-insertWith k f Pf (leaf l<u) l<k<u = here (Pf refl nothing)
  Any-insertWith k f Pf (node kv@(k′ , v′) lp pu bal) (l<k , k<u) with compare k k′
  ... | tri< k<k′ _ _ = joinˡ⁺-left⁺ kv (insertWith k f lp _) pu bal (Any-insertWith k f Pf lp (l<k , [ k<k′ ]ᴿ))
  ... | tri> _ _ k′<k = joinʳ⁺-right⁺ kv lp (insertWith k f pu _) bal (Any-insertWith k f Pf pu ([ k′<k ]ᴿ , k<u))
  ... | tri≈ _ k≈k′ _ = here (Pf k≈k′ (just v′))

  Any-insert :
    (P≈ : ∀ {k k′} v (eq : k ≈ k′) → P (k , v) → P (k′ , Value.respects V eq v)) →
    ∀ {l u h} (k : Key) (v : Val k) → (Pv : P (k , v))
    (t : Tree V l u h) (seg : l < k < u) →
    Any P (proj₂ (insert k v t seg))
  Any-insert P≈ k v Pv = Any-insertWith k (F.const v) $ λ where
    eq nothing   → Pv
    eq (just v′) → P≈ v eq Pv

  insert⁺ : ∀ {l u h} (k : Key) (f : Maybe (Val k) → Val k) (t : Tree V l u h) (seg : l < k < u) →
     (p : Any P t) → k ≉ Any.lookup p → Any P (proj₂ (insertWith k f t seg))
  insert⁺ k f (node (k′ , v′) l r bal) (l<k , k<u) p k≉ with compare k k′
  insert⁺ k f (node kv@(k′ , v′) l r bal) (l<k , k<u) (here p)  k≉ | tri< k<k′ _ _
    = joinˡ⁺-here⁺ kv (insertWith k f l (l<k , [ k<k′ ]ᴿ)) r bal p
  insert⁺ k f (node kv@(k′ , v′) l r bal) (l<k , k<u) (left p)  k≉ | tri< k<k′ _ _
    = joinˡ⁺-left⁺ kv (insertWith k f l (l<k , [ k<k′ ]ᴿ)) r bal (insert⁺ k f l _ p k≉)
  insert⁺ k f (node kv@(k′ , v′) l r bal) (l<k , k<u) (right p) k≉ | tri< k<k′ _ _
    = joinˡ⁺-right⁺ kv (insertWith k f l (l<k , [ k<k′ ]ᴿ)) r bal p
  insert⁺ k f (node kv@(k′ , v′) l r bal) (l<k , k<u) (here p)  k≉ | tri> _ _ k′<k
    = joinʳ⁺-here⁺ kv l (insertWith k f r ([ k′<k ]ᴿ , k<u)) bal p
  insert⁺ k f (node kv@(k′ , v′) l r bal) (l<k , k<u) (left p)  k≉ | tri> _ _ k′<k
    = joinʳ⁺-left⁺ kv l (insertWith k f r ([ k′<k ]ᴿ , k<u)) bal p
  insert⁺ k f (node kv@(k′ , v′) l r bal) (l<k , k<u) (right p) k≉ | tri> _ _ k′<k
    = joinʳ⁺-right⁺ kv l (insertWith k f r ([ k′<k ]ᴿ , k<u)) bal (insert⁺ k f r _ p k≉)
  insert⁺ k f (node (k′ , v′) l r bal) (l<k , k<u) (here p)  k≉ | tri≈ _ k≈k′ _ = ⊥-elim (k≉ k≈k′)
  insert⁺ k f (node (k′ , v′) l r bal) (l<k , k<u) (left p)  k≉ | tri≈ _ k≈k′ _ = left p
  insert⁺ k f (node (k′ , v′) l r bal) (l<k , k<u) (right p) k≉ | tri≈ _ k≈k′ _ = right p
