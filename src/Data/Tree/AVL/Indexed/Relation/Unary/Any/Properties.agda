------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Any
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties
  {a ℓ₁ ℓ₂} (sto : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Maybe.Relation.Unary.All as Maybe using (nothing; just)
open import Data.Nat.Base using (ℕ)
open import Data.Product as Prod using (∃; _,_; proj₂)
open import Function.Base as F
open import Level using (Level)

open import Relation.Binary using (_Respects_; tri<; tri≈; tri>)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Data.Tree.AVL.Indexed sto as AVL
open import Data.Tree.AVL.Indexed.Relation.Unary.Any sto as Any
open StrictTotalOrder sto renaming (Carrier to Key); open Eq using (_≉_; sym; refl)

import Relation.Binary.Reasoning.StrictPartialOrder as <-Reasoning


private
  variable
    v p q : Level
    V : Value v
    l u : Key⁺
    n : ℕ
    P : Pred (K& V) p

------------------------------------------------------------------------
-- Any.lookup

lookup-result : {t : Tree V l u n} (p : Any P t) → P (Any.lookup p)
lookup-result (here p)  = p
lookup-result (left p)  = lookup-result p
lookup-result (right p) = lookup-result p

lookup-bounded : {t : Tree V l u n} (p : Any P t) → l < Any.lookup p .key < u
lookup-bounded {t = node kv lk ku bal} (here p)  = ordered lk , ordered ku
lookup-bounded {t = node kv lk ku bal} (left p)  =
  Prod.map₂ (flip (trans⁺ _) (ordered ku)) (lookup-bounded p)
lookup-bounded {t = node kv lk ku bal} (right p) =
  Prod.map₁ (trans⁺ _ (ordered lk)) (lookup-bounded p)

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
    ... | tri< k<k′ _ _ = let seg′ = l<k , [ k<k′ ]ᴿ; lk′ = insertWith k f lk seg′
                              ih = Any-insertWith-nothing lk seg′ pr (λ p → ¬p (left p))
                          in joinˡ⁺-left⁺ kv lk′ ku bal ih
    ... | tri> _ _ k>k′ = let seg′ = [ k>k′ ]ᴿ , k<u; ku′ = insertWith k f ku seg′
                              ih = Any-insertWith-nothing ku seg′ pr (λ p → ¬p (right p))
                          in joinʳ⁺-right⁺ kv lk ku′ bal ih

    Any-insertWith-just : (t : Tree V l u n) (seg : l < k < u) →
                          (pr : ∀ k′ v → (eq : k ≈ k′) → P (k′ , Val≈ eq (f (just (Val≈ (sym eq) v))))) →
                          Any ((k ≈_) ∘′ key) t → Any P (proj₂ (insertWith k f t seg))
    Any-insertWith-just (node kv@(k′ , v) lk ku bal) (l<k , k<u) pr p
      with p | compare k k′
    -- happy paths
    ... | here _   | tri≈ _ k≈k′ _ = here (pr k′ v k≈k′)
    ... | left lp  | tri< k<k′ _ _ = let seg′ = l<k , [ k<k′ ]ᴿ; lk′ = insertWith k f lk seg′ in
                                     joinˡ⁺-left⁺ kv lk′ ku bal (Any-insertWith-just lk seg′ pr lp)
    ... | right rp | tri> _ _ k>k′ = let seg′ = [ k>k′ ]ᴿ , k<u; ku′ = insertWith k f ku seg′ in
                                     joinʳ⁺-right⁺ kv lk ku′ bal (Any-insertWith-just ku seg′ pr rp)

    -- impossible cases
    ... | here eq  | tri< k<k′ _ _ = flip contradiction (irrefl⁺ [ k ]) $ begin-strict
      [ k  ] <⟨ [ k<k′ ]ᴿ ⟩
      [ k′ ] ≈⟨ [ sym eq ]ᴱ ⟩
      [ k  ] ∎
    ... | here eq  | tri> _ _ k>k′ = flip contradiction (irrefl⁺ [ k ]) $ begin-strict
      [ k  ] ≈⟨ [ eq ]ᴱ ⟩
      [ k′ ] <⟨ [ k>k′ ]ᴿ ⟩
      [ k  ] ∎
    ... | left lp  | tri≈ _ k≈k′ _ = flip contradiction (irrefl⁺ [ k ]) $ begin-strict
      let k″ = Any.lookup lp .key; k≈k″ = lookup-result lp; (_ , k″<k′) = lookup-bounded lp in
      [ k  ] ≈⟨ [ k≈k″ ]ᴱ ⟩
      [ k″ ] <⟨ k″<k′ ⟩
      [ k′ ] ≈⟨ [ sym k≈k′ ]ᴱ ⟩
      [ k  ] ∎
    ... | left lp  | tri> _ _ k>k′ = flip contradiction (irrefl⁺ [ k ]) $ begin-strict
      let k″ = Any.lookup lp .key; k≈k″ = lookup-result lp; (_ , k″<k′) = lookup-bounded lp in
      [ k  ] ≈⟨ [ k≈k″ ]ᴱ ⟩
      [ k″ ] <⟨ k″<k′ ⟩
      [ k′ ] <⟨ [ k>k′ ]ᴿ ⟩
      [ k  ] ∎
    ... | right rp | tri< k<k′ _ _ = flip contradiction (irrefl⁺ [ k ]) $ begin-strict
      let k″ = Any.lookup rp .key; k≈k″ = lookup-result rp; (k′<k″ , _) = lookup-bounded rp in
      [ k  ] <⟨ [ k<k′ ]ᴿ ⟩
      [ k′ ] <⟨ k′<k″ ⟩
      [ k″ ] ≈⟨ [ sym k≈k″ ]ᴱ ⟩
      [ k  ] ∎
    ... | right rp | tri≈ _ k≈k′ _ = flip contradiction (irrefl⁺ [ k ]) $ begin-strict
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
