-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Sublist.Heterogeneous.Properties where

open import Data.Empty
open import Data.List.Any using (Any; here; there)
open import Data.List.Base as List hiding (map; _∷ʳ_)
import Data.List.Properties as Lₚ
open import Data.List.Relation.Pointwise as Pw using (Pointwise; []; _∷_)
open import Data.List.Relation.Sublist.Heterogeneous

open import Data.Maybe.All as MAll using (nothing; just)
open import Data.Nat using (ℕ; _≤_; _≥_); open ℕ; open _≤_
import Data.Nat.Properties as ℕₚ
open import Function

open import Relation.Nullary using (yes; no; ¬_)
import Relation.Nullary.Decidable as Dec
open import Relation.Unary as U using (Pred; _⊆_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  length-mono-Sublist-≤ : ∀ {as bs} → Sublist R as bs → length as ≤ length bs
  length-mono-Sublist-≤ []        = z≤n
  length-mono-Sublist-≤ (y ∷ʳ rs) = ℕₚ.≤-step (length-mono-Sublist-≤ rs)
  length-mono-Sublist-≤ (r ∷ rs)  = s≤s (length-mono-Sublist-≤ rs)

------------------------------------------------------------------------
-- Conversion to and from Pointwise (proto-reflexivity)

  fromPointwise : Pointwise R ⇒ Sublist R
  fromPointwise []       = []
  fromPointwise (p ∷ ps) = p ∷ fromPointwise ps

  toPointwise : ∀ {as bs} → length as ≡ length bs →
                Sublist R as bs → Pointwise R as bs
  toPointwise {bs = []}     eq []         = []
  toPointwise {bs = b ∷ bs} eq (r ∷ rs)   = r ∷ toPointwise (ℕₚ.suc-injective eq) rs
  toPointwise {bs = b ∷ bs} eq (.b ∷ʳ rs) =
    ⊥-elim $ ℕₚ.<-irrefl eq (s≤s (length-mono-Sublist-≤ rs))

module _ {a b c r s t} {A : Set a} {B : Set b} {C : Set c}
         {R : REL A B r} {S : REL B C s} {T : REL A C t} where

  trans : Trans R S T → Trans (Sublist R) (Sublist S) (Sublist T)
  trans rs⇒t []        []        = []
  trans rs⇒t rs        (y ∷ʳ ss) = y ∷ʳ trans rs⇒t rs ss
  trans rs⇒t (y ∷ʳ rs) (s ∷ ss)  = _ ∷ʳ trans rs⇒t rs ss
  trans rs⇒t (r ∷ rs)  (s ∷ ss)  = rs⇒t r s ∷ trans rs⇒t rs ss

module _ {a b r s e} {A : Set a} {B : Set b}
         {R : REL A B r} {S : REL B A s} {E : REL A B e} where

  antisym : Antisym R S E → Antisym (Sublist R) (Sublist S) (Pointwise E)
  antisym rs⇒e []        []        = []
  antisym rs⇒e (r ∷ rs)  (s ∷ ss)  = rs⇒e r s ∷ antisym rs⇒e rs ss
  -- impossible cases
  antisym rs⇒e (_∷ʳ_ {xs} {ys₁} y rs) (_∷ʳ_ {ys₂} {zs} z ss) =
    ⊥-elim $ ℕₚ.<-irrefl P.refl $ begin
    length (y ∷ ys₁) ≤⟨ length-mono-Sublist-≤ ss ⟩
    length zs        ≤⟨ ℕₚ.n≤1+n (length zs) ⟩
    length (z ∷ zs)  ≤⟨ length-mono-Sublist-≤ rs ⟩
    length ys₁       ∎ where open ℕₚ.≤-Reasoning
  antisym rs⇒e (_∷ʳ_ {xs} {ys₁} y rs) (_∷_ {y} {ys₂} {z} {zs} s ss)  =
    ⊥-elim $ ℕₚ.<-irrefl P.refl $ begin
    length (z ∷ zs) ≤⟨ length-mono-Sublist-≤ rs ⟩
    length ys₁      ≤⟨ length-mono-Sublist-≤ ss ⟩
    length zs       ∎ where open ℕₚ.≤-Reasoning
  antisym rs⇒e (_∷_ {x} {xs} {y} {ys₁} r rs)  (_∷ʳ_ {ys₂} {zs} z ss) =
    ⊥-elim $ ℕₚ.<-irrefl P.refl $ begin
    length (y ∷ ys₁) ≤⟨ length-mono-Sublist-≤ ss ⟩
    length xs        ≤⟨ length-mono-Sublist-≤ rs ⟩
    length ys₁       ∎ where open ℕₚ.≤-Reasoning

------------------------------------------------------------------------
-- Various functions' outputs are sublists

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  tail-Sublist : ∀ {as bs} → Pointwise R as bs →
                 MAll.All (λ as → Sublist R as bs) (tail as)
  tail-Sublist []       = nothing
  tail-Sublist (p ∷ ps) = just (_ ∷ʳ fromPointwise ps)

  take-Sublist : ∀ n → Sublist R ⇒ (Sublist R ∘′ take n)
  take-Sublist n       (y ∷ʳ rs) = y ∷ʳ take-Sublist n rs
  take-Sublist zero    rs        = minimum _
  take-Sublist (suc n) []        = []
  take-Sublist (suc n) (r ∷ rs)  = r ∷ take-Sublist n rs

  drop-Sublist : ∀ n → Sublist R ⇒ (Sublist R ∘′ drop n)
  drop-Sublist n       (y ∷ʳ rs) = y ∷ʳ drop-Sublist n rs
  drop-Sublist zero    rs        = rs
  drop-Sublist (suc n) []        = []
  drop-Sublist (suc n) (r ∷ rs)  = _ ∷ʳ drop-Sublist n rs

module _ {a b r p} {A : Set a} {B : Set b}
         {R : REL A B r} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-Sublist : Sublist R ⇒ (Sublist R ∘′ takeWhile P?)
  takeWhile-Sublist []        = []
  takeWhile-Sublist (y ∷ʳ rs) = y ∷ʳ takeWhile-Sublist rs
  takeWhile-Sublist {a ∷ as} (r ∷ rs) with P? a
  ... | yes pa = r ∷ takeWhile-Sublist rs
  ... | no ¬pa = minimum _

  dropWhile-Sublist : Sublist R ⇒ (Sublist R ∘′ dropWhile P?)
  dropWhile-Sublist []        = []
  dropWhile-Sublist (y ∷ʳ rs) = y ∷ʳ dropWhile-Sublist rs
  dropWhile-Sublist {a ∷ as} (r ∷ rs) with P? a
  ... | yes pa = _ ∷ʳ dropWhile-Sublist rs
  ... | no ¬pa = r ∷ rs

  filter-Sublist : Sublist R ⇒ (Sublist R ∘′ filter P?)
  filter-Sublist []        = []
  filter-Sublist (y ∷ʳ rs) = y ∷ʳ filter-Sublist rs
  filter-Sublist {a ∷ as} (r ∷ rs) with P? a
  ... | yes pa = r ∷ filter-Sublist rs
  ... | no ¬pa = _ ∷ʳ filter-Sublist rs

------------------------------------------------------------------------
-- Various functions are increasing wrt _⊆_

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

------------------------------------------------------------------------
-- _∷_

  ∷ˡ⁻ : ∀ {a as bs} → Sublist R (a ∷ as) bs → Sublist R as bs
  ∷ˡ⁻ (y ∷ʳ rs) = y ∷ʳ ∷ˡ⁻ rs
  ∷ˡ⁻ (r ∷ rs)  = _ ∷ʳ rs

  _∷ʳ⁻_ : ∀ {a as b bs} → ¬ R a b → Sublist R (a ∷ as) (b ∷ bs) →
          Sublist R (a ∷ as) bs
  ¬r ∷ʳ⁻ (y ∷ʳ rs) = rs
  ¬r ∷ʳ⁻ (r ∷ rs)  = ⊥-elim (¬r r)

  ∷⁻ : ∀ {a as b bs} → Sublist R (a ∷ as) (b ∷ bs) → Sublist R as bs
  ∷⁻ (y ∷ʳ rs) = ∷ˡ⁻ rs
  ∷⁻ (x ∷ rs)  = rs

module _ {a b c d r} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {R : REL C D r} where

------------------------------------------------------------------------
-- map

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Sublist (λ a b → R (f a) (g b)) as bs →
         Sublist R (List.map f as) (List.map g bs)
  map⁺ f g []        = []
  map⁺ f g (y ∷ʳ rs) = g y ∷ʳ map⁺ f g rs
  map⁺ f g (r ∷ rs)  = r ∷ map⁺ f g rs

  map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
         Sublist R (List.map f as) (List.map g bs) →
         Sublist (λ a b → R (f a) (g b)) as bs
  map⁻ {[]}     {bs}     f g rs        = minimum _
  map⁻ {a ∷ as} {[]}     f g ()
  map⁻ {a ∷ as} {b ∷ bs} f g (_ ∷ʳ rs) = b ∷ʳ map⁻ f g rs
  map⁻ {a ∷ as} {b ∷ bs} f g (r ∷ rs)  = r ∷ map⁻ f g rs


module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

------------------------------------------------------------------------
-- _++_

  ++⁺ : ∀ {as bs cs ds} → Sublist R as bs → Sublist R cs ds →
        Sublist R (as ++ cs) (bs ++ ds)
  ++⁺ []         cds = cds
  ++⁺ (y ∷ʳ abs) cds = y ∷ʳ ++⁺ abs cds
  ++⁺ (ab ∷ abs) cds = ab ∷ ++⁺ abs cds

  ++⁻ : ∀ {as bs cs ds} → Pointwise R as bs → Sublist R (as ++ cs) (bs ++ ds) →
        Sublist R cs ds
  ++⁻ []       rs = rs
  ++⁻ (p ∷ ps) rs = ++⁻ ps (∷⁻ rs)

  ++ˡ : ∀ {as bs} (cs : List B) → Sublist R as bs → Sublist R as (cs ++ bs)
  ++ˡ zs = ++⁺ (minimum zs)

  ++ʳ : ∀ {as bs} (cs : List B) → Sublist R as bs → Sublist R as (bs ++ cs)
  ++ʳ cs []        = minimum cs
  ++ʳ cs (y ∷ʳ rs) = y ∷ʳ ++ʳ cs rs
  ++ʳ cs (r ∷ rs)  = r ∷ ++ʳ cs rs

------------------------------------------------------------------------
-- take / drop

  ≤-take-Sublist : ∀ {m n as bs} → m ≤ n → Pointwise R as bs →
                   Sublist R (take m as) (take n bs)
  ≤-take-Sublist z≤n       ps        = minimum _
  ≤-take-Sublist (s≤s m≤n) []        = []
  ≤-take-Sublist (s≤s m≤n) (p ∷ ps)  = p ∷ ≤-take-Sublist m≤n ps

  ≥-drop-Sublist : ∀ {m n as bs} → m ≥ n → Pointwise R as bs →
                   Sublist R (drop m as) (drop n bs)
  ≥-drop-Sublist {zero}  z≤n       ps       = fromPointwise ps
  ≥-drop-Sublist {suc m} m≥n       []       = minimum _
  ≥-drop-Sublist {suc m} z≤n       (p ∷ ps) = _ ∷ʳ ≥-drop-Sublist {m} z≤n ps
  ≥-drop-Sublist {suc m} (s≤s m≥n) (p ∷ ps) = ≥-drop-Sublist m≥n ps

  ≥-drop⁺ : ∀ {m n as bs} → m ≥ n → Sublist R as bs → Sublist R (drop m as) (drop n bs)
  ≥-drop⁺ {m} z≤n       rs        = drop-Sublist m rs
  ≥-drop⁺     (s≤s m≥n) []        = []
  ≥-drop⁺     (s≤s m≥n) (y ∷ʳ rs) = ≥-drop⁺ (ℕₚ.≤-step m≥n) rs
  ≥-drop⁺     (s≤s m≥n) (r ∷ rs)  = ≥-drop⁺ m≥n rs

  drop⁺ : ∀ {as bs} m → Sublist R as bs → Sublist R (drop m as) (drop m bs)
  drop⁺ m = ≥-drop⁺ (ℕₚ.≤-refl {m})


module _ {a b r p q} {A : Set a} {B : Set b}
         {R : REL A B r} {P : Pred A p} {Q : Pred B q}
         (P? : U.Decidable P) (Q? : U.Decidable Q) where

  ⊆-takeWhile-Sublist : ∀ {as bs} →
    (∀ {a b} → R a b → P a → Q b) →
    Pointwise R as bs → Sublist R (takeWhile P? as) (takeWhile Q? bs)
  ⊆-takeWhile-Sublist rp⇒q [] = []
  ⊆-takeWhile-Sublist {a ∷ as} {b ∷ bs} rp⇒q (p ∷ ps) with P? a | Q? b
  ... | yes pa | yes qb = p ∷ ⊆-takeWhile-Sublist rp⇒q ps
  ... | yes pa | no ¬qb = ⊥-elim $ ¬qb $ rp⇒q p pa
  ... | no ¬pa | yes qb = minimum _
  ... | no ¬pa | no ¬qb = []

  ⊇-dropWhile-Sublist : ∀ {as bs} →
    (∀ {a b} → R a b → Q b → P a) →
    Pointwise R as bs → Sublist R (dropWhile P? as) (dropWhile Q? bs)
  ⊇-dropWhile-Sublist rq⇒p [] = []
  ⊇-dropWhile-Sublist {a ∷ as} {b ∷ bs} rq⇒p (p ∷ ps) with P? a | Q? b
  ... | yes pa | yes qb = ⊇-dropWhile-Sublist rq⇒p ps
  ... | yes pa | no ¬qb = b ∷ʳ dropWhile-Sublist P? (fromPointwise ps)
  ... | no ¬pa | yes qb = ⊥-elim $ ¬pa $ rq⇒p p qb
  ... | no ¬pa | no ¬qb = p ∷ fromPointwise ps

  ⊆-filter-Sublist : ∀ {as bs} →
    (∀ {a b} → R a b → P a → Q b) →
    Sublist R as bs → Sublist R (filter P? as) (filter Q? bs)
  ⊆-filter-Sublist rp⇒q [] = []
  ⊆-filter-Sublist rp⇒q (y ∷ʳ rs) with Q? y
  ... | yes qb = y ∷ʳ ⊆-filter-Sublist rp⇒q rs
  ... | no ¬qb = ⊆-filter-Sublist rp⇒q rs
  ⊆-filter-Sublist {a ∷ as} {b ∷ bs} rp⇒q (r ∷ rs) with P? a | Q? b
  ... | yes pa | yes qb = r ∷ ⊆-filter-Sublist rp⇒q rs
  ... | yes pa | no ¬qb = ⊥-elim $ ¬qb $ rp⇒q r pa
  ... | no ¬pa | yes qb = _ ∷ʳ ⊆-filter-Sublist rp⇒q rs
  ... | no ¬pa | no ¬qb = ⊆-filter-Sublist rp⇒q rs

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

-- reverseAcc

  reverseAcc⁺ : ∀ {as bs cs ds} → Sublist R as bs → Sublist R cs ds →
                Sublist R (reverseAcc cs as) (reverseAcc ds bs)
  reverseAcc⁺ []         cds = cds
  reverseAcc⁺ (y ∷ʳ abs) cds = reverseAcc⁺ abs (y ∷ʳ cds)
  reverseAcc⁺ (r ∷ abs)  cds = reverseAcc⁺ abs (r ∷ cds)

  reverse⁺ : ∀ {as bs} → Sublist R as bs → Sublist R (reverse as) (reverse bs)
  reverse⁺ rs = reverseAcc⁺ rs []

  reverse⁻ : ∀ {as bs} → Sublist R (reverse as) (reverse bs) → Sublist R as bs
  reverse⁻ {as} {bs} p = cast (reverse⁺ p) where
    cast = P.subst₂ (Sublist R) (Lₚ.reverse-involutive as) (Lₚ.reverse-involutive bs)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} (R? : Decidable R) where

------------------------------------------------------------------------
-- Decidability result

  sublist? : Decidable (Sublist R)
  sublist? []       ys       = yes (minimum ys)
  sublist? (x ∷ xs) []       = no λ ()
  sublist? (x ∷ xs) (y ∷ ys) with R? x y
  ... | yes r = Dec.map′ (r ∷_) ∷⁻ (sublist? xs ys)
  ... | no ¬r = Dec.map′ (y ∷ʳ_) (¬r ∷ʳ⁻_) (sublist? (x ∷ xs) ys)
