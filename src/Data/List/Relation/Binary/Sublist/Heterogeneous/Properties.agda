-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Heterogeneous.Properties where

open import Data.Empty
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Base as List hiding (map; _∷ʳ_)
import Data.List.Properties as Lₚ
open import Data.List.Relation.Unary.Any.Properties
  using (here-injective; there-injective)
open import Data.List.Relation.Binary.Pointwise as Pw using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Sublist.Heterogeneous

open import Data.Maybe.Relation.Unary.All as MAll using (nothing; just)
open import Data.Nat using (ℕ; _≤_; _≥_); open ℕ; open _≤_
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; uncurry)

open import Function.Core
open import Function.Bijection   using (_⤖_; bijection)
open import Function.Equivalence using (_⇔_ ; equivalence)

open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Decidable as Dec
open import Relation.Unary as U using (Pred; _⊆_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Injectivity of constructors

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  ∷-injectiveˡ : ∀ {x y xs ys} {px qx : R x y} {pxs qxs : Sublist R xs ys} →
                 (Sublist R (x ∷ xs) (y ∷ ys) ∋ px ∷ pxs) ≡ (qx ∷ qxs) → px ≡ qx
  ∷-injectiveˡ P.refl = P.refl

  ∷-injectiveʳ : ∀ {x y xs ys} {px qx : R x y} {pxs qxs : Sublist R xs ys} →
                 (Sublist R (x ∷ xs) (y ∷ ys) ∋ px ∷ pxs) ≡ (qx ∷ qxs) → pxs ≡ qxs
  ∷-injectiveʳ P.refl = P.refl

  ∷ʳ-injective : ∀ {y xs ys} {pxs qxs : Sublist R xs ys} →
                 (Sublist R xs (y ∷ ys) ∋ y ∷ʳ pxs) ≡ (y ∷ʳ qxs) → pxs ≡ qxs
  ∷ʳ-injective P.refl = P.refl

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  length-mono-≤ : ∀ {as bs} → Sublist R as bs → length as ≤ length bs
  length-mono-≤ []        = z≤n
  length-mono-≤ (y ∷ʳ rs) = ℕₚ.≤-step (length-mono-≤ rs)
  length-mono-≤ (r ∷ rs)  = s≤s (length-mono-≤ rs)

------------------------------------------------------------------------
-- Conversion to and from Pointwise (proto-reflexivity)

  fromPointwise : Pointwise R ⇒ Sublist R
  fromPointwise []       = []
  fromPointwise (p ∷ ps) = p ∷ fromPointwise ps

  toPointwise : ∀ {as bs} → length as ≡ length bs →
                Sublist R as bs → Pointwise R as bs
  toPointwise {bs = []}     eq []         = []
  toPointwise {bs = b ∷ bs} eq (r ∷ rs)   = r ∷ toPointwise (ℕₚ.suc-injective eq) rs
  toPointwise {bs = b ∷ bs} eq (b ∷ʳ rs) =
    ⊥-elim $ ℕₚ.<-irrefl eq (s≤s (length-mono-≤ rs))

------------------------------------------------------------------------
-- Various functions' outputs are sublists

-- These lemmas are generalisations of results of the form `f xs ⊆ xs`.
-- (where _⊆_ stands for Sublist R). If R is reflexive then we can indeed
-- obtain `f xs ⊆ xs` from `xs ⊆ ys → f xs ⊆ ys`. The other direction is
-- only true if R is both reflexive and transitive.

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  tail-Sublist : ∀ {as bs} → Sublist R as bs →
                 MAll.All (λ as → Sublist R as bs) (tail as)
  tail-Sublist []        = nothing
  tail-Sublist (b ∷ʳ ps) = MAll.map (b ∷ʳ_) (tail-Sublist ps)
  tail-Sublist (p ∷ ps)  = just (_ ∷ʳ ps)

  take-Sublist : ∀ {as bs} n → Sublist R as bs → Sublist R (take n as) bs
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

  takeWhile-Sublist : ∀ {as bs} → Sublist R as bs → Sublist R (takeWhile P? as) bs
  takeWhile-Sublist []        = []
  takeWhile-Sublist (y ∷ʳ rs) = y ∷ʳ takeWhile-Sublist rs
  takeWhile-Sublist {a ∷ as} (r ∷ rs) with P? a
  ... | yes pa = r ∷ takeWhile-Sublist rs
  ... | no ¬pa = minimum _

  dropWhile-Sublist : ∀ {as bs} → Sublist R as bs → Sublist R (dropWhile P? as) bs
  dropWhile-Sublist []        = []
  dropWhile-Sublist (y ∷ʳ rs) = y ∷ʳ dropWhile-Sublist rs
  dropWhile-Sublist {a ∷ as} (r ∷ rs) with P? a
  ... | yes pa = _ ∷ʳ dropWhile-Sublist rs
  ... | no ¬pa = r ∷ rs

  filter-Sublist : ∀ {as bs} → Sublist R as bs → Sublist R (filter P? as) bs
  filter-Sublist []        = []
  filter-Sublist (y ∷ʳ rs) = y ∷ʳ filter-Sublist rs
  filter-Sublist {a ∷ as} (r ∷ rs) with P? a
  ... | yes pa = r ∷ filter-Sublist rs
  ... | no ¬pa = _ ∷ʳ filter-Sublist rs

------------------------------------------------------------------------
-- Various functions are increasing wrt _⊆_

-- We write f⁺ for the proof that `xs ⊆ ys → f xs ⊆ f ys`
-- and f⁻ for the one that `f xs ⊆ f ys → xs ⊆ ys`.

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

------------------------------------------------------------------------
-- _∷_

  ∷ˡ⁻ : ∀ {a as bs} → Sublist R (a ∷ as) bs → Sublist R as bs
  ∷ˡ⁻ (y ∷ʳ rs) = y ∷ʳ ∷ˡ⁻ rs
  ∷ˡ⁻ (r ∷  rs) = _ ∷ʳ rs

  ∷ʳ⁻ : ∀ {a as b bs} → ¬ R a b → Sublist R (a ∷ as) (b ∷ bs) →
        Sublist R (a ∷ as) bs
  ∷ʳ⁻ ¬r (y ∷ʳ rs) = rs
  ∷ʳ⁻ ¬r (r ∷  rs) = ⊥-elim (¬r r)

  ∷⁻ : ∀ {a as b bs} → Sublist R (a ∷ as) (b ∷ bs) → Sublist R as bs
  ∷⁻ (y ∷ʳ rs) = ∷ˡ⁻ rs
  ∷⁻ (x ∷  rs) = rs

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

  ++⁻ : ∀ {as bs cs ds} → length as ≡ length bs →
        Sublist R (as ++ cs) (bs ++ ds) → Sublist R cs ds
  ++⁻ {[]}     {[]}     eq rs = rs
  ++⁻ {a ∷ as} {b ∷ bs} eq rs = ++⁻ (ℕₚ.suc-injective eq) (∷⁻ rs)

  ++ˡ : ∀ {as bs} (cs : List B) → Sublist R as bs → Sublist R as (cs ++ bs)
  ++ˡ zs = ++⁺ (minimum zs)

  ++ʳ : ∀ {as bs} (cs : List B) → Sublist R as bs → Sublist R as (bs ++ cs)
  ++ʳ cs []        = minimum cs
  ++ʳ cs (y ∷ʳ rs) = y ∷ʳ ++ʳ cs rs
  ++ʳ cs (r ∷ rs)  = r ∷ ++ʳ cs rs


------------------------------------------------------------------------
-- concat

  concat⁺ : ∀ {ass bss} → Sublist (Sublist R) ass bss →
            Sublist R (concat ass) (concat bss)
  concat⁺ []          = []
  concat⁺ (y  ∷ʳ rss) = ++ˡ y (concat⁺ rss)
  concat⁺ (rs ∷  rss) = ++⁺ rs (concat⁺ rss)

------------------------------------------------------------------------
-- take / drop

  take⁺ : ∀ {m n as bs} → m ≤ n → Pointwise R as bs →
          Sublist R (take m as) (take n bs)
  take⁺ z≤n       ps        = minimum _
  take⁺ (s≤s m≤n) []        = []
  take⁺ (s≤s m≤n) (p ∷  ps) = p ∷ take⁺ m≤n ps

  drop⁺ : ∀ {m n as bs} → m ≥ n → Sublist R as bs →
          Sublist R (drop m as) (drop n bs)
  drop⁺ {m} z≤n       rs        = drop-Sublist m rs
  drop⁺     (s≤s m≥n) []        = []
  drop⁺     (s≤s m≥n) (y ∷ʳ rs) = drop⁺ (ℕₚ.≤-step m≥n) rs
  drop⁺     (s≤s m≥n) (r ∷ rs)  = drop⁺ m≥n rs

  drop⁺-≥ : ∀ {m n as bs} → m ≥ n → Pointwise R as bs →
            Sublist R (drop m as) (drop n bs)
  drop⁺-≥ m≥n pw = drop⁺ m≥n (fromPointwise pw)

  drop⁺-⊆ : ∀ {as bs} m → Sublist R as bs →
            Sublist R (drop m as) (drop m bs)
  drop⁺-⊆ m = drop⁺ (ℕₚ.≤-refl {m})

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

  ⊆-filter-Sublist : ∀ {as bs} → (∀ {a b} → R a b → P a → Q b) →
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

module _ {a r p} {A : Set a} {R : Rel A r} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-filter : ∀ {as} → Pointwise R as as →
                     Sublist R (takeWhile P? as) (filter P? as)
  takeWhile-filter [] = []
  takeWhile-filter {a ∷ as} (p ∷ ps) with P? a
  ... | yes pa = p ∷ takeWhile-filter ps
  ... | no ¬pa = minimum _

  filter-dropWhile : ∀ {as} → Pointwise R as as →
                     Sublist R (filter P? as) (dropWhile (¬? ∘ P?) as)
  filter-dropWhile [] = []
  filter-dropWhile {a ∷ as} (p ∷ ps) with P? a
  ... | yes pa = p ∷ filter-Sublist P? (fromPointwise ps)
  ... | no ¬pa = filter-dropWhile ps

------------------------------------------------------------------------
-- reverse

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

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

------------------------------------------------------------------------
-- Inversion lemmas

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} {a as b bs} where

  ∷⁻¹ : R a b → Sublist R as bs ⇔ Sublist R (a ∷ as) (b ∷ bs)
  ∷⁻¹ r = equivalence (r ∷_) ∷⁻

  ∷ʳ⁻¹ : ¬ R a b → Sublist R (a ∷ as) bs ⇔ Sublist R (a ∷ as) (b ∷ bs)
  ∷ʳ⁻¹ ¬r = equivalence (_ ∷ʳ_) (∷ʳ⁻ ¬r)

------------------------------------------------------------------------
-- Irrelevant special case

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  Sublist-[]-irrelevant : U.Irrelevant (Sublist R [])
  Sublist-[]-irrelevant []       []        = P.refl
  Sublist-[]-irrelevant (y ∷ʳ p) (.y ∷ʳ q) = P.cong (y ∷ʳ_) (Sublist-[]-irrelevant p q)

------------------------------------------------------------------------
-- (to/from)Any is a bijection

  toAny-injective : ∀ {xs x} {p q : Sublist R [ x ] xs} → toAny p ≡ toAny q → p ≡ q
  toAny-injective {p = y ∷ʳ p} {y ∷ʳ q} =
    P.cong (y ∷ʳ_) ∘′ toAny-injective ∘′ there-injective
  toAny-injective {p = _ ∷ p}  {_ ∷ q}  =
    P.cong₂ (flip _∷_) (Sublist-[]-irrelevant p q) ∘′ here-injective

  fromAny-injective : ∀ {xs x} {p q : Any (R x) xs} →
                      fromAny {R = R} p ≡ fromAny q → p ≡ q
  fromAny-injective {p = here px} {here qx} = P.cong here ∘′ ∷-injectiveˡ
  fromAny-injective {p = there p} {there q} =
    P.cong there ∘′ fromAny-injective ∘′ ∷ʳ-injective

  toAny∘fromAny≗id : ∀ {xs x} (p : Any (R x) xs) → toAny (fromAny {R = R} p) ≡ p
  toAny∘fromAny≗id (here px) = P.refl
  toAny∘fromAny≗id (there p) = P.cong there (toAny∘fromAny≗id p)

  Sublist-[x]-bijection : ∀ {x xs} → (Sublist R [ x ] xs) ⤖ (Any (R x) xs)
  Sublist-[x]-bijection = bijection toAny fromAny toAny-injective toAny∘fromAny≗id

------------------------------------------------------------------------
-- Relational properties

module Reflexivity
    {a r} {A : Set a} {R : Rel A r}
    (R-refl : Reflexive R) where

  reflexive : _≡_ ⇒ Sublist R
  reflexive P.refl = fromPointwise (Pw.refl R-refl)

  refl : Reflexive (Sublist R)
  refl = reflexive P.refl

open Reflexivity public

module Transitivity
    {a b c r s t} {A : Set a} {B : Set b} {C : Set c}
    {R : REL A B r} {S : REL B C s} {T : REL A C t}
    (rs⇒t : Trans R S T) where

  trans : Trans (Sublist R) (Sublist S) (Sublist T)
  trans rs        (y ∷ʳ ss) = y ∷ʳ trans rs ss
  trans (y ∷ʳ rs) (s ∷ ss)  = _ ∷ʳ trans rs ss
  trans (r ∷ rs)  (s ∷ ss)  = rs⇒t r s ∷ trans rs ss
  trans []        []        = []

open Transitivity public

module Antisymmetry
    {a b r s e} {A : Set a} {B : Set b}
    {R : REL A B r} {S : REL B A s} {E : REL A B e}
    (rs⇒e : Antisym R S E) where

  open ℕₚ.≤-Reasoning

  antisym : Antisym (Sublist R) (Sublist S) (Pointwise E)
  antisym []        []        = []
  antisym (r ∷ rs)  (s ∷ ss)  = rs⇒e r s ∷ antisym rs ss
  -- impossible cases
  antisym (_∷ʳ_ {xs} {ys₁} y rs) (_∷ʳ_ {ys₂} {zs} z ss) =
    ⊥-elim $ ℕₚ.<-irrefl P.refl $ begin
    length (y ∷ ys₁) ≤⟨ length-mono-≤ ss ⟩
    length zs        ≤⟨ ℕₚ.n≤1+n (length zs) ⟩
    length (z ∷ zs)  ≤⟨ length-mono-≤ rs ⟩
    length ys₁       ∎
  antisym (_∷ʳ_ {xs} {ys₁} y rs) (_∷_ {y} {ys₂} {z} {zs} s ss)  =
    ⊥-elim $ ℕₚ.<-irrefl P.refl $ begin
    length (z ∷ zs) ≤⟨ length-mono-≤ rs ⟩
    length ys₁      ≤⟨ length-mono-≤ ss ⟩
    length zs       ∎
  antisym (_∷_ {x} {xs} {y} {ys₁} r rs)  (_∷ʳ_ {ys₂} {zs} z ss) =
    ⊥-elim $ ℕₚ.<-irrefl P.refl $ begin
    length (y ∷ ys₁) ≤⟨ length-mono-≤ ss ⟩
    length xs        ≤⟨ length-mono-≤ rs ⟩
    length ys₁       ∎

open Antisymmetry public

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} (R? : Decidable R) where

  sublist? : Decidable (Sublist R)
  sublist? []       ys       = yes (minimum ys)
  sublist? (x ∷ xs) []       = no λ ()
  sublist? (x ∷ xs) (y ∷ ys) with R? x y
  ... | yes r = Dec.map (∷⁻¹   r) (sublist? xs ys)
  ... | no ¬r = Dec.map (∷ʳ⁻¹ ¬r) (sublist? (x ∷ xs) ys)

module _ {a e r} {A : Set a} {E : Rel A e} {R : Rel A r} where

  isPreorder : IsPreorder E R → IsPreorder (Pointwise E) (Sublist R)
  isPreorder ER-isPreorder = record
    { isEquivalence = Pw.isEquivalence       ER.isEquivalence
    ; reflexive     = fromPointwise ∘ Pw.map ER.reflexive
    ; trans         = trans                  ER.trans
    } where module ER = IsPreorder ER-isPreorder

  isPartialOrder : IsPartialOrder E R → IsPartialOrder (Pointwise E) (Sublist R)
  isPartialOrder ER-isPartialOrder = record
    { isPreorder = isPreorder ER.isPreorder
    ; antisym    = antisym    ER.antisym
    } where module ER = IsPartialOrder ER-isPartialOrder

  isDecPartialOrder : IsDecPartialOrder E R →
                      IsDecPartialOrder (Pointwise E) (Sublist R)
  isDecPartialOrder ER-isDecPartialOrder = record
    { isPartialOrder = isPartialOrder ER.isPartialOrder
    ; _≟_            = Pw.decidable   ER._≟_
    ; _≤?_           = sublist?       ER._≤?_
    } where module ER = IsDecPartialOrder ER-isDecPartialOrder

module _ {a e r} where

  preorder : Preorder a e r → Preorder _ _ _
  preorder ER-preorder = record
    { isPreorder = isPreorder ER.isPreorder
    } where module ER = Preorder ER-preorder

  poset : Poset a e r → Poset _ _ _
  poset ER-poset = record
    { isPartialOrder = isPartialOrder ER.isPartialOrder
    } where module ER = Poset ER-poset

  decPoset : DecPoset a e r → DecPoset _ _ _
  decPoset ER-poset = record
    { isDecPartialOrder = isDecPartialOrder ER.isDecPartialOrder
    } where module ER = DecPoset ER-poset
