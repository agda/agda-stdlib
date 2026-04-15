------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous sublist relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Sublist.Heterogeneous.Properties where

open import Level

open import Data.Bool.Base using (true; false)
open import Data.List.Relation.Unary.All using (Null; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Base as List hiding (map; _∷ʳ_)
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any.Properties
  using (here-injective; there-injective)
open import Data.List.Relation.Binary.Pointwise as Pw using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Sublist.Heterogeneous

open import Data.Maybe.Relation.Unary.All as Maybe using (nothing; just)
open import Data.Nat.Base using (ℕ; _≤_; _≥_); open ℕ; open _≤_
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (∃₂; _×_; _,_; <_,_>; proj₂; uncurry)

open import Function.Base
open import Function.Bundles using (_⤖_; _⇔_ ; mk⤖; mk⇔)
open import Function.Consequences.Propositional using (strictlySurjective⇒surjective)
open import Relation.Nullary.Decidable as Dec using (Dec; does; _because_; yes; no; ¬?)
open import Relation.Nullary.Negation using (¬_; contradiction; contradiction′)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Unary as U using (Pred)
open import Relation.Binary.Core using (Rel; REL; _⇒_)
open import Relation.Binary.Bundles using (Preorder; Poset; DecPoset)
open import Relation.Binary.Definitions
  using (Reflexive; Trans; Antisym; Decidable; Irrelevant; Irreflexive)
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
import Relation.Binary.Reasoning.Preorder as ≲-Reasoning
open import Relation.Binary.Reasoning.Syntax

private
  variable
    a b c d e p q r s t : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    x : A
    y : B
    as cs xs : List A
    bs ds ys : List B
    ass : List (List A)
    bss : List (List B)
    m n : ℕ

------------------------------------------------------------------------
-- Injectivity of constructors

module _ {R : REL A B r} where

  ∷-injectiveˡ : {px qx : R x y} {pxs qxs : Sublist R xs ys} →
                 (Sublist R (x ∷ xs) (y ∷ ys) ∋ px ∷ pxs) ≡ (qx ∷ qxs) → px ≡ qx
  ∷-injectiveˡ ≡.refl = ≡.refl

  ∷-injectiveʳ : {px qx : R x y} {pxs qxs : Sublist R xs ys} →
                 (Sublist R (x ∷ xs) (y ∷ ys) ∋ px ∷ pxs) ≡ (qx ∷ qxs) → pxs ≡ qxs
  ∷-injectiveʳ ≡.refl = ≡.refl

  ∷ʳ-injective : {pxs qxs : Sublist R xs ys} →
                 (Sublist R xs (y ∷ ys) ∋ y ∷ʳ pxs) ≡ (y ∷ʳ qxs) → pxs ≡ qxs
  ∷ʳ-injective ≡.refl = ≡.refl

module _ {R : REL A B r} where

  length-mono-≤ : Sublist R as bs → length as ≤ length bs
  length-mono-≤ []        = z≤n
  length-mono-≤ (y ∷ʳ rs) = ℕ.m≤n⇒m≤1+n (length-mono-≤ rs)
  length-mono-≤ (r ∷ rs)  = s≤s (length-mono-≤ rs)

------------------------------------------------------------------------
-- Conversion to and from Pointwise (proto-reflexivity)

  fromPointwise : Pointwise R ⇒ Sublist R
  fromPointwise []       = []
  fromPointwise (p ∷ ps) = p ∷ fromPointwise ps

  toPointwise : length as ≡ length bs →
                Sublist R as bs → Pointwise R as bs
  toPointwise {bs = []}     eq []         = []
  toPointwise {bs = b ∷ bs} eq (r ∷ rs)   = r ∷ toPointwise (ℕ.suc-injective eq) rs
  toPointwise {bs = b ∷ bs} eq (b ∷ʳ rs) =
    contradiction (s≤s (length-mono-≤ rs)) (ℕ.<-irrefl eq)

------------------------------------------------------------------------
-- Various functions' outputs are sublists

-- These lemmas are generalisations of results of the form `f xs ⊆ xs`.
-- (where _⊆_ stands for Sublist R). If R is reflexive then we can
-- indeed obtain `f xs ⊆ xs` from `xs ⊆ ys → f xs ⊆ ys`. The other
-- direction is only true if R is both reflexive and transitive.

module _ {R : REL A B r} where

  tail-Sublist : Sublist R as bs →
                 Maybe.All (λ as → Sublist R as bs) (tail as)
  tail-Sublist []        = nothing
  tail-Sublist (b ∷ʳ ps) = Maybe.map (b ∷ʳ_) (tail-Sublist ps)
  tail-Sublist (p ∷ ps)  = just (_ ∷ʳ ps)

  take-Sublist : ∀ n → Sublist R as bs → Sublist R (take n as) bs
  take-Sublist n       (y ∷ʳ rs) = y ∷ʳ take-Sublist n rs
  take-Sublist zero    rs        = minimum _
  take-Sublist (suc n) []        = []
  take-Sublist (suc n) (r ∷ rs)  = r ∷ take-Sublist n rs

  drop-Sublist : ∀ n → Sublist R ⇒ (Sublist R ∘′ drop n)
  drop-Sublist n       (y ∷ʳ rs) = y ∷ʳ drop-Sublist n rs
  drop-Sublist zero    rs        = rs
  drop-Sublist (suc n) []        = []
  drop-Sublist (suc n) (r ∷ rs)  = _ ∷ʳ drop-Sublist n rs

module _ {R : REL A B r} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-Sublist : Sublist R as bs → Sublist R (takeWhile P? as) bs
  takeWhile-Sublist []        = []
  takeWhile-Sublist (y ∷ʳ rs) = y ∷ʳ takeWhile-Sublist rs
  takeWhile-Sublist {a ∷ as} (r ∷ rs) with does (P? a)
  ... | true  = r ∷ takeWhile-Sublist rs
  ... | false = minimum _

  dropWhile-Sublist : Sublist R as bs → Sublist R (dropWhile P? as) bs
  dropWhile-Sublist []        = []
  dropWhile-Sublist (y ∷ʳ rs) = y ∷ʳ dropWhile-Sublist rs
  dropWhile-Sublist {a ∷ as} (r ∷ rs) with does (P? a)
  ... | true  = _ ∷ʳ dropWhile-Sublist rs
  ... | false = r ∷ rs

  filter-Sublist : Sublist R as bs → Sublist R (filter P? as) bs
  filter-Sublist []        = []
  filter-Sublist (y ∷ʳ rs) = y ∷ʳ filter-Sublist rs
  filter-Sublist {a ∷ as} (r ∷ rs) with does (P? a)
  ... | true  = r ∷ filter-Sublist rs
  ... | false = _ ∷ʳ filter-Sublist rs

------------------------------------------------------------------------
-- Various functions are increasing wrt _⊆_

-- We write f⁺ for the proof that `xs ⊆ ys → f xs ⊆ f ys`
-- and f⁻ for the one that `f xs ⊆ f ys → xs ⊆ ys`.

module _ {R : REL A B r} where

------------------------------------------------------------------------
-- _∷_

  ∷ˡ⁻ : Sublist R (x ∷ xs) ys → Sublist R xs ys
  ∷ˡ⁻ (y ∷ʳ rs) = y ∷ʳ ∷ˡ⁻ rs
  ∷ˡ⁻ (r ∷  rs) = _ ∷ʳ rs

  ∷ʳ⁻ : ¬ R x y → Sublist R (x ∷ xs) (y ∷ ys) →
        Sublist R (x ∷ xs) ys
  ∷ʳ⁻ ¬r (y ∷ʳ rs) = rs
  ∷ʳ⁻ ¬r (r ∷  rs) = contradiction r ¬r

  ∷⁻ : Sublist R (x ∷ xs) (y ∷ ys) → Sublist R xs ys
  ∷⁻ (y ∷ʳ rs) = ∷ˡ⁻ rs
  ∷⁻ (x ∷  rs) = rs

module _ {R : REL C D r} where

------------------------------------------------------------------------
-- map

  map⁺ : (f : A → C) (g : B → D) →
         Sublist (λ a b → R (f a) (g b)) as bs →
         Sublist R (List.map f as) (List.map g bs)
  map⁺ f g []        = []
  map⁺ f g (y ∷ʳ rs) = g y ∷ʳ map⁺ f g rs
  map⁺ f g (r ∷ rs)  = r ∷ map⁺ f g rs

  map⁻ : (f : A → C) (g : B → D) →
         Sublist R (List.map f as) (List.map g bs) →
         Sublist (λ a b → R (f a) (g b)) as bs
  map⁻ {as = []}     {bs}     f g rs        = minimum _
  map⁻ {as = a ∷ as} {b ∷ bs} f g (_ ∷ʳ rs) = b ∷ʳ map⁻ f g rs
  map⁻ {as = a ∷ as} {b ∷ bs} f g (r ∷ rs)  = r ∷ map⁻ f g rs


module _ {R : REL A B r} where

------------------------------------------------------------------------
-- _++_

  ++⁺ : Sublist R as bs → Sublist R cs ds →
        Sublist R (as ++ cs) (bs ++ ds)
  ++⁺ []         cds = cds
  ++⁺ (y ∷ʳ abs) cds = y ∷ʳ ++⁺ abs cds
  ++⁺ (ab ∷ abs) cds = ab ∷ ++⁺ abs cds

  ++⁻ : length as ≡ length bs →
        Sublist R (as ++ cs) (bs ++ ds) → Sublist R cs ds
  ++⁻ {as = []}     {[]}     eq rs = rs
  ++⁻ {as = a ∷ as} {b ∷ bs} eq rs = ++⁻ (ℕ.suc-injective eq) (∷⁻ rs)

  ++ˡ : (cs : List B) → Sublist R as bs → Sublist R as (cs ++ bs)
  ++ˡ zs = ++⁺ (minimum zs)

  ++ʳ : (cs : List B) → Sublist R as bs → Sublist R as (bs ++ cs)
  ++ʳ cs []        = minimum cs
  ++ʳ cs (y ∷ʳ rs) = y ∷ʳ ++ʳ cs rs
  ++ʳ cs (r ∷ rs)  = r ∷ ++ʳ cs rs


------------------------------------------------------------------------
-- concat

  concat⁺ : Sublist (Sublist R) ass bss →
            Sublist R (concat ass) (concat bss)
  concat⁺ []          = []
  concat⁺ (y  ∷ʳ rss) = ++ˡ y (concat⁺ rss)
  concat⁺ (rs ∷  rss) = ++⁺ rs (concat⁺ rss)

------------------------------------------------------------------------
-- take / drop

  take⁺ : m ≤ n → Pointwise R as bs →
          Sublist R (take m as) (take n bs)
  take⁺ z≤n       ps        = minimum _
  take⁺ (s≤s m≤n) []        = []
  take⁺ (s≤s m≤n) (p ∷  ps) = p ∷ take⁺ m≤n ps

  drop⁺ : m ≥ n → Sublist R as bs →
          Sublist R (drop m as) (drop n bs)
  drop⁺ (z≤n {m}) rs        = drop-Sublist m rs
  drop⁺ (s≤s m≥n) []        = []
  drop⁺ (s≤s m≥n) (y ∷ʳ rs) = drop⁺ (ℕ.m≤n⇒m≤1+n m≥n) rs
  drop⁺ (s≤s m≥n) (r ∷ rs)  = drop⁺ m≥n rs

  drop⁺-≥ : m ≥ n → Pointwise R as bs →
            Sublist R (drop m as) (drop n bs)
  drop⁺-≥ m≥n pw = drop⁺ m≥n (fromPointwise pw)

  drop⁺-⊆ : ∀ m → Sublist R as bs →
            Sublist R (drop m as) (drop m bs)
  drop⁺-⊆ m = drop⁺ (ℕ.≤-refl {m})

module _ {R : REL A B r} {P : Pred A p} {Q : Pred B q}
         (P? : U.Decidable P) (Q? : U.Decidable Q) where

  ⊆-takeWhile-Sublist : (∀ {a b} → R a b → P a → Q b) →
                        Pointwise R as bs →
                        Sublist R (takeWhile P? as) (takeWhile Q? bs)
  ⊆-takeWhile-Sublist rp⇒q [] = []
  ⊆-takeWhile-Sublist {a ∷ as} {b ∷ bs} rp⇒q (p ∷ ps) with P? a | Q? b
  ... | false because _ | _               = minimum _
  ... | true  because _ | true  because _ = p ∷ ⊆-takeWhile-Sublist rp⇒q ps
  ... | yes pa          | no ¬qb          = contradiction (rp⇒q p pa) ¬qb

  ⊇-dropWhile-Sublist : (∀ {a b} → R a b → Q b → P a) →
                        Pointwise R as bs →
                        Sublist R (dropWhile P? as) (dropWhile Q? bs)
  ⊇-dropWhile-Sublist rq⇒p [] = []
  ⊇-dropWhile-Sublist {a ∷ as} {b ∷ bs} rq⇒p (p ∷ ps) with P? a | Q? b
  ... | true  because _ | true  because _ = ⊇-dropWhile-Sublist rq⇒p ps
  ... | true  because _ | false because _ =
    b ∷ʳ dropWhile-Sublist P? (fromPointwise ps)
  ... | false because _ | false because _ = p ∷ fromPointwise ps
  ... | no ¬pa          | yes qb          = contradiction (rq⇒p p qb) ¬pa

  ⊆-filter-Sublist : (∀ {a b} → R a b → P a → Q b) →
                     Sublist R as bs → Sublist R (filter P? as) (filter Q? bs)
  ⊆-filter-Sublist rp⇒q [] = []
  ⊆-filter-Sublist rp⇒q (y ∷ʳ rs) with does (Q? y)
  ... | true  = y ∷ʳ ⊆-filter-Sublist rp⇒q rs
  ... | false = ⊆-filter-Sublist rp⇒q rs
  ⊆-filter-Sublist {a ∷ as} {b ∷ bs} rp⇒q (r ∷ rs) with P? a | Q? b
  ... | true  because _ | true  because _ = r ∷ ⊆-filter-Sublist rp⇒q rs
  ... | false because _ | true  because _ = _ ∷ʳ ⊆-filter-Sublist rp⇒q rs
  ... | false because _ | false because _ = ⊆-filter-Sublist rp⇒q rs
  ... | yes pa          | no ¬qb          = contradiction (rp⇒q r pa) ¬qb

module _ {R : Rel A r} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-filter : Pointwise R as as →
                     Sublist R (takeWhile P? as) (filter P? as)
  takeWhile-filter [] = []
  takeWhile-filter {a ∷ as} (p ∷ ps) with does (P? a)
  ... | true  = p ∷ takeWhile-filter ps
  ... | false = minimum _

  filter-dropWhile : Pointwise R as as →
                     Sublist R (filter P? as) (dropWhile (¬? ∘ P?) as)
  filter-dropWhile [] = []
  filter-dropWhile {a ∷ as} (p ∷ ps) with does (P? a)
  ... | true  = p ∷ filter-Sublist P? (fromPointwise ps)
  ... | false = filter-dropWhile ps

------------------------------------------------------------------------
-- reverse

module _ {R : REL A B r} where

  reverseAcc⁺ : Sublist R as bs → Sublist R cs ds →
                Sublist R (reverseAcc cs as) (reverseAcc ds bs)
  reverseAcc⁺ []         cds = cds
  reverseAcc⁺ (y ∷ʳ abs) cds = reverseAcc⁺ abs (y ∷ʳ cds)
  reverseAcc⁺ (r ∷ abs)  cds = reverseAcc⁺ abs (r ∷ cds)

  ʳ++⁺ : Sublist R as bs → Sublist R cs ds →
         Sublist R (as ʳ++ cs) (bs ʳ++ ds)
  ʳ++⁺ = reverseAcc⁺

  reverse⁺ : Sublist R as bs → Sublist R (reverse as) (reverse bs)
  reverse⁺ rs = reverseAcc⁺ rs []

  reverse⁻ : Sublist R (reverse as) (reverse bs) → Sublist R as bs
  reverse⁻ {as = as} {bs = bs} p = cast (reverse⁺ p) where
    cast = ≡.subst₂ (Sublist R) (List.reverse-involutive as) (List.reverse-involutive bs)

------------------------------------------------------------------------
-- Inversion lemmas

module _ {R : REL A B r} where

  ∷⁻¹ : R x y → Sublist R xs ys ⇔ Sublist R (x ∷ xs) (y ∷ ys)
  ∷⁻¹ r = mk⇔ (r ∷_) ∷⁻

  ∷ʳ⁻¹ : ¬ R x y → Sublist R (x ∷ xs) ys ⇔ Sublist R (x ∷ xs) (y ∷ ys)
  ∷ʳ⁻¹ ¬r = mk⇔ (_ ∷ʳ_) (∷ʳ⁻ ¬r)

------------------------------------------------------------------------
-- Empty special case

module _ {R : REL A B r} where

  Sublist-[]-universal : U.Universal (Sublist R [])
  Sublist-[]-universal []      = []
  Sublist-[]-universal (_ ∷ _) = _ ∷ʳ Sublist-[]-universal _

  Sublist-[]-irrelevant : U.Irrelevant (Sublist R [])
  Sublist-[]-irrelevant []       []        = ≡.refl
  Sublist-[]-irrelevant (y ∷ʳ p) (.y ∷ʳ q) = ≡.cong (y ∷ʳ_) (Sublist-[]-irrelevant p q)

------------------------------------------------------------------------
-- (to/from)Any is a bijection

  toAny-injective :{p q : Sublist R [ x ] xs} → toAny p ≡ toAny q → p ≡ q
  toAny-injective {p = y ∷ʳ p} {y ∷ʳ q} =
    ≡.cong (y ∷ʳ_) ∘′ toAny-injective ∘′ there-injective
  toAny-injective {p = _ ∷ p}  {_ ∷ q}  =
    ≡.cong₂ (flip _∷_) (Sublist-[]-irrelevant p q) ∘′ here-injective

  fromAny-injective : {p q : Any (R x) xs} →
                      fromAny {R = R} p ≡ fromAny q → p ≡ q
  fromAny-injective {p = here px} {here qx} = ≡.cong here ∘′ ∷-injectiveˡ
  fromAny-injective {p = there p} {there q} =
    ≡.cong there ∘′ fromAny-injective ∘′ ∷ʳ-injective

  toAny∘fromAny≗id : (p : Any (R x) xs) → toAny (fromAny {R = R} p) ≡ p
  toAny∘fromAny≗id (here px) = ≡.refl
  toAny∘fromAny≗id (there p) = ≡.cong there (toAny∘fromAny≗id p)

  Sublist-[x]-bijection : (Sublist R [ x ] xs) ⤖ (Any (R x) xs)
  Sublist-[x]-bijection = mk⤖ (toAny-injective , strictlySurjective⇒surjective < fromAny , toAny∘fromAny≗id >)

------------------------------------------------------------------------
-- Relational properties

module Reflexivity
    {R : Rel A r}
    (R-refl : Reflexive R) where

  reflexive : _≡_ ⇒ Sublist R
  reflexive ≡.refl = fromPointwise (Pw.refl R-refl)

  refl : Reflexive (Sublist R)
  refl = reflexive ≡.refl

open Reflexivity public

module Transitivity
    {R : REL A B r} {S : REL B C s} {T : REL A C t}
    (rs⇒t : Trans R S T) where

  trans : Trans (Sublist R) (Sublist S) (Sublist T)
  trans rs        (y ∷ʳ ss) = y ∷ʳ trans rs ss
  trans (y ∷ʳ rs) (s ∷ ss)  = _ ∷ʳ trans rs ss
  trans (r ∷ rs)  (s ∷ ss)  = rs⇒t r s ∷ trans rs ss
  trans []        []        = []

open Transitivity public

module Antisymmetry
    {R : REL A B r} {S : REL B A s} {E : REL A B e}
    (rs⇒e : Antisym R S E) where

  open ℕ.≤-Reasoning

  private
    antisym-lemma : Sublist R xs ys → ¬ Sublist S (y ∷ ys) xs
    antisym-lemma {xs} {ys} {y} rs ss = ℕ.<-irrefl ≡.refl $ begin
      length (y ∷ ys) ≤⟨ length-mono-≤ ss ⟩
      length xs       ≤⟨ length-mono-≤ rs ⟩
      length ys       ∎

  antisym : Antisym (Sublist R) (Sublist S) (Pointwise E)
  -- impossible cases
  antisym (_ ∷ʳ rs) ss = contradiction′ (antisym-lemma rs) ss
  antisym (_∷_ {x} {xs} {y} {ys₁} r rs)  (_∷ʳ_ {ys₂} {zs} z ss) =
    contradiction′ (antisym-lemma rs) ss
  -- diagonal cases
  antisym []        []        = []
  antisym (r ∷ rs)  (s ∷ ss)  = rs⇒e r s ∷ antisym rs ss

open Antisymmetry public

module _ {R : REL A B r} (R? : Decidable R) where

  sublist? : Decidable (Sublist R)
  sublist? []       ys       = yes (minimum ys)
  sublist? (x ∷ xs) []       = no λ ()
  sublist? (x ∷ xs) (y ∷ ys) with R? x y
  ... | true  because  [r] =
    Dec.map (∷⁻¹  (invert  [r])) (sublist? xs ys)
  ... | false because [¬r] =
    Dec.map (∷ʳ⁻¹ (invert [¬r])) (sublist? (x ∷ xs) ys)

module _ {E : Rel A e} {R : Rel A r} where

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
    ; _≟_            = Pw.decidable   ER._≈?_
    ; _≤?_           = sublist?       ER._≤?_
    } where module ER = IsDecPartialOrder ER-isDecPartialOrder

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

------------------------------------------------------------------------
-- Reasoning over sublists
------------------------------------------------------------------------

module ⊆-Reasoning (≲ : Preorder a e r) where

  open Preorder ≲ using (module Eq)

  open ≲-Reasoning (preorder ≲) public
    renaming (≲-go to ⊆-go; ≈-go to ≋-go)

  open ⊆-syntax _IsRelatedTo_ _IsRelatedTo_ ⊆-go public
  open ≋-syntax _IsRelatedTo_ _IsRelatedTo_ ≋-go (Pw.symmetric Eq.sym) public

------------------------------------------------------------------------
-- Properties of disjoint sublists

module Disjointness {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  private
    infix 4 _⊆_
    _⊆_ = Sublist R

  -- Forgetting the union

  DisjointUnion→Disjoint : ∀ {xs ys zs us} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} {τ : us ⊆ zs} →
    DisjointUnion τ₁ τ₂ τ → Disjoint τ₁ τ₂
  DisjointUnion→Disjoint []         = []
  DisjointUnion→Disjoint (y   ∷ₙ u) = y   ∷ₙ DisjointUnion→Disjoint u
  DisjointUnion→Disjoint (x≈y ∷ₗ u) = x≈y ∷ₗ DisjointUnion→Disjoint u
  DisjointUnion→Disjoint (x≈y ∷ᵣ u) = x≈y ∷ᵣ DisjointUnion→Disjoint u

  -- Reconstructing the union

  Disjoint→DisjointUnion : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
    Disjoint τ₁ τ₂ → ∃₂ λ us (τ : us ⊆ zs) → DisjointUnion τ₁ τ₂ τ
  Disjoint→DisjointUnion []         = _ , _ , []
  Disjoint→DisjointUnion (y   ∷ₙ u) = _ , _ , y   ∷ₙ proj₂ (proj₂ (Disjoint→DisjointUnion u))
  Disjoint→DisjointUnion (x≈y ∷ₗ u) = _ , _ , x≈y ∷ₗ proj₂ (proj₂ (Disjoint→DisjointUnion u))
  Disjoint→DisjointUnion (x≈y ∷ᵣ u) = _ , _ , x≈y ∷ᵣ proj₂ (proj₂ (Disjoint→DisjointUnion u))

  -- Disjoint is decidable

  ⊆-disjoint? : ∀ {xs ys zs} (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) → Dec (Disjoint τ₁ τ₂)
  ⊆-disjoint? [] [] = yes []
  -- Present in both sublists: not disjoint.
  ⊆-disjoint? (x≈z ∷ τ₁) (y≈z ∷ τ₂) = no λ()
  -- Present in either sublist: ok.
  ⊆-disjoint? (y ∷ʳ τ₁) (x≈y ∷ τ₂) =
    Dec.map′ (x≈y ∷ᵣ_) (λ{ (_ ∷ᵣ d) → d }) (⊆-disjoint? τ₁ τ₂)
  ⊆-disjoint? (x≈y ∷ τ₁) (y ∷ʳ τ₂) =
    Dec.map′ (x≈y ∷ₗ_) (λ{ (_ ∷ₗ d) → d }) (⊆-disjoint? τ₁ τ₂)
  -- Present in neither sublist: ok.
  ⊆-disjoint? (y ∷ʳ τ₁) (.y ∷ʳ τ₂) =
    Dec.map′ (y ∷ₙ_) (λ{ (_ ∷ₙ d) → d }) (⊆-disjoint? τ₁ τ₂)

  -- Disjoint is proof-irrelevant

  Disjoint-irrelevant : ∀{xs ys zs} → Irrelevant (Disjoint {R = R} {xs} {ys} {zs})
  Disjoint-irrelevant [] [] = ≡.refl
  Disjoint-irrelevant (y   ∷ₙ d₁) (.y   ∷ₙ d₂) = ≡.cong (y ∷ₙ_) (Disjoint-irrelevant d₁ d₂)
  Disjoint-irrelevant (x≈y ∷ₗ d₁) (.x≈y ∷ₗ d₂) = ≡.cong (x≈y ∷ₗ_) (Disjoint-irrelevant d₁ d₂)
  Disjoint-irrelevant (x≈y ∷ᵣ d₁) (.x≈y ∷ᵣ d₂) = ≡.cong (x≈y ∷ᵣ_) (Disjoint-irrelevant d₁ d₂)

  -- Note: DisjointUnion is not proof-irrelevant unless the underlying relation R is.
  -- The proof is not entirely trivial, thus, we leave it for future work:
  --
  -- DisjointUnion-irrelevant : Irrelevant R →
  --                            ∀{xs ys us zs} {τ : us ⊆ zs} →
  --                            Irrelevant (λ (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) → DisjointUnion τ₁ τ₂ τ)

  -- Irreflexivity

  Disjoint-irrefl′ : ∀{xs ys} {τ : xs ⊆ ys} → Disjoint τ τ → Null xs
  Disjoint-irrefl′ []       = []
  Disjoint-irrefl′ (y ∷ₙ d) = Disjoint-irrefl′ d

  Disjoint-irrefl : ∀{x xs ys} → Irreflexive {A = x ∷ xs ⊆ ys } _≡_ Disjoint
  Disjoint-irrefl ≡.refl x with Disjoint-irrefl′ x
  ... | () ∷ _

  -- Symmetry

  DisjointUnion-sym : ∀ {xs ys xys} {zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} {τ : xys ⊆ zs} →
                            DisjointUnion τ₁ τ₂ τ → DisjointUnion τ₂ τ₁ τ
  DisjointUnion-sym []         = []
  DisjointUnion-sym (y   ∷ₙ d) = y ∷ₙ DisjointUnion-sym d
  DisjointUnion-sym (x≈y ∷ₗ d) = x≈y ∷ᵣ DisjointUnion-sym d
  DisjointUnion-sym (x≈y ∷ᵣ d) = x≈y ∷ₗ DisjointUnion-sym d

  Disjoint-sym : ∀ {xs ys} {zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
                 Disjoint τ₁ τ₂ → Disjoint τ₂ τ₁
  Disjoint-sym []         = []
  Disjoint-sym (y   ∷ₙ d) = y ∷ₙ Disjoint-sym d
  Disjoint-sym (x≈y ∷ₗ d) = x≈y ∷ᵣ Disjoint-sym d
  Disjoint-sym (x≈y ∷ᵣ d) = x≈y ∷ₗ Disjoint-sym d

  -- Empty sublist

  DisjointUnion-[]ˡ : ∀{xs ys} {ε : [] ⊆ ys} {τ : xs ⊆ ys} → DisjointUnion ε τ τ
  DisjointUnion-[]ˡ {ε = []}     {τ = []} = []
  DisjointUnion-[]ˡ {ε = y ∷ʳ ε} {τ = y  ∷ʳ τ} = y   ∷ₙ DisjointUnion-[]ˡ
  DisjointUnion-[]ˡ {ε = y ∷ʳ ε} {τ = x≈y ∷ τ} = x≈y ∷ᵣ DisjointUnion-[]ˡ

  DisjointUnion-[]ʳ : ∀{xs ys} {ε : [] ⊆ ys} {τ : xs ⊆ ys} → DisjointUnion τ ε τ
  DisjointUnion-[]ʳ {ε = []}     {τ = []} = []
  DisjointUnion-[]ʳ {ε = y ∷ʳ ε} {τ = y  ∷ʳ τ} = y   ∷ₙ DisjointUnion-[]ʳ
  DisjointUnion-[]ʳ {ε = y ∷ʳ ε} {τ = x≈y ∷ τ} = x≈y ∷ₗ DisjointUnion-[]ʳ

  -- A sublist τ : x∷xs ⊆ ys can be split into two disjoint sublists
  -- [x] ⊆ ys (canonical choice) and (∷ˡ⁻ τ) : xs ⊆ ys.

  DisjointUnion-fromAny∘toAny-∷ˡ⁻ : ∀ {x xs ys} (τ : (x ∷ xs) ⊆ ys) → DisjointUnion (fromAny (toAny τ)) (∷ˡ⁻ τ) τ
  DisjointUnion-fromAny∘toAny-∷ˡ⁻ (y  ∷ʳ τ) = y   ∷ₙ DisjointUnion-fromAny∘toAny-∷ˡ⁻ τ
  DisjointUnion-fromAny∘toAny-∷ˡ⁻ (xRy ∷ τ) = xRy ∷ₗ DisjointUnion-[]ˡ

  -- Disjoint union of three mutually disjoint lists.
  --
  -- τᵢⱼ denotes the disjoint union of τᵢ and τⱼ: DisjointUnion τᵢ τⱼ τᵢⱼ

  record DisjointUnion³
    {xs ys zs ts} (τ₁  : xs  ⊆ ts) (τ₂  : ys  ⊆ ts) (τ₃  : zs  ⊆ ts)
    {xys xzs yzs} (τ₁₂ : xys ⊆ ts) (τ₁₃ : xzs ⊆ ts) (τ₂₃ : yzs ⊆ ts) : Set (a ⊔ b ⊔ r) where
    field
      {union³} : List A
      sub³  : union³ ⊆ ts
      join₁ : DisjointUnion τ₁ τ₂₃ sub³
      join₂ : DisjointUnion τ₂ τ₁₃ sub³
      join₃ : DisjointUnion τ₃ τ₁₂ sub³

  infixr 5 _∷ʳ-DisjointUnion³_ _∷₁-DisjointUnion³_ _∷₂-DisjointUnion³_ _∷₃-DisjointUnion³_

  -- Weakening the target list ts of a disjoint union.

  _∷ʳ-DisjointUnion³_ :
    ∀ {xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts} →
    ∀ {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
    ∀ y →
    DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃ →
    DisjointUnion³ (y ∷ʳ τ₁) (y ∷ʳ τ₂) (y ∷ʳ τ₃) (y ∷ʳ τ₁₂) (y ∷ʳ τ₁₃) (y ∷ʳ τ₂₃)
  y ∷ʳ-DisjointUnion³ record{ sub³ = σ ; join₁ = d₁ ; join₂ = d₂ ; join₃ = d₃ } = record
    { sub³  = y ∷ʳ σ
    ; join₁ = y ∷ₙ d₁
    ; join₂ = y ∷ₙ d₂
    ; join₃ = y ∷ₙ d₃
    }

  -- Adding an element to the first list.

  _∷₁-DisjointUnion³_ :
    ∀ {xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts} →
    ∀ {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
    ∀ {x y} (xRy : R x y) →
    DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃ →
    DisjointUnion³ (xRy ∷ τ₁) (y ∷ʳ τ₂) (y ∷ʳ τ₃) (xRy ∷ τ₁₂) (xRy ∷ τ₁₃) (y ∷ʳ τ₂₃)
  xRy ∷₁-DisjointUnion³ record{ sub³ = σ ; join₁ = d₁ ; join₂ = d₂ ; join₃ = d₃ } = record
    { sub³  = xRy ∷ σ
    ; join₁ = xRy ∷ₗ d₁
    ; join₂ = xRy ∷ᵣ d₂
    ; join₃ = xRy ∷ᵣ d₃
    }

  -- Adding an element to the second list.

  _∷₂-DisjointUnion³_ :
    ∀ {xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts} →
    ∀ {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
    ∀ {x y} (xRy : R x y) →
    DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃ →
    DisjointUnion³ (y ∷ʳ τ₁) (xRy ∷ τ₂) (y ∷ʳ τ₃) (xRy ∷ τ₁₂) (y ∷ʳ τ₁₃) (xRy ∷ τ₂₃)
  xRy ∷₂-DisjointUnion³ record{ sub³ = σ ; join₁ = d₁ ; join₂ = d₂ ; join₃ = d₃ } = record
    { sub³  = xRy ∷ σ
    ; join₁ = xRy ∷ᵣ d₁
    ; join₂ = xRy ∷ₗ d₂
    ; join₃ = xRy ∷ᵣ d₃
    }

  -- Adding an element to the third list.

  _∷₃-DisjointUnion³_ :
    ∀ {xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts} →
    ∀ {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
    ∀ {x y} (xRy : R x y) →
    DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃ →
    DisjointUnion³ (y ∷ʳ τ₁) (y ∷ʳ τ₂) (xRy ∷ τ₃) (y ∷ʳ τ₁₂) (xRy ∷ τ₁₃) (xRy ∷ τ₂₃)
  xRy ∷₃-DisjointUnion³ record{ sub³ = σ ; join₁ = d₁ ; join₂ = d₂ ; join₃ = d₃ } = record
    { sub³  = xRy ∷ σ
    ; join₁ = xRy ∷ᵣ d₁
    ; join₂ = xRy ∷ᵣ d₂
    ; join₃ = xRy ∷ₗ d₃
    }

  -- Computing the disjoint union of three disjoint lists.

  disjointUnion³ : ∀{xs ys zs ts} {τ₁ : xs ⊆ ts} {τ₂ : ys ⊆ ts} {τ₃ : zs ⊆ ts}
    {xys xzs yzs} {τ₁₂ : xys ⊆ ts} {τ₁₃ : xzs ⊆ ts} {τ₂₃ : yzs ⊆ ts} →
    DisjointUnion τ₁ τ₂ τ₁₂ →
    DisjointUnion τ₁ τ₃ τ₁₃ →
    DisjointUnion τ₂ τ₃ τ₂₃ →
    DisjointUnion³ τ₁ τ₂ τ₃ τ₁₂ τ₁₃ τ₂₃
  disjointUnion³ [] [] [] = record { sub³ = [] ; join₁ = [] ; join₂ = [] ; join₃ = [] }
  disjointUnion³ (y   ∷ₙ d₁₂) (.y  ∷ₙ d₁₃) (.y   ∷ₙ d₂₃) = y ∷ʳ-DisjointUnion³ disjointUnion³ d₁₂ d₁₃ d₂₃
  disjointUnion³ (y   ∷ₙ d₁₂) (xRy ∷ᵣ d₁₃) (.xRy ∷ᵣ d₂₃) = xRy ∷₃-DisjointUnion³ disjointUnion³ d₁₂ d₁₃ d₂₃
  disjointUnion³ (xRy ∷ᵣ d₁₂) (y   ∷ₙ d₁₃) (.xRy ∷ₗ d₂₃) = xRy ∷₂-DisjointUnion³ disjointUnion³ d₁₂ d₁₃ d₂₃
  disjointUnion³ (xRy ∷ₗ d₁₂) (.xRy ∷ₗ d₁₃) (y    ∷ₙ d₂₃) = xRy ∷₁-DisjointUnion³ disjointUnion³ d₁₂ d₁₃ d₂₃
  disjointUnion³ (xRy ∷ᵣ d₁₂) (xRy′ ∷ᵣ d₁₃) ()

  -- If a sublist τ is disjoint to two lists σ₁ and σ₂,
  -- then also to their disjoint union σ.

  disjoint⇒disjoint-to-union : ∀{xs ys zs yzs ts}
    {τ : xs ⊆ ts} {σ₁ : ys ⊆ ts} {σ₂ : zs ⊆ ts} {σ : yzs ⊆ ts} →
    Disjoint τ σ₁ → Disjoint τ σ₂ → DisjointUnion σ₁ σ₂ σ → Disjoint τ σ
  disjoint⇒disjoint-to-union d₁ d₂ u = let
       _ , _ , u₁ = Disjoint→DisjointUnion d₁
       _ , _ , u₂ = Disjoint→DisjointUnion d₂
    in DisjointUnion→Disjoint (DisjointUnion³.join₁ (disjointUnion³ u₁ u₂ u))

open Disjointness public

-- Monotonicity of disjointness.

module DisjointnessMonotonicity
    {R : REL A B r} {S : REL B C s} {T : REL A C t}
    (rs⇒t : Trans R S T) where

  -- We can enlarge and convert the target list of a disjoint union.

  weakenDisjointUnion : ∀ {xs ys xys zs ws}
    {τ₁ : Sublist R xs zs}
    {τ₂ : Sublist R ys zs}
    {τ : Sublist R xys zs} (σ : Sublist S zs ws) →
    DisjointUnion τ₁ τ₂ τ →
    DisjointUnion (trans rs⇒t τ₁ σ) (trans rs⇒t τ₂ σ) (trans rs⇒t τ σ)
  weakenDisjointUnion [] [] = []
  weakenDisjointUnion (w  ∷ʳ σ) d         = w ∷ₙ weakenDisjointUnion σ d
  weakenDisjointUnion (_   ∷ σ) (y   ∷ₙ d) = _ ∷ₙ weakenDisjointUnion σ d
  weakenDisjointUnion (zSw ∷ σ) (xRz ∷ₗ d) = rs⇒t xRz zSw ∷ₗ weakenDisjointUnion σ d
  weakenDisjointUnion (zSw ∷ σ) (yRz ∷ᵣ d) = rs⇒t yRz zSw ∷ᵣ weakenDisjointUnion σ d

  weakenDisjoint : ∀ {xs ys zs ws}
    {τ₁ : Sublist R xs zs}
    {τ₂ : Sublist R ys zs} (σ : Sublist S zs ws) →
    Disjoint τ₁ τ₂ →
    Disjoint (trans rs⇒t τ₁ σ) (trans rs⇒t τ₂ σ)
  weakenDisjoint [] [] = []
  weakenDisjoint (w  ∷ʳ σ) d         = w ∷ₙ weakenDisjoint σ d
  weakenDisjoint (_   ∷ σ) (y   ∷ₙ d) = _ ∷ₙ weakenDisjoint σ d
  weakenDisjoint (zSw ∷ σ) (xRz ∷ₗ d) = rs⇒t xRz zSw ∷ₗ weakenDisjoint σ d
  weakenDisjoint (zSw ∷ σ) (yRz ∷ᵣ d) = rs⇒t yRz zSw ∷ᵣ weakenDisjoint σ d

  -- Lists remain disjoint when elements are removed.

  shrinkDisjoint : ∀ {us vs xs ys zs}
                      (σ₁ : Sublist R us xs) {τ₁ : Sublist S xs zs}
                      (σ₂ : Sublist R vs ys) {τ₂ : Sublist S ys zs} →
                      Disjoint τ₁ τ₂ →
                      Disjoint (trans rs⇒t σ₁ τ₁) (trans rs⇒t σ₂ τ₂)
  shrinkDisjoint σ₁         σ₂ (y   ∷ₙ d) = y ∷ₙ shrinkDisjoint σ₁ σ₂ d
  shrinkDisjoint (x  ∷ʳ σ₁) σ₂ (xSz ∷ₗ d) = _ ∷ₙ shrinkDisjoint σ₁ σ₂ d
  shrinkDisjoint (uRx ∷ σ₁) σ₂ (xSz ∷ₗ d) = rs⇒t uRx xSz ∷ₗ shrinkDisjoint σ₁ σ₂ d
  shrinkDisjoint σ₁ (y  ∷ʳ σ₂) (ySz ∷ᵣ d) = _ ∷ₙ shrinkDisjoint σ₁ σ₂ d
  shrinkDisjoint σ₁ (vRy ∷ σ₂) (ySz ∷ᵣ d) = rs⇒t vRy ySz ∷ᵣ shrinkDisjoint σ₁ σ₂ d
  shrinkDisjoint [] []         []         = []

open DisjointnessMonotonicity public
