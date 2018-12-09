-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Sublist.Heterogeneous.Properties where

open import Data.Empty
open import Data.List.Any using (Any; here; there)
open import Data.List.Base as List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Sublist.Heterogeneous
open import Data.Nat using (ℕ; _≤_); open ℕ; open _≤_
open import Data.Nat.Properties
  using (suc-injective; ≤-step; n≤1+n; <-irrefl; module ≤-Reasoning)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  fromAny : ∀ {a bs} → Any (R a) bs → Sublist R [ a ] bs
  fromAny (here r)  = r ∷ minimum _
  fromAny (there p) = _ ∷ʳ fromAny p

  toAny : ∀ {a bs} → Sublist R [ a ] bs → Any (R a) bs
  toAny (y ∷ʳ rs) = there (toAny rs)
  toAny (r ∷ rs)  = here r

  length-mono-Sublist-≤ : ∀ {as bs} → Sublist R as bs → length as ≤ length bs
  length-mono-Sublist-≤ []        = z≤n
  length-mono-Sublist-≤ (y ∷ʳ rs) = ≤-step (length-mono-Sublist-≤ rs)
  length-mono-Sublist-≤ (r ∷ rs)  = s≤s (length-mono-Sublist-≤ rs)

  fromPointwise : Pointwise R ⇒ Sublist R
  fromPointwise []       = []
  fromPointwise (r ∷ rs) = r ∷ fromPointwise rs

  toPointwise : ∀ {as bs} → length as ≡ length bs →
                Sublist R as bs → Pointwise R as bs
  toPointwise {bs = []}     eq []         = []
  toPointwise {bs = b ∷ bs} eq (r ∷ rs)   = r ∷ toPointwise (suc-injective eq) rs
  toPointwise {bs = b ∷ bs} eq (.b ∷ʳ rs) =
    ⊥-elim $ <-irrefl eq (s≤s (length-mono-Sublist-≤ rs))

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
    ⊥-elim $ <-irrefl P.refl $ begin
    length (y ∷ ys₁) ≤⟨ length-mono-Sublist-≤ ss ⟩
    length zs        ≤⟨ n≤1+n (length zs) ⟩
    length (z ∷ zs)  ≤⟨ length-mono-Sublist-≤ rs ⟩
    length ys₁       ∎ where open ≤-Reasoning
  antisym rs⇒e (_∷ʳ_ {xs} {ys₁} y rs) (_∷_ {y} {ys₂} {z} {zs} s ss)  =
    ⊥-elim $ <-irrefl P.refl $ begin
    length (z ∷ zs) ≤⟨ length-mono-Sublist-≤ rs ⟩
    length ys₁      ≤⟨ length-mono-Sublist-≤ ss ⟩
    length zs       ∎ where open ≤-Reasoning
  antisym rs⇒e (_∷_ {x} {xs} {y} {ys₁} r rs)  (_∷ʳ_ {ys₂} {zs} z ss) =
    ⊥-elim $ <-irrefl P.refl $ begin
    length (y ∷ ys₁) ≤⟨ length-mono-Sublist-≤ ss ⟩
    length xs        ≤⟨ length-mono-Sublist-≤ rs ⟩
    length ys₁       ∎ where open ≤-Reasoning

------------------------------------------------------------------------
-- _++_

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  ++⁺ : ∀ {as bs cs ds} → Sublist R as bs → Sublist R cs ds →
        Sublist R (as ++ cs) (bs ++ ds)
  ++⁺ []         cds = cds
  ++⁺ (y ∷ʳ abs) cds = y ∷ʳ ++⁺ abs cds
  ++⁺ (ab ∷ abs) cds = ab ∷ ++⁺ abs cds

------------------------------------------------------------------------
-- map

module _ {a b c d r} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {R : REL C D r} where

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
