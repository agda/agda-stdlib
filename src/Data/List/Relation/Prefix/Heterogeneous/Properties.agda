------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous prefix relation
------------------------------------------------------------------------

module Data.List.Relation.Prefix.Heterogeneous.Properties where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Prefix.Heterogeneous
open import Data.Product using (uncurry)
open import Function

open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary

------------------------------------------------------------------------
-- First as a decidable partial order (once made homogeneous)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  refl : Pointwise R ⇒ Prefix R
  refl []       = []
  refl (x ∷ xs) = x ∷ refl xs

module _ {a b c r s t} {A : Set a} {B : Set b} {C : Set c}
         {R : REL A B r} {S : REL B C s} {T : REL A C t} where

  trans : Trans R S T → Trans (Prefix R) (Prefix S) (Prefix T)
  trans rs⇒t []            bs~cs         = []
  trans rs⇒t (a∼b ∷ as∼bs) (b∼c ∷ bs∼cs) = rs⇒t a∼b b∼c ∷ trans rs⇒t as∼bs bs∼cs

module _ {a b r s e} {A : Set a} {B : Set b}
         {R : REL A B r} {S : REL B A s} {E : REL A B e} where

  antisym : Antisym R S E → Antisym (Prefix R) (Prefix S) (Pointwise E)
  antisym rs⇒e []            []            = []
  antisym rs⇒e (a∼b ∷ as∼bs) (b∼a ∷ bs∼as) = rs⇒e a∼b b∼a ∷ antisym rs⇒e as∼bs bs∼as

------------------------------------------------------------------------
-- _++_

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  ++⁺ : ∀ {as bs cs ds} → Pointwise R as bs →
        Prefix R cs ds → Prefix R (as List.++ cs) (bs List.++ ds)
  ++⁺ []            cs⊆ds = cs⊆ds
  ++⁺ (a∼b ∷ as∼bs) cs⊆ds = a∼b ∷ (++⁺ as∼bs cs⊆ds)

  ++⁻ : ∀ {as bs cs ds} → Pointwise R as bs →
        Prefix R (as List.++ cs) (bs List.++ ds) → Prefix R cs ds
  ++⁻ []            cs⊆ds         = cs⊆ds
  ++⁻ (a∼b ∷ as∼bs) (_ ∷ acs⊆bds) = ++⁻ as∼bs acs⊆bds

------------------------------------------------------------------------
-- map

module _ {a b c d r} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {R : REL C D r} where

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Prefix (λ a b → R (f a) (g b)) as bs →
         Prefix R (List.map f as) (List.map g bs)
  map⁺ f g []       = []
  map⁺ f g (x ∷ xs) = x ∷ map⁺ f g xs

  map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
         Prefix R (List.map f as) (List.map g bs) →
         Prefix (λ a b → R (f a) (g b)) as bs
  map⁻ {[]}     {bs}     f g xs = []
  map⁻ {a ∷ as} {[]}     f g ()
  map⁻ {a ∷ as} {b ∷ bs} f g (x ∷ xs) = x ∷ map⁻ f g xs

------------------------------------------------------------------------
-- Decidability

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  prefix? : Decidable R → Decidable (Prefix R)
  prefix? R? []       bs       = yes []
  prefix? R? (a ∷ as) []       = no (λ ())
  prefix? R? (a ∷ as) (b ∷ bs) = Dec.map′ (uncurry _∷_) uncons
                               $ R? a b ×-dec prefix? R? as bs
