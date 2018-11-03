------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous prefix relation
------------------------------------------------------------------------

module Data.List.Relation.Prefix.Heterogeneous.Properties where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Prefix.Heterogeneous
open import Relation.Binary

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  refl : Pointwise R ⇒ Prefix R
  refl []       = []
  refl (x ∷ xs) = x ∷ refl xs

  infixl 5 _++_
  _++_ : ∀ {as bs cs ds} → Pointwise R as bs → Prefix R cs ds →
         Prefix R (as List.++ cs) (bs List.++ ds)
  []            ++ cs⊆ds = cs⊆ds
  (a∼b ∷ as∼bs) ++ cs⊆ds = a∼b ∷ (as∼bs ++ cs⊆ds)

module _ {a b c r s t} {A : Set a} {B : Set b} {C : Set c}
         {R : REL A B r} {S : REL B C s} {T : REL A C t} where

  trans : Trans R S T → Trans (Prefix R) (Prefix S) (Prefix T)
  trans rs⇒t []            bs~cs         = []
  trans rs⇒t (a∼b ∷ as∼bs) (b∼c ∷ bs∼cs) = rs⇒t a∼b b∼c ∷ trans rs⇒t as∼bs bs∼cs

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
