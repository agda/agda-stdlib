------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of general interleavings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Interleaving.Properties where

open import Data.Nat
open import Data.Nat.Properties using (+-suc)
open import Data.List.Base hiding (_∷ʳ_)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Interleaving hiding (map)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning)
open ≡-Reasoning

------------------------------------------------------------------------
-- length

module _ {a b c l r} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A C l} {R : REL B C r} where

  interleave-length : ∀ {as l r} → Interleaving L R l r as →
                      length as ≡ length l + length r
  interleave-length []        = refl
  interleave-length (l ∷ˡ sp) = cong suc (interleave-length sp)
  interleave-length {as} {l} {r ∷ rs} (_ ∷ʳ sp) = begin
    length as                   ≡⟨ cong suc (interleave-length sp) ⟩
    suc (length l + length rs)  ≡⟨ sym $ +-suc _ _ ⟩
    length l + length (r ∷ rs)  ∎

------------------------------------------------------------------------
-- _++_

  ++⁺ : ∀ {as₁ as₂ l₁ l₂ r₁ r₂} →
        Interleaving L R as₁ l₁ r₁ → Interleaving L R as₂ l₂ r₂ →
        Interleaving L R (as₁ ++ as₂) (l₁ ++ l₂) (r₁ ++ r₂)
  ++⁺ []         sp₂ = sp₂
  ++⁺ (l ∷ˡ sp₁) sp₂ = l ∷ˡ (++⁺ sp₁ sp₂)
  ++⁺ (r ∷ʳ sp₁) sp₂ = r ∷ʳ (++⁺ sp₁ sp₂)

  ++-disjoint : ∀ {as₁ as₂ l₁ r₂} →
                Interleaving L R l₁ [] as₁ → Interleaving L R [] r₂ as₂ →
                Interleaving L R l₁ r₂ (as₁ ++ as₂)
  ++-disjoint []         sp₂ = sp₂
  ++-disjoint (l ∷ˡ sp₁) sp₂ = l ∷ˡ ++-disjoint sp₁ sp₂

------------------------------------------------------------------------
-- map

module _ {a b c d e f l r}
         {A : Set a} {B : Set b} {C : Set c}
         {D : Set d} {E : Set e} {F : Set f}
         {L : REL A C l} {R : REL B C r}
         (f : E → A) (g : F → B) (h : D → C)
         where

  map⁺ : ∀ {as l r} →
         Interleaving (λ x z → L (f x) (h z)) (λ y z → R (g y) (h z)) l r as  →
         Interleaving L R (map f l) (map g r) (map h as)
  map⁺ []        = []
  map⁺ (l ∷ˡ sp) = l ∷ˡ map⁺ sp
  map⁺ (r ∷ʳ sp) = r ∷ʳ map⁺ sp

  map⁻ : ∀ {as l r} →
         Interleaving L R (map f l) (map g r) (map h as) →
         Interleaving (λ x z → L (f x) (h z)) (λ y z → R (g y) (h z)) l r as
  map⁻ {[]}    {[]}    {[]}    []        = []
  map⁻ {_ ∷ _} {[]}    {_ ∷ _} (r ∷ʳ sp) = r ∷ʳ map⁻ sp
  map⁻ {_ ∷ _} {_ ∷ _} {[]}    (l ∷ˡ sp) = l ∷ˡ map⁻ sp
  map⁻ {_ ∷ _} {_ ∷ _} {_ ∷ _} (l ∷ˡ sp) = l ∷ˡ map⁻ sp
  map⁻ {_ ∷ _} {_ ∷ _} {_ ∷ _} (r ∷ʳ sp) = r ∷ʳ map⁻ sp
  -- impossible cases needed until 2.6.0
  map⁻ {[]} {_} {_ ∷ _} ()
  map⁻ {[]} {_ ∷ _} {_} ()
  map⁻ {_ ∷ _} {[]} {[]} ()

------------------------------------------------------------------------
-- reverse

module _ {a b c l r} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A C l} {R : REL B C r}
         where

  reverseAcc⁺ : ∀ {as₁ as₂ l₁ l₂ r₁ r₂} →
                Interleaving L R l₁ r₁ as₁ →
                Interleaving L R l₂ r₂ as₂ →
                Interleaving L R (reverseAcc l₁ l₂) (reverseAcc r₁ r₂) (reverseAcc as₁ as₂)
  reverseAcc⁺ sp₁ []         = sp₁
  reverseAcc⁺ sp₁ (l ∷ˡ sp₂) = reverseAcc⁺ (l ∷ˡ sp₁) sp₂
  reverseAcc⁺ sp₁ (r ∷ʳ sp₂) = reverseAcc⁺ (r ∷ʳ sp₁) sp₂

  reverse⁺ : ∀ {as l r} → Interleaving L R l r as →
             Interleaving L R (reverse l) (reverse r) (reverse as)
  reverse⁺ = reverseAcc⁺ []

  reverse⁻ : ∀ {as l r} → Interleaving L R (reverse l) (reverse r) (reverse as) →
             Interleaving L R l r as
  reverse⁻ {as} {l} {r} sp with reverse⁺ sp
  ... | sp′ rewrite reverse-involutive as
                  | reverse-involutive l
                  | reverse-involutive r = sp′
