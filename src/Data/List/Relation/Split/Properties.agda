------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of list-splitting
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.List.Relation.Split.Properties where

open import Data.Nat
open import Data.Nat.Properties using (+-suc)
open import Data.List.Base as List using (List; []; _∷_; filter)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Relation.Split
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module _ {a b c l r} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A B l} {R : REL A C r} where

  length : ∀ {as l r} → Split L R as l r →
           List.length as ≡ List.length l + List.length r
  length []        = P.refl
  length (l ∷ˡ sp) = P.cong suc (length sp)
  length {as} {l} {r ∷ rs} (_ ∷ʳ sp) = begin
    List.length as                       ≡⟨ P.cong suc (length sp) ⟩
    suc (List.length l + List.length rs) ≡⟨ P.sym $ +-suc _ _ ⟩
    List.length l + List.length (r ∷ rs) ∎ where open P.≡-Reasoning

------------------------------------------------------------------------
-- Split is stable under some List functions

-- (++)

  ++⁺ : ∀ {as₁ as₂ l₁ l₂ r₁ r₂} → Split L R as₁ l₁ r₁ → Split L R as₂ l₂ r₂ →
        Split L R (as₁ List.++ as₂) (l₁ List.++ l₂) (r₁ List.++ r₂)
  ++⁺ []         sp₂ = sp₂
  ++⁺ (l ∷ˡ sp₁) sp₂ = l ∷ˡ (++⁺ sp₁ sp₂)
  ++⁺ (r ∷ʳ sp₁) sp₂ = r ∷ʳ (++⁺ sp₁ sp₂)

  disjoint : ∀ {as₁ as₂ l₁ r₂} → Split L R as₁ l₁ [] → Split L R as₂ [] r₂ →
             Split L R (as₁ List.++ as₂) l₁ r₂
  disjoint []         sp₂ = sp₂
  disjoint (l ∷ˡ sp₁) sp₂ = l ∷ˡ disjoint sp₁ sp₂

module _ {a b c l r} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A B l} {R : REL A C r}
         {d e f} {D : Set d} {E : Set e} {F : Set f}
         (f : D → A) (g : E → B) (h : F → C)
         where

-- map

  map⁺ : ∀ {as l r} →
         Split (λ a b → L (f a) (g b)) (λ a c → R (f a) (h c)) as l r →
         Split L R (List.map f as) (List.map g l) (List.map h r)
  map⁺ []        = []
  map⁺ (l ∷ˡ sp) = l ∷ˡ map⁺ sp
  map⁺ (r ∷ʳ sp) = r ∷ʳ map⁺ sp

  map⁻ : ∀ {as l r} →
         Split L R (List.map f as) (List.map g l) (List.map h r) →
         Split (λ a b → L (f a) (g b)) (λ a c → R (f a) (h c)) as l r
  map⁻ {[]}    {[]}    {[]}    []        = []
  map⁻ {_ ∷ _} {[]}    {_ ∷ _} (r ∷ʳ sp) = r ∷ʳ map⁻ sp
  map⁻ {_ ∷ _} {_ ∷ _} {[]}    (l ∷ˡ sp) = l ∷ˡ map⁻ sp
  map⁻ {_ ∷ _} {_ ∷ _} {_ ∷ _} (l ∷ˡ sp) = l ∷ˡ map⁻ sp
  map⁻ {_ ∷ _} {_ ∷ _} {_ ∷ _} (r ∷ʳ sp) = r ∷ʳ map⁻ sp
  -- impossible cases needed until 2.6.0
  map⁻ {[]} {_} {_ ∷ _} ()
  map⁻ {[]} {_ ∷ _} {_} ()
  map⁻ {_ ∷ _} {[]} {[]} ()

module _ {a b c l r} {A : Set a} {B : Set b} {C : Set c}
         {L : REL A B l} {R : REL A C r}
         where

-- reverse

  reverseAcc⁺ : ∀ {as₁ as₂ l₁ l₂ r₁ r₂} → Split L R as₁ l₁ r₁ → Split L R as₂ l₂ r₂ →
    Split L R (List.reverseAcc as₁ as₂) (List.reverseAcc l₁ l₂) (List.reverseAcc r₁ r₂)
  reverseAcc⁺ sp₁ []         = sp₁
  reverseAcc⁺ sp₁ (l ∷ˡ sp₂) = reverseAcc⁺ (l ∷ˡ sp₁) sp₂
  reverseAcc⁺ sp₁ (r ∷ʳ sp₂) = reverseAcc⁺ (r ∷ʳ sp₁) sp₂

  reverse⁺ : ∀ {as l r} → Split L R as l r →
            Split L R (List.reverse as) (List.reverse l) (List.reverse r)
  reverse⁺ = reverseAcc⁺ []

  reverse⁻ : ∀ {as l r} → Split L R (List.reverse as) (List.reverse l) (List.reverse r) →
             Split L R as l r
  reverse⁻ {as} {l} {r} sp with reverse⁺ sp
  ... | sp′ rewrite reverse-involutive as
                  | reverse-involutive l
                  | reverse-involutive r = sp′
