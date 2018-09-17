------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of list-splitting
------------------------------------------------------------------------

module Data.List.Relation.Split.Properties where

open import Data.Nat
open import Data.Nat.Properties using (+-suc)
open import Data.List.Base as List using (List; []; _∷_)
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
  length (l ˡ∷ sp) = P.cong suc (length sp)
  length {as} {l} {r ∷ rs} (_ ʳ∷ sp) = begin
    List.length as                       ≡⟨ P.cong suc (length sp) ⟩
    suc (List.length l + List.length rs) ≡⟨ P.sym $ +-suc _ _ ⟩
    List.length l + List.length (r ∷ rs) ∎ where open P.≡-Reasoning

------------------------------------------------------------------------
-- Split is stable under some List functions

-- (++)

  ++⁺ : ∀ {as₁ as₂ l₁ l₂ r₁ r₂} → Split L R as₁ l₁ r₁ → Split L R as₂ l₂ r₂ →
        Split L R (as₁ List.++ as₂) (l₁ List.++ l₂) (r₁ List.++ r₂)
  ++⁺ []         sp₂ = sp₂
  ++⁺ (l ˡ∷ sp₁) sp₂ = l ˡ∷ (++⁺ sp₁ sp₂)
  ++⁺ (r ʳ∷ sp₁) sp₂ = r ʳ∷ (++⁺ sp₁ sp₂)

-- reverse

  reverseAcc⁺ : ∀ {as₁ as₂ l₁ l₂ r₁ r₂} → Split L R as₁ l₁ r₁ → Split L R as₂ l₂ r₂ →
    Split L R (List.reverseAcc as₁ as₂) (List.reverseAcc l₁ l₂) (List.reverseAcc r₁ r₂)
  reverseAcc⁺ sp₁ []         = sp₁
  reverseAcc⁺ sp₁ (l ˡ∷ sp₂) = reverseAcc⁺ (l ˡ∷ sp₁) sp₂
  reverseAcc⁺ sp₁ (r ʳ∷ sp₂) = reverseAcc⁺ (r ʳ∷ sp₁) sp₂

  reverse⁺ : ∀ {as l r} → Split L R as l r →
            Split L R (List.reverse as) (List.reverse l) (List.reverse r)
  reverse⁺ = reverseAcc⁺ []

  reverse⁻ : ∀ {as l r} → Split L R (List.reverse as) (List.reverse l) (List.reverse r) →
             Split L R as l r
  reverse⁻ {as} {l} {r} sp with reverse⁺ sp
  ... | sp′ rewrite reverse-involutive as
                  | reverse-involutive l
                  | reverse-involutive r = sp′

