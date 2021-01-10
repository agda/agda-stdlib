------------------------------------------------------------------------
-- The Agda standard library
--
-- Regular expressions: Brzozowski derivative
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecPoset)

module Text.Regex.Derivative.Brzozowski {a e r} (P? : DecPoset a e r) where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.Sum.Base as Sum using (inj₁; inj₂)

open import Function.Base using (_$_; _∘′_; case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction; ¬?)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open DecPoset P? using (preorder) renaming (Carrier to A)
open import Text.Regex.Base preorder as R hiding (_∣_; _∙_; _⋆)
open import Text.Regex.Properties P?
open import Text.Regex.SmartConstructors preorder

open import Data.List.Relation.Ternary.Appending.Propositional {A = A}
open import Data.List.Relation.Ternary.Appending.Propositional.Properties {A = A}

------------------------------------------------------------------------
-- Action of characters on regular expressions

private
  decToExp : ∀ {p} {P : Set p} → Dec P → Exp
  decToExp (yes _) = ε
  decToExp (no _)  = ∅

eat : A → Exp → Exp
eat a ε         = ∅
eat a [ rs ]    = decToExp ((a ∷ []) ∈?[ rs ])
eat a [^ rs ]   = decToExp ((a ∷ []) ∈?[^ rs ])
eat a (e R.∣ f) = eat a e ∣ eat a f
eat a (e R.∙ f) = case []∈? e of λ where
  (yes _) → (eat a e ∙ f) ∣ (eat a f)
  (no ¬p) → eat a e ∙ f
eat a (e R.⋆)   = eat a e ∙ (e ⋆)

------------------------------------------------------------------------
-- This action is sound and complete with respect to matching

eat-sound : ∀ x {xs} e → xs ∈ eat x e → (x ∷ xs) ∈ e
eat-sound x ε         pr = contradiction pr ∉∅
eat-sound x [ rs ]    pr with (x ∷ []) ∈?[ rs ]
... | yes p = case pr of λ where ε → p
... | no _  = contradiction pr ∉∅
eat-sound x [^ rs ]   pr with (x ∷ []) ∈?[^ rs ]
... | yes p = case pr of λ where ε → p
... | no _  = contradiction pr ∉∅
eat-sound x (e R.∣ f) pr with ∣-sound (eat x e) (eat x f) pr
... | sum pr′ = sum $ Sum.map (eat-sound x e) (eat-sound x f) pr′
eat-sound x (e R.∙ f) pr with []∈? e
... | yes []∈e with ∣-sound (eat x e ∙ f) (eat x f) pr
... | sum (inj₂ pr') = prod ([] ++ _) []∈e (eat-sound x f pr')
... | sum (inj₁ pr') with ∙-sound (eat x e) f pr'
... | prod eq p q = prod (refl ∷ eq) (eat-sound x e p) q
eat-sound x (e R.∙ f) pr | no ¬p with ∙-sound (eat x e) f pr
... | prod eq p q = prod (refl ∷ eq) (eat-sound x e p) q
eat-sound x (e R.⋆) pr with ∙-sound (eat x e) (e ⋆) pr
... | prod eq p q =
  star (sum (inj₂ (prod (refl ∷ eq) (eat-sound x e p) (⋆-sound e q))))

eat-complete′ : ∀ x {xs w} e → w ≋ (x ∷ xs) → w ∈ e → xs ∈ eat x e
eat-complete  : ∀ x {xs} e → (x ∷ xs) ∈ e → xs ∈ eat x e

eat-complete x e = eat-complete′ x e ≋-refl

eat-complete′ x [ rs ] (refl ∷ []) [ p ]
  with (x ∷ []) ∈?[ rs ]
... | yes _ = ε
... | no ¬p = contradiction [ p ] ¬p
eat-complete′ x [^ rs ] (refl ∷ []) [^ p ]
  with (x ∷ []) ∈?[^ rs ]
... | yes _ = ε
... | no ¬p = contradiction [^ p ] ¬p
eat-complete′ x (e R.∣ f) eq (sum p) =
  ∣-complete (eat x e) (eat x f) $ sum $
  Sum.map (eat-complete′ x e eq) (eat-complete′ x f eq) p
eat-complete′ x (e R.∙ f) eq p with []∈? e
eat-complete′ x (e R.∙ f) (refl ∷ eq) (prod ([]++ _) p q) | no []∉e
  = contradiction p []∉e
eat-complete′ x (e R.∙ f) (refl ∷ eq) (prod (refl ∷ app) p q) | no []∉e
  = ∙-complete (eat x e) f (prod (respʳ-≋ app eq) (eat-complete x e p) q)
eat-complete′ x (e R.∙ f) eq (prod ([]++ eq′) p q) | yes []∈e
  = ∣-complete (eat x e ∙ f) (eat x f) $ sum $ inj₂
  $ eat-complete′ x f (≋-trans eq′ eq) q
eat-complete′ x (e R.∙ f) (refl ∷ eq) (prod (refl ∷ app) p q) | yes []∈e
  = ∣-complete (eat x e ∙ f) (eat x f) $ sum $ inj₁
  $ ∙-complete (eat x e) f (prod (respʳ-≋ app eq) (eat-complete x e p) q)
eat-complete′ x (e R.⋆) eq (star (sum (inj₂ (prod ([]++ app) p q))))
  = eat-complete′ x (e R.⋆) (≋-trans app eq) q
eat-complete′ x (e R.⋆) (refl ∷ eq) (star (sum (inj₂ (prod (refl ∷ app) p q))))
  = ∙-complete (eat x e) (e ⋆) $ prod (respʳ-≋ app eq) (eat-complete x e p)
  $ ⋆-complete e q

------------------------------------------------------------------------
-- Consequence: matching is decidable

_∈?_ : Decidable _∈_
[]       ∈? e = []∈? e
(x ∷ xs) ∈? e = map′ (eat-sound x e) (eat-complete x e) (xs ∈? eat x e)

_∉?_ : Decidable _∉_
xs ∉? e = ¬? (xs ∈? e)
