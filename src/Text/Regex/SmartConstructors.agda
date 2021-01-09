------------------------------------------------------------------------
-- The Agda standard library
--
-- Regular expressions: smart constructors
-- Computing the Brzozowski derivative of a regular expression may lead
-- to a blow-up in the size of the expression. To keep it tractable it
-- is crucial to use smart constructors.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Preorder)

module Text.Regex.SmartConstructors {a e r} (P : Preorder a e r) where

open import Data.List.Base using ([])
open import Data.List.Relation.Ternary.Appending.Propositional
open import Data.Sum.Base using (inj₁; inj₂; fromInj₁; fromInj₂)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (refl)

open import Text.Regex.Base P as R hiding (_∣_; _∙_; _⋆)
open import Text.Regex.Properties.Core P

------------------------------------------------------------------------
-- Sum

infixr 5 _∣_

_∣_ : (e f : Exp) → Exp
e ∣ f with is-∅ e | is-∅ f
... | yes _ | _ = f
... | _ | yes _ = e
... | _ | _     = e R.∣ f

∣-sound : ∀ {w} e f → w ∈ (e ∣ f) → w ∈ (e R.∣ f)
∣-sound e f p with is-∅ e | is-∅ f
... | yes _ | _     = sum (inj₂ p)
... | no _  | yes _ = sum (inj₁ p)
... | no _  | no _  = p

∣-complete : ∀ {w} e f → w ∈ (e R.∣ f) → w ∈ (e ∣ f)
∣-complete e f pr@(sum p) with is-∅ e | is-∅ f
... | yes refl | _        = fromInj₂ (λ p → contradiction p ∉∅) p
... | no _     | yes refl = fromInj₁ (λ p → contradiction p ∉∅) p
... | no _     | no _     = pr

------------------------------------------------------------------------
-- Product

infixr 6 _∙_

_∙_ : (e f : Exp) → Exp
e ∙ f with is-∅ e | is-ε e | is-∅ f | is-ε f
... | yes _ | _ | _ | _ = R.∅
... | _ | yes _ | _ | _ = f
... | _ | _ | yes _ | _ = R.∅
... | _ | _ | _ | yes _ = e
... | _ | _ | _ | _ = e R.∙ f

∙-sound : ∀ {w} e f → w ∈ (e ∙ f) → w ∈ (e R.∙ f)
∙-sound e f p with is-∅ e | is-ε e | is-∅ f | is-ε f
... | yes refl | _        | _        | _        = contradiction p ∉∅
... | no _     | yes refl | _        | _        = prod ([] ++ _) ε p
... | no _     | no _     | yes refl | _        = contradiction p ∉∅
... | no _     | no _     | no _     | yes refl = prod (_ ++[]) p ε
... | no _     | no _     | no _     | no _     = p

∙-complete : ∀ {w} e f → w ∈ (e R.∙ f) → w ∈ (e ∙ f)
∙-complete e f pr@(prod eq p q) with is-∅ e | is-ε e | is-∅ f | is-ε f
... | yes refl | _        | _        | _        = contradiction p ∉∅
... | no _     | yes refl | _        | _        = ∈ε∙e-inv pr
... | no _     | no _     | yes refl | _        = contradiction q ∉∅
... | no _     | no _     | no _     | yes refl = ∈e∙ε-inv pr
... | no _     | no _     | no _     | no _     = pr

------------------------------------------------------------------------
-- Kleene star

infix  7 _⋆

_⋆ : Exp → Exp
e ⋆ with is-∅ e | is-ε e
... | yes _ | _ = R.ε
... | _ | yes _ = R.ε
... | _ | _ = e R.⋆

⋆-sound : ∀ {w} e → w ∈ (e ⋆) → w ∈ (e R.⋆)
⋆-sound e p with is-∅ e | is-ε e
... | yes refl | _        = star (sum (inj₁ p))
... | no _     | yes refl = star (sum (inj₁ p))
... | no _     | no _     = p

⋆-complete : ∀ {w} e → w ∈ (e R.⋆) → w ∈ (e ⋆)
⋆-complete e pr with is-∅ e | is-ε e
... | yes refl | no _     = ∈∅⋆-inv pr
... | no _     | yes refl = ∈ε⋆-inv pr
... | no _     | no _     = pr

------------------------------------------------------------------------
-- Derived notions: at least one and maybe one

infixl 7 _+ _⁇
_+ : Exp → Exp
e + = e ∙ e ⋆

_⁇ : Exp → Exp
∅ ⁇ = ε
e ⁇ = ε ∣ e
