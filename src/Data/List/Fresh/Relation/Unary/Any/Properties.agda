------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Any predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.Any.Properties where

open import Level using (Level; _⊔_; Lift)
open import Data.Bool.Base using (true; false)
open import Data.Empty
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘′_)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary
open import Relation.Unary  as U using (Pred)
open import Relation.Binary as B using (Rel)
open import Relation.Nary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.List.Fresh
open import Data.List.Fresh.Relation.Unary.All
open import Data.List.Fresh.Relation.Unary.Any

private
  variable
    a b p q r s : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- NonEmpty

module _ {R : Rel A r} {P : Pred A p} where

  Any⇒NonEmpty : {xs : List# A R} → Any P xs → NonEmpty xs
  Any⇒NonEmpty {xs = cons x xs pr} p  = cons x xs pr

------------------------------------------------------------------------
-- Correspondence between Any and All

module _ {R : Rel A r} {P : Pred A p} {Q : Pred A q} (P⇒¬Q : ∀[ P ⇒ ∁ Q ]) where

  Any⇒¬All : {xs : List# A R} → Any P xs → ¬ (All Q xs)
  Any⇒¬All (here p)   (q ∷ _)  = P⇒¬Q p q
  Any⇒¬All (there ps) (_ ∷ qs) = Any⇒¬All ps qs

  All⇒¬Any : {xs : List# A R} → All P xs → ¬ (Any Q xs)
  All⇒¬Any (p ∷ _)  (here q)   = P⇒¬Q p q
  All⇒¬Any (_ ∷ ps) (there qs) = All⇒¬Any ps qs

module _ {R : Rel A r} {P : Pred A p} {Q : Pred A q} (P? : Decidable P) where

  ¬All⇒Any : {xs : List# A R} → ¬ (All P xs) → Any (∁ P) xs
  ¬All⇒Any {xs = []}      ¬ps = ⊥-elim (¬ps [])
  ¬All⇒Any {xs = x ∷# xs} ¬ps with P? x
  ... |  true because  [p] = there (¬All⇒Any (¬ps ∘′ (invert [p] ∷_)))
  ... | false because [¬p] = here (invert [¬p])

  ¬Any⇒All : {xs : List# A R} → ¬ (Any P xs) → All (∁ P) xs
  ¬Any⇒All {xs = []}      ¬ps = []
  ¬Any⇒All {xs = x ∷# xs} ¬ps with P? x
  ... |  true because  [p] = ⊥-elim (¬ps (here (invert [p])))
  ... | false because [¬p] = invert [¬p] ∷ ¬Any⇒All (¬ps ∘′ there)

------------------------------------------------------------------------
-- remove

module _ {R : Rel A r} {P : Pred A p} where

  length-remove : {xs : List# A R} (k : Any P xs) →
    length xs ≡ suc (length (xs ─ k))
  length-remove (here _)  = refl
  length-remove (there p) = cong suc (length-remove p)

------------------------------------------------------------------------
-- append

module _ {R : Rel A r} {P : Pred A p} where

  append⁺ˡ : {xs ys : List# A R} {ps : All (_# ys) xs} →
             Any P xs → Any P (append xs ys ps)
  append⁺ˡ (here px) = here px
  append⁺ˡ (there p) = there (append⁺ˡ p)

  append⁺ʳ : {xs ys : List# A R} {ps : All (_# ys) xs} →
             Any P ys → Any P (append xs ys ps)
  append⁺ʳ {xs = []}      p = p
  append⁺ʳ {xs = x ∷# xs} p = there (append⁺ʳ p)

  append⁻ : ∀ xs {ys : List# A R} {ps : All (_# ys) xs} →
            Any P (append xs ys ps) → Any P xs ⊎ Any P ys
  append⁻ []        p         = inj₂ p
  append⁻ (x ∷# xs) (here px) = inj₁ (here px)
  append⁻ (x ∷# xs) (there p) = Sum.map₁ there (append⁻ xs p)
