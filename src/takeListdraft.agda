-- List-related properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-} -- for deprecated scans

module takeListdraft where

open import Algebra.Bundles using (Semigroup; Monoid)
open import Algebra.Consequences.Propositional
 using (selfInverse⇒involutive; selfInverse⇒injective)
open import Algebra.Definitions as AlgebraicDefinitions using (SelfInverse; Involutive)
open import Algebra.Morphism.Structures using (IsMagmaHomomorphism; IsMonoidHomomorphism)
import Algebra.Structures as AlgebraicStructures
open import Data.Bool.Base using (Bool; false; true; not; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; cast; toℕ)
open import Data.List.Base as List
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.Any using (just) renaming (Any to MAny)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base as Product
  using (_×_; _,_; uncurry; uncurry′; proj₁; proj₂; <_,_>)
import Data.Product.Relation.Unary.All as Product using (All)
open import Data.Sum using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.These.Base as These using (These; this; that; these)
open import Data.Fin.Properties using (toℕ-cast)
open import Function.Base using (id; _∘_; _∘′_; _∋_; _-⟨_∣; ∣_⟩-_; _$_; const; flip)
open import Function.Definitions using (Injective)
open import Level using (Level)
open import Relation.Binary.Definitions as B using (DecidableEquality)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no; _because_; does)
open import Relation.Nullary.Negation.Core using (contradiction; ¬_)
open import Relation.Nullary.Decidable as Decidable
  using (isYes; map′; ⌊_⌋; ¬?; _×-dec_; dec-true; dec-false)
open import Relation.Unary using (Pred; Decidable; ∁; _≐_)
open import Relation.Unary.Properties using (∁?)
import Data.Nat.GeneralisedArithmetic as ℕ

open import Data.List.Properties using (++-identity)

open ≡-Reasoning

private
  variable
    a b c d e p q ℓ : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e
    x y z w : A
    xs ys zs ws : List A

------------------------------------------------------------------------
-- Take++ : When you append 2 lists together and then take the length of the first list, you get the first list back
take-++ : (n : ℕ) (xs ys : List A) → n ≤ length xs → take n (xs ++ ys) ≡ take n xs
take-++ zero xs ys n≤len = refl
take-++ (suc n) [] ys () 
take-++ (suc n) (x ∷ xs) ys (s≤s n≤len) = cong (x ∷_) (take-++ n xs ys n≤len)

-- Take++₁ : When you append 2 lists together and then take more than the length of the first list, you get the first list back and some of the second list
-- lemma : 
lengthxs : {A : Set} {n : ℕ} (x : A) (xs : List A) → ((suc n) ≡ length (x ∷ xs)) → (n ≡ length xs)
lengthxs {A} {n} x xs sucn=len = 
  begin
    n
  ≡⟨ cong pred sucn=len ⟩
    pred (length (x ∷ xs))
  ≡⟨ refl ⟩
    length xs
  ∎

take-++₁ : {A : Set} {n i : ℕ} (xs ys : List A) → (n ≡ length xs) → take (n + i) (xs ++ ys) ≡ xs ++ take i ys
take-++₁ {A} {n = zero} {i} [] ys n=len = refl
take-++₁ {A} {n = suc n} {i} (x ∷ xs) ys sucn=len =
  begin
    x ∷ take (n + i) (xs ++ ys) 
  ≡⟨ cong (x ∷_) (take-++₁ xs ys (lengthxs x xs sucn=len)) ⟩
    x ∷ (xs ++ take i ys)
  ≡⟨ refl ⟩
    (x ∷ xs) ++ take i ys
  ∎













