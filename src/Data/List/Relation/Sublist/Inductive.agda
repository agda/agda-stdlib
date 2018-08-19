------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of sublist. This commonly known as an Order
-- Preserving Embedding (OPE).
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Inductive where

open import Data.Empty
open import Data.Nat.Base
open import Data.Nat.Properties
open ≤-Reasoning
open import Data.List.Base
open import Function
import Function.Injection as F
open import Function.Equivalence as Equiv using (_⇔_ ; equivalence)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Nullary.Decidable as D

------------------------------------------------------------------------
-- Type and basic combinators

module _ {a} {A : Set a} where

  infix 3 _⊆_
  data _⊆_ : Rel (List A) a where
    base : [] ⊆ []
    skip : ∀ {xs y ys} → xs ⊆ ys → xs ⊆ (y ∷ ys)
    keep : ∀ {x xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

  infix 4 []⊆_
  []⊆_ : ∀ xs → [] ⊆ xs
  []⊆ []     = base
  []⊆ x ∷ xs = skip ([]⊆ xs)

------------------------------------------------------------------------
-- Properties of length

module _ {a} {A : Set a} where

  ⊆-length : ∀ {xs ys : List A} → xs ⊆ ys → length xs ≤ length ys
  ⊆-length base     = ≤-refl
  ⊆-length (skip p) = ≤-step (⊆-length p)
  ⊆-length (keep p) = s≤s (⊆-length p)

------------------------------------------------------------------------
-- Relational properties

module _ {a} {A : Set a} where

  ⊆-reflexive : _≡_ ⇒ _⊆_ {A = A}
  ⊆-reflexive {[]}     refl = base
  ⊆-reflexive {x ∷ xs} refl = keep (⊆-reflexive refl)

  ⊆-refl : Reflexive {A = List A} _⊆_
  ⊆-refl = ⊆-reflexive refl

  ⊆-trans : Transitive {A = List A} _⊆_
  ⊆-trans p        base     = p
  ⊆-trans p        (skip q) = skip (⊆-trans p q)
  ⊆-trans (skip p) (keep q) = skip (⊆-trans p q)
  ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)

  ⊆-antisym : Antisymmetric {A = List A} _≡_ _⊆_
  -- Positive cases
  ⊆-antisym base     base     = refl
  ⊆-antisym (keep p) (keep q) = cong (_ ∷_) (⊆-antisym p q)
  -- Dismissing the impossible cases
  ⊆-antisym {x ∷ xs} {y ∷ ys} (skip p) (skip q) = ⊥-elim $ 1+n≰n $ begin
    length (y ∷ ys) ≤⟨ ⊆-length q ⟩
    length xs       ≤⟨ n≤1+n (length xs) ⟩
    length (x ∷ xs) ≤⟨ ⊆-length p ⟩
    length ys       ∎
  ⊆-antisym {x ∷ xs} {y ∷ ys} (skip p) (keep q) = ⊥-elim $ 1+n≰n $ begin
    length (x ∷ xs) ≤⟨ ⊆-length p ⟩
    length ys       ≤⟨ ⊆-length q ⟩
    length xs       ∎
  ⊆-antisym {x ∷ xs} {y ∷ ys} (keep p) (skip q) =  ⊥-elim $ 1+n≰n $ begin
    length (y ∷ ys) ≤⟨ ⊆-length q ⟩
    length xs       ≤⟨ ⊆-length p ⟩
    length ys       ∎

  ⊆-minimum : Minimum {A = List A} _⊆_ []
  ⊆-minimum = []⊆_

module _ {a} (A : Set a) where

  ⊆-isPreorder : IsPreorder {A = List A} _≡_ _⊆_
  ⊆-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = ⊆-reflexive
    ; trans         = ⊆-trans
    }

  ⊆-preorder : Preorder _ _ _
  ⊆-preorder = record
    { isPreorder = ⊆-isPreorder
    }

  ⊆-isPartialOrder : IsPartialOrder _≡_ _⊆_
  ⊆-isPartialOrder = record
    { isPreorder = ⊆-isPreorder
    ; antisym    = ⊆-antisym
    }

  ⊆-poset : Poset _ _ _
  ⊆-poset = record
    { isPartialOrder = ⊆-isPartialOrder
    }

------------------------------------------------------------------------
-- _∷_

module _ {a} {A : Set a} where

  ∷⁻ : ∀ x {us vs : List A} → x ∷ us ⊆ x ∷ vs → us ⊆ vs
  ∷⁻ x (skip p) = ⊆-trans (skip ⊆-refl) p
  ∷⁻ x (keep p) = p

------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} where

  map⁺ : ∀ {xs ys} (f : A → B) → xs ⊆ ys → map f xs ⊆ map f ys
  map⁺ f base     = base
  map⁺ f (skip p) = skip (map⁺ f p)
  map⁺ f (keep p) = keep (map⁺ f p)

  open F.Injection

  map⁻ : ∀ {xs ys} (inj : A F.↣ B) →
         map (inj ⟨$⟩_) xs ⊆ map (inj ⟨$⟩_) ys → xs ⊆ ys
  map⁻ {[]}     {ys}     inj p = []⊆ ys
  map⁻ {x ∷ xs} {[]}     inj ()
  map⁻ {x ∷ xs} {y ∷ ys} inj p
    with inj ⟨$⟩ x | inspect (inj ⟨$⟩_) x
       | inj ⟨$⟩ y | inspect (inj ⟨$⟩_) y
       | injective inj {x} {y}
  map⁻ {x ∷ xs} {y ∷ ys} inj (skip p)
    | fx | [ eq ] | fy | _ | _ = skip (map⁻ inj (coerce p))
    where coerce = subst (λ fx → fx ∷ _ ⊆ _) (sym eq)
  map⁻ {x ∷ xs} {y ∷ ys} inj (keep p)
    | fx | _      | fx | _ | eq
    rewrite eq refl = keep (map⁻ inj p)

------------------------------------------------------------------------
-- Combinators

module _ {a} {A : Set a} where

  ++⁺ : ∀ {xs ys us vs : List A} → xs ⊆ ys → us ⊆ vs → xs ++ us ⊆ ys ++ vs
  ++⁺ base     q = q
  ++⁺ (skip p) q = skip (++⁺ p q)
  ++⁺ (keep p) q = keep (++⁺ p q)

  ++⁻ : ∀ xs {us vs : List A} → xs ++ us ⊆ xs ++ vs → us ⊆ vs
  ++⁻ []       p = p
  ++⁻ (x ∷ xs) p = ++⁻ xs (∷⁻ x p)

  skips : ∀ {xs ys} (zs : List A) → xs ⊆ ys → xs ⊆ zs ++ ys
  skips zs = ++⁺ ([]⊆ zs)

------------------------------------------------------------------------
-- Inversion lemmas

module _ {a} {A : Set a} where

  keep⁻¹ : ∀ (x : A) {xs ys} → (xs ⊆ ys) ⇔ (x ∷ xs ⊆ x ∷ ys)
  keep⁻¹ x = equivalence keep (∷⁻ x)

  skip⁻¹ : ∀ {x y : A} {xs ys} → x ≢ y → (x ∷ xs ⊆ ys) ⇔ (x ∷ xs ⊆ y ∷ ys)
  skip⁻¹ ¬eq = equivalence skip $ λ where
    (skip p) → p
    (keep p) → ⊥-elim (¬eq refl)

  ++⁻¹ : ∀ (ps : List A) {xs ys} → (xs ⊆ ys) ⇔ (ps ++ xs ⊆ ps ++ ys)
  ++⁻¹ ps = equivalence (++⁺ ⊆-refl) (++⁻ ps)

------------------------------------------------------------------------
-- Decidability of the order

module Decidable
       {a} {A : Set a} (eq? : Decidable {A = A} _≡_) where

  infix 3 _⊆?_
  _⊆?_ : Decidable {A = List A} _⊆_
  []     ⊆? ys     = yes ([]⊆ ys)
  x ∷ xs ⊆? []     = no λ ()
  x ∷ xs ⊆? y ∷ ys with eq? x y
  ... | yes refl = D.map (keep⁻¹ x) (xs ⊆? ys)
  ... | no ¬eq   = D.map (skip⁻¹ ¬eq) (x ∷ xs ⊆? ys)
