------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Inductive.Properties where

open import Data.Empty
open import Data.List.Base hiding (lookup)
open import Data.List.Properties
open import Data.List.Any using (here; there)
open import Data.List.Any.Properties using (here-injective; there-injective)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Sublist.Inductive
open import Data.Maybe as Maybe using (nothing; just)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Function
import Function.Injection as F
open import Relation.Nullary
open import Relation.Unary as U using (Pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- The `loookup` function induced by a proof that `xs ⊆ ys` is injective

module _ {a} {A : Set a} {x : A} where

  lookup-injective : ∀ {xs ys} {p : xs ⊆ ys} {v w : x ∈ xs} →
                     lookup p v ≡ lookup p w → v ≡ w
  lookup-injective {p = skip p} {v} {w} eq =
    lookup-injective (there-injective eq)
  lookup-injective {p = keep p} {here px} {here qx} eq =
    cong here (≡-irrelevance _ _)
  lookup-injective {p = keep p} {there v} {there w} eq =
    cong there (lookup-injective (there-injective eq))
  -- impossible cases
  lookup-injective {p = keep p} {here px} {there w} ()
  lookup-injective {p = keep p} {there v} {here qx} ()
  lookup-injective {p = base} {}

------------------------------------------------------------------------
-- Some properties

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

  open ≤-Reasoning

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

  ⊆-minimum : Minimum (_⊆_ {A = A}) []
  ⊆-minimum = []⊆_

module _ {a} (A : Set a) where

  ⊆-isPreorder : IsPreorder _≡_ (_⊆_ {A = A})
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

import Relation.Binary.PartialOrderReasoning as PosetReasoning
module ⊆-Reasoning {a} {A : Set a}  where
  private module P = PosetReasoning (⊆-poset A)
  open P public
    renaming (_≤⟨_⟩_ to _⊆⟨_⟩_; _≈⟨⟩_ to _≡⟨⟩_)
    hiding (_≈⟨_⟩_)


------------------------------------------------------------------------
-- Various functions' outputs are sublists

module _ {a} {A : Set a} where

  tail-⊆ : (xs : List A) → Maybe.All (_⊆ xs) (tail xs)
  tail-⊆ []       = nothing
  tail-⊆ (x ∷ xs) = just (skip ⊆-refl)

  take-⊆ : ∀ n (xs : List A) → take n xs ⊆ xs
  take-⊆ zero    xs       = []⊆ xs
  take-⊆ (suc n) []       = []⊆ []
  take-⊆ (suc n) (x ∷ xs) = keep (take-⊆ n xs)

  drop-⊆ : ∀ n (xs : List A) → drop n xs ⊆ xs
  drop-⊆ zero    xs       = ⊆-refl
  drop-⊆ (suc n) []       = []⊆ []
  drop-⊆ (suc n) (x ∷ xs) = skip (drop-⊆ n xs)

module _ {a p} {A : Set a} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-⊆ : ∀ xs → takeWhile P? xs ⊆ xs
  takeWhile-⊆ []       = []⊆ []
  takeWhile-⊆ (x ∷ xs) with P? x
  ... | yes p = keep (takeWhile-⊆ xs)
  ... | no ¬p = []⊆ x ∷ xs

  dropWhile-⊆ : ∀ xs → dropWhile P? xs ⊆ xs
  dropWhile-⊆ []       = []⊆ []
  dropWhile-⊆ (x ∷ xs) with P? x
  ... | yes p = skip (dropWhile-⊆ xs)
  ... | no ¬p = ⊆-refl

  filter-⊆ : ∀ xs → filter P? xs ⊆ xs
  filter-⊆ []       = []⊆ []
  filter-⊆ (x ∷ xs) with P? x
  ... | yes p = keep (filter-⊆ xs)
  ... | no ¬p = skip (filter-⊆ xs)

------------------------------------------------------------------------
-- Various functions are increasing wrt _⊆_

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

-- _++_

module _ {a} {A : Set a} where

  ++⁺ : ∀ {xs ys us vs : List A} → xs ⊆ ys → us ⊆ vs → xs ++ us ⊆ ys ++ vs
  ++⁺ base     q = q
  ++⁺ (skip p) q = skip (++⁺ p q)
  ++⁺ (keep p) q = keep (++⁺ p q)

-- take / drop

  ≤-take-⊆ : ∀ {m n} → m ≤ n → (xs : List A) → take m xs ⊆ take n xs
  ≤-take-⊆ z≤n     xs       = []⊆ take _ xs
  ≤-take-⊆ (s≤s p) []       = []⊆ []
  ≤-take-⊆ (s≤s p) (x ∷ xs) = keep (≤-take-⊆ p xs)

  ≥-drop-⊆ : ∀ {m n} → m ≥ n → (xs : List A) → drop m xs ⊆ drop n xs
  ≥-drop-⊆ {m} z≤n     xs       = drop-⊆ m xs
  ≥-drop-⊆     (s≤s p) []       = []⊆ []
  ≥-drop-⊆     (s≤s p) (x ∷ xs) = ≥-drop-⊆ p xs

  drop⁺ : ∀ n {xs ys : List A} → xs ⊆ ys → drop n xs ⊆ drop n ys
  drop⁺ zero    p        = p
  drop⁺ (suc n) base     = []⊆ []
  drop⁺ (suc n) (keep p) = drop⁺ n p
  drop⁺ (suc n) {xs} {y ∷ ys} (skip p) = begin
    drop (suc n) xs ⊆⟨ ≥-drop-⊆ (n≤1+n n) xs ⟩
    drop n xs       ⊆⟨ drop⁺ n p ⟩
    drop n ys       ∎ where open ⊆-Reasoning

module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q}
         (P? : U.Decidable P) (Q? : U.Decidable Q) where

  ⊆-takeWhile-⊆ : (P U.⊆ Q) → ∀ xs → takeWhile P? xs ⊆ takeWhile Q? xs
  ⊆-takeWhile-⊆ P⊆Q []       = []⊆ []
  ⊆-takeWhile-⊆ P⊆Q (x ∷ xs) with P? x | Q? x
  ... | yes px | yes qx = keep (⊆-takeWhile-⊆ P⊆Q xs)
  ... | yes px | no ¬qx = ⊥-elim $ ¬qx (P⊆Q px)
  ... | no ¬px | _      = []⊆ _

  ⊇-dropWhile-⊆ : (P U.⊇ Q) → ∀ xs → dropWhile P? xs ⊆ dropWhile Q? xs
  ⊇-dropWhile-⊆ P⊇Q []       = []⊆ []
  ⊇-dropWhile-⊆ P⊇Q (x ∷ xs) with P? x | Q? x
  ... | yes px | yes qx = ⊇-dropWhile-⊆ P⊇Q xs
  ... | yes px | no ¬qx = skip (dropWhile-⊆ P? xs)
  ... | no ¬px | yes qx = ⊥-elim $ ¬px (P⊇Q qx)
  ... | no ¬px | no ¬qx = ⊆-refl

-- filter

  ⊆-filter-⊆ : (P U.⊆ Q) → ∀ xs → filter P? xs ⊆ filter Q? xs
  ⊆-filter-⊆ P⊆Q []       = []⊆ []
  ⊆-filter-⊆ P⊆Q (x ∷ xs) with P? x | Q? x
  ... | yes px | yes qx = keep (⊆-filter-⊆ P⊆Q xs)
  ... | yes px | no ¬qx = ⊥-elim $ ¬qx (P⊆Q px)
  ... | no ¬px | yes qx = skip (⊆-filter-⊆ P⊆Q xs)
  ... | no ¬px | no ¬qx = ⊆-filter-⊆ P⊆Q xs

module _ {a p} {A : Set a} {P : Pred A p} (P? : U.Decidable P) where

  filter⁺ : ∀ {xs ys : List A} → xs ⊆ ys → filter P? xs ⊆ filter P? ys
  filter⁺                   base     = base
  filter⁺ {xs}     {y ∷ ys} (skip p) with P? y
  ... | yes py = skip (filter⁺ p)
  ... | no ¬py = filter⁺ p
  filter⁺ {x ∷ xs} {x ∷ ys} (keep p) with P? x
  ... | yes px = keep (filter⁺ p)
  ... | no ¬px = filter⁺ p

-- reverse

module _ {a} {A : Set a} where

  open ⊆-Reasoning

  reverse⁺ : {xs ys : List A} → xs ⊆ ys → reverse xs ⊆ reverse ys
  reverse⁺ base = []⊆ []
  reverse⁺ {xs} {y ∷ ys} (skip p) = begin
    reverse xs       ≡⟨ sym $ ++-identityʳ _ ⟩
    reverse xs ++ [] ⊆⟨ ++⁺ (reverse⁺ p) ([]⊆ _) ⟩
    reverse ys ∷ʳ y  ≡⟨ sym $ unfold-reverse y ys ⟩
    reverse (y ∷ ys) ∎
  reverse⁺ {x ∷ xs} {x ∷ ys} (keep p) = begin
    reverse (x ∷ xs) ≡⟨ unfold-reverse x xs ⟩
    reverse xs ∷ʳ x  ⊆⟨ ++⁺ (reverse⁺ p) ⊆-refl ⟩
    reverse ys ∷ʳ x  ≡⟨ sym $ unfold-reverse x ys ⟩
    reverse (x ∷ ys) ∎

  reverse⁻ : {xs ys : List A} → reverse xs ⊆ reverse ys → xs ⊆ ys
  reverse⁻ {xs} {ys} p = cast (reverse⁺ p) where
    cast = subst₂ _⊆_ (reverse-involutive xs) (reverse-involutive ys)
