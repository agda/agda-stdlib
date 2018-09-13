------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Relation.Sublist.Inductive.Setoid.Properties
       {c ℓ} (S : Setoid c ℓ) where

open import Data.Empty
open import Data.List.Base hiding (lookup)
open import Data.List.Properties
open import Data.List.Any using (here; there)
open import Data.List.Any.Properties using (here-injective; there-injective)
open import Data.Maybe as Maybe using (nothing; just)
open import Data.Nat.Base
open import Data.Nat.Properties

open import Data.List.Membership.Setoid S
open import Data.List.Relation.Equality.Setoid S as Eq
  using (_≋_; []; _∷_; ≋-refl; ≋-isEquivalence)
import Data.List.Relation.Sublist.Inductive.Setoid as Sublist
open Sublist S


open import Function
import Function.Bijection as Bij
open import Function.Equivalence as Equiv using (_⇔_ ; equivalence)
import Function.Injection as Inj

import Algebra.FunctionProperties as FunProp

open import Relation.Nullary
import Relation.Nullary.Decidable as D
open import Relation.Unary as U using (Pred)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module S = Setoid S renaming (Carrier to A)
open S

------------------------------------------------------------------------
-- []⊆_ is irrelevant.

[]⊆-irrelevant : U.Irrelevant ([] ⊆_)
[]⊆-irrelevant base     base     = P.refl
[]⊆-irrelevant (skip p) (skip q) = P.cong skip ([]⊆-irrelevant p q)


------------------------------------------------------------------------
-- Some properties

⊆-length : ∀ {xs ys} → xs ⊆ ys → length xs ≤ length ys
⊆-length base         = ≤-refl
⊆-length (skip p)     = ≤-step (⊆-length p)
⊆-length (keep x≈y p) = s≤s (⊆-length p)

------------------------------------------------------------------------
-- Relational properties

⊆-reflexive : _≋_ ⇒ _⊆_
⊆-reflexive []            = base
⊆-reflexive (x≈y ∷ xs≈ys) = keep x≈y (⊆-reflexive xs≈ys)

⊆-refl : Reflexive _⊆_
⊆-refl = ⊆-reflexive ≋-refl

⊆-trans : Transitive _⊆_
⊆-trans p            base         = p
⊆-trans p            (skip q)     = skip (⊆-trans p q)
⊆-trans (skip p)     (keep x≈y q) = skip (⊆-trans p q)
⊆-trans (keep x≈y p) (keep y≈z q) = keep (trans x≈y y≈z) (⊆-trans p q)


⊆-antisym : Antisymmetric _≋_ _⊆_
-- Positive cases
⊆-antisym base         base         = []
⊆-antisym (keep x≈y p) (keep y≈x q) = x≈y ∷ ⊆-antisym p q
-- Dismissing the impossible cases
⊆-antisym {x ∷ xs} {y ∷ ys} (skip p) (skip q) = ⊥-elim $ 1+n≰n $ begin
  length (y ∷ ys) ≤⟨ ⊆-length q ⟩
  length xs       ≤⟨ n≤1+n (length xs) ⟩
  length (x ∷ xs) ≤⟨ ⊆-length p ⟩
  length ys       ∎ where open ≤-Reasoning
⊆-antisym {x ∷ xs} {y ∷ ys} (skip p) (keep x≈y q) = ⊥-elim $ 1+n≰n $ begin
  length (x ∷ xs) ≤⟨ ⊆-length p ⟩
  length ys       ≤⟨ ⊆-length q ⟩
  length xs       ∎ where open ≤-Reasoning
⊆-antisym {x ∷ xs} {y ∷ ys} (keep x≈y p) (skip q) =  ⊥-elim $ 1+n≰n $ begin
  length (y ∷ ys) ≤⟨ ⊆-length q ⟩
  length xs       ≤⟨ ⊆-length p ⟩
  length ys       ∎ where open ≤-Reasoning

⊆-minimum : Minimum _⊆_ []
⊆-minimum = []⊆_


⊆-isPreorder : IsPreorder _≋_ _⊆_
⊆-isPreorder = record
  { isEquivalence = ≋-isEquivalence
  ; reflexive     = ⊆-reflexive
  ; trans         = ⊆-trans
  }

⊆-preorder : Preorder _ _ _
⊆-preorder = record
  { isPreorder = ⊆-isPreorder
  }

⊆-isPartialOrder : IsPartialOrder _≋_ _⊆_
⊆-isPartialOrder = record
  { isPreorder = ⊆-isPreorder
  ; antisym    = ⊆-antisym
  }

⊆-poset : Poset _ _ _
⊆-poset = record
  { isPartialOrder = ⊆-isPartialOrder
  }

import Relation.Binary.PartialOrderReasoning as PosetReasoning
module ⊆-Reasoning where
  private module PR = PosetReasoning ⊆-poset
  open PR public renaming (_≤⟨_⟩_ to _⊆⟨_⟩_)

------------------------------------------------------------------------
-- Various functions' outputs are sublists

tail-⊆ : ∀ xs → Maybe.All (_⊆ xs) (tail xs)
tail-⊆ []       = nothing
tail-⊆ (x ∷ xs) = just (skip ⊆-refl)

take-⊆ : ∀ n xs → take n xs ⊆ xs
take-⊆ zero    xs       = []⊆ xs
take-⊆ (suc n) []       = []⊆ []
take-⊆ (suc n) (x ∷ xs) = keep refl (take-⊆ n xs)

drop-⊆ : ∀ n xs → drop n xs ⊆ xs
drop-⊆ zero    xs       = ⊆-refl
drop-⊆ (suc n) []       = []⊆ []
drop-⊆ (suc n) (x ∷ xs) = skip (drop-⊆ n xs)

module _ {p} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-⊆ : ∀ xs → takeWhile P? xs ⊆ xs
  takeWhile-⊆ []       = []⊆ []
  takeWhile-⊆ (x ∷ xs) with P? x
  ... | yes p = keep refl (takeWhile-⊆ xs)
  ... | no ¬p = []⊆ x ∷ xs

  dropWhile-⊆ : ∀ xs → dropWhile P? xs ⊆ xs
  dropWhile-⊆ []       = []⊆ []
  dropWhile-⊆ (x ∷ xs) with P? x
  ... | yes p = skip (dropWhile-⊆ xs)
  ... | no ¬p = ⊆-refl

  filter-⊆ : ∀ xs → filter P? xs ⊆ xs
  filter-⊆ []       = []⊆ []
  filter-⊆ (x ∷ xs) with P? x
  ... | yes p = keep refl (filter-⊆ xs)
  ... | no ¬p = skip (filter-⊆ xs)

------------------------------------------------------------------------
-- Various functions are increasing wrt _⊆_


------------------------------------------------------------------------
-- _∷_

∷⁻ : ∀ {x y xs ys} → x ≈ y → x ∷ xs ⊆ y ∷ ys → xs ⊆ ys
∷⁻ x≈y (skip p)      = ⊆-trans (skip ⊆-refl) p
∷⁻ x≈y (keep x≈y′ p) = p

-- map

module _ {d ℓ′} (T : Setoid d ℓ′) where

  open Setoid T renaming (Carrier to B; _≈_ to _≈′_)
  module T = Sublist T

  map⁺ : ∀ {f xs ys} → f Preserves _≈_ ⟶ _≈′_ →
         xs ⊆ ys → map f xs T.⊆ map f ys
  map⁺ f base         = T.base
  map⁺ f (skip p)     = T.skip (map⁺ f p)
  map⁺ f (keep x≈y p) = T.keep (f x≈y) (map⁺ f p)

  open Inj.Injection

  map⁻ : ∀ {xs ys} (inj : Inj.Injection S T) →
         map (inj ⟨$⟩_) xs T.⊆ map (inj ⟨$⟩_) ys → xs ⊆ ys
  map⁻ {[]}     {ys}     inj p = []⊆ ys
  map⁻ {x ∷ xs} {[]}     inj ()
  map⁻ {x ∷ xs} {y ∷ ys} inj p
    with inj ⟨$⟩ x | P.inspect (inj ⟨$⟩_) x
       | inj ⟨$⟩ y | P.inspect (inj ⟨$⟩_) y
       | injective inj {x} {y}
  map⁻ {x ∷ xs} {y ∷ ys} inj (skip p)
    | fx | P.[ eq ] | fy | _ | _ = skip (map⁻ inj (coerce p))
    where coerce = P.subst (λ fx → fx ∷ _ T.⊆ _) (P.sym eq)
  map⁻ {x ∷ xs} {y ∷ ys} inj (keep x≈y p)
    | fx | _      | fy | _ | eq = keep (eq x≈y) (map⁻ inj p)

-- _++_

++⁺ : ∀ {xs ys us vs} → xs ⊆ ys → us ⊆ vs → xs ++ us ⊆ ys ++ vs
++⁺ base         q = q
++⁺ (skip p)     q = skip (++⁺ p q)
++⁺ (keep x≈y p) q = keep x≈y (++⁺ p q)

++⁻ : ∀ xs {us vs} → xs ++ us ⊆ xs ++ vs → us ⊆ vs
++⁻ []       p = p
++⁻ (x ∷ xs) p = ++⁻ xs (∷⁻ refl p)

skips : ∀ {xs ys} zs → xs ⊆ ys → xs ⊆ zs ++ ys
skips zs = ++⁺ ([]⊆ zs)

-- take / drop

≤-take-⊆ : ∀ {m n} → m ≤ n → ∀ xs → take m xs ⊆ take n xs
≤-take-⊆ z≤n     xs       = []⊆ take _ xs
≤-take-⊆ (s≤s p) []       = []⊆ []
≤-take-⊆ (s≤s p) (x ∷ xs) = keep refl (≤-take-⊆ p xs)

≥-drop-⊆ : ∀ {m n} → m ≥ n → ∀ xs → drop m xs ⊆ drop n xs
≥-drop-⊆ {m} z≤n     xs       = drop-⊆ m xs
≥-drop-⊆     (s≤s p) []       = []⊆ []
≥-drop-⊆     (s≤s p) (x ∷ xs) = ≥-drop-⊆ p xs

drop⁺ : ∀ n {xs ys : List A} → xs ⊆ ys → drop n xs ⊆ drop n ys
drop⁺ zero    p            = p
drop⁺ (suc n) base         = []⊆ []
drop⁺ (suc n) (keep x≈y p) = drop⁺ n p
drop⁺ (suc n) {xs} {y ∷ ys} (skip p) = begin
  drop (suc n) xs ⊆⟨ ≥-drop-⊆ (n≤1+n n) xs ⟩
  drop n xs       ⊆⟨ drop⁺ n p ⟩
  drop n ys       ∎ where open ⊆-Reasoning

module _ {p q} {P : Pred A p} {Q : Pred A q}
         (P? : U.Decidable P) (Q? : U.Decidable Q) where

  ⊆-takeWhile-⊆ : (P U.⊆ Q) → ∀ xs → takeWhile P? xs ⊆ takeWhile Q? xs
  ⊆-takeWhile-⊆ P⊆Q []       = []⊆ []
  ⊆-takeWhile-⊆ P⊆Q (x ∷ xs) with P? x | Q? x
  ... | yes px | yes qx = keep refl (⊆-takeWhile-⊆ P⊆Q xs)
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
  ... | yes px | yes qx = keep refl (⊆-filter-⊆ P⊆Q xs)
  ... | yes px | no ¬qx = ⊥-elim $ ¬qx (P⊆Q px)
  ... | no ¬px | yes qx = skip (⊆-filter-⊆ P⊆Q xs)
  ... | no ¬px | no ¬qx = ⊆-filter-⊆ P⊆Q xs

module _ {p} {P : Pred A p} (P? : U.Decidable P) (P≈ : P Respects _≈_) where

  filter⁺ : ∀ {xs ys} → xs ⊆ ys → filter P? xs ⊆ filter P? ys
  filter⁺                   base     = base
  filter⁺ {xs}     {y ∷ ys} (skip p) with P? y
  ... | yes py = skip (filter⁺ p)
  ... | no ¬py = filter⁺ p
  filter⁺ {x ∷ xs} {y ∷ ys} (keep x≈y p) with P? x | P? y
  ... | yes px | yes py = keep x≈y (filter⁺ p)
  ... | no ¬px | no ¬py = filter⁺ p
  ... | yes px | no ¬py = ⊥-elim $ ¬py (P≈ x≈y px)
  ... | no ¬px | yes py = ⊥-elim $ ¬px (P≈ (sym x≈y) py)

-- reverse

reverseAcc⁺ : ∀ {us vs xs ys} → us ⊆ vs → xs ⊆ ys → reverseAcc us xs ⊆ reverseAcc vs ys
reverseAcc⁺ acc base         = acc
reverseAcc⁺ acc (skip p)     = reverseAcc⁺ (skip acc) p
reverseAcc⁺ acc (keep x≈y p) = reverseAcc⁺ (keep x≈y acc) p

reverse⁺ : ∀ {xs ys} → xs ⊆ ys → reverse xs ⊆ reverse ys
reverse⁺ = reverseAcc⁺ base

reverse⁻ : ∀ {xs ys} → reverse xs ⊆ reverse ys → xs ⊆ ys
reverse⁻ {xs} {ys} p = cast (reverse⁺ p) where
  cast = P.subst₂ _⊆_ (reverse-involutive xs) (reverse-involutive ys)

------------------------------------------------------------------------
-- Inversion lemmas

keep⁻¹ : ∀ {x y xs ys} → x ≈ y → (xs ⊆ ys) ⇔ (x ∷ xs ⊆ y ∷ ys)
keep⁻¹ eq = equivalence (keep eq) (∷⁻ eq)

skip⁻¹ : ∀ {x y xs ys} → ¬ (x ≈ y) → (x ∷ xs ⊆ ys) ⇔ (x ∷ xs ⊆ y ∷ ys)
skip⁻¹ ¬eq = equivalence skip $ λ where
  (skip p)     → p
  (keep x≈y p) → ⊥-elim (¬eq x≈y)

++⁻¹ : ∀ ps {xs ys} → (xs ⊆ ys) ⇔ (ps ++ xs ⊆ ps ++ ys)
++⁻¹ ps = equivalence (++⁺ ⊆-refl) (++⁻ ps)

------------------------------------------------------------------------
-- Decidability of the order

module Decidable (eq? : Decidable _≈_) where

  infix 3 _⊆?_
  _⊆?_ : Decidable _⊆_
  []     ⊆? ys     = yes ([]⊆ ys)
  x ∷ xs ⊆? []     = no λ ()
  x ∷ xs ⊆? y ∷ ys with eq? x y
  ... | yes x≈y = D.map (keep⁻¹ x≈y) (xs ⊆? ys)
  ... | no ¬x≈y = D.map (skip⁻¹ ¬x≈y) (x ∷ xs ⊆? ys)
