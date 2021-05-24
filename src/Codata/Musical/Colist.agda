------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

-- Disabled to prevent warnings from BoundedVec
{-# OPTIONS --warn=noUserWarning #-}

module Codata.Musical.Colist where

open import Level using (Level)
open import Category.Monad
open import Codata.Musical.Notation
open import Codata.Musical.Conat using (Coℕ; zero; suc)
import Codata.Musical.Colist.Properties
import Codata.Musical.Colist.Relation.Unary.All.Properties
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; nothing; just; Is-just)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Data.Nat.Base using (ℕ; zero; suc; _≥′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (s≤′s)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec.Bounded as Vec≤ using (Vec≤)
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; _↔̇_; Inverse; inverse)
open import Level using (_⊔_)
open import Relation.Binary
import Relation.Binary.Construct.FromRel as Ind
import Relation.Binary.Reasoning.Preorder as PreR
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary using (Pred)

private
  variable
    a b p : Level
    A : Set a
    B : Set b
    P : Pred A p

------------------------------------------------------------------------
-- Re-export type and basic definitions

open import Codata.Musical.Colist.Base public
module Colist-injective = Codata.Musical.Colist.Properties
open import Codata.Musical.Colist.Bisimilarity public
open import Codata.Musical.Colist.Relation.Unary.All public
module All-injective = Codata.Musical.Colist.Relation.Unary.All.Properties
open import Codata.Musical.Colist.Relation.Unary.Any public
open import Codata.Musical.Colist.Relation.Unary.Any.Properties public

------------------------------------------------------------------------
-- More operations

take : ∀ {a} {A : Set a} (n : ℕ) → Colist A → Vec≤ A n
take zero    xs       = Vec≤.[]
take (suc n) []       = Vec≤.[]
take (suc n) (x ∷ xs) = x Vec≤.∷ take n (♭ xs)


module ¬¬Monad {p} where
  open RawMonad (¬¬-Monad {p}) public
open ¬¬Monad  -- we don't want the RawMonad content to be opened publicly

------------------------------------------------------------------------
-- Memberships, subsets, prefixes

-- x ∈ xs means that x is a member of xs.

infix 4 _∈_

_∈_ : {A : Set a} → A → Colist A → Set a
x ∈ xs = Any (_≡_ x) xs

-- xs ⊆ ys means that xs is a subset of ys.

infix 4 _⊆_

_⊆_ : {A : Set a} → Rel (Colist A) a
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

-- xs ⊑ ys means that xs is a prefix of ys.

infix 4 _⊑_

data _⊑_ {A : Set a} : Rel (Colist A) a where
  []  : ∀ {ys}                            → []     ⊑ ys
  _∷_ : ∀ x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) → x ∷ xs ⊑ x ∷ ys

-- Any can be expressed using _∈_ (and vice versa).

Any-∈ : ∀ {xs} → Any P xs ↔ ∃ λ x → x ∈ xs × P x
Any-∈ {P = P} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ (λ { (x , x∈xs , p) → from x∈xs p })
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = λ { (x , x∈xs , p) → to∘from x∈xs p }
    }
  }
  where
  to : ∀ {xs} → Any P xs → ∃ λ x → x ∈ xs × P x
  to (here  p) = _ , here P.refl , p
  to (there p) = Prod.map id (Prod.map there id) (to p)

  from : ∀ {x xs} → x ∈ xs → P x → Any P xs
  from (here P.refl) p = here p
  from (there x∈xs)  p = there (from x∈xs p)

  to∘from : ∀ {x xs} (x∈xs : x ∈ xs) (p : P x) →
            to (from x∈xs p) ≡ (x , x∈xs , p)
  to∘from (here P.refl) p = P.refl
  to∘from (there x∈xs)  p =
    P.cong (Prod.map id (Prod.map there id)) (to∘from x∈xs p)

  from∘to : ∀ {xs} (p : Any P xs) →
            let (x , x∈xs , px) = to p in from x∈xs px ≡ p
  from∘to (here _)  = P.refl
  from∘to (there p) = P.cong there (from∘to p)

-- Prefixes are subsets.

⊑⇒⊆ : _⊑_ {A = A} ⇒ _⊆_
⊑⇒⊆ (x ∷ xs⊑ys) (here ≡x)    = here ≡x
⊑⇒⊆ (_ ∷ xs⊑ys) (there x∈xs) = there (⊑⇒⊆ (♭ xs⊑ys) x∈xs)

-- The prefix relation forms a poset.

⊑-Poset : ∀ {ℓ} → Set ℓ → Poset _ _ _
⊑-Poset A = record
  { Carrier        = Colist A
  ; _≈_            = _≈_
  ; _≤_            = _⊑_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Setoid.isEquivalence (setoid A)
      ; reflexive     = reflexive
      ; trans         = trans
      }
    ; antisym  = antisym
    }
  }
  where
  reflexive : _≈_ ⇒ _⊑_
  reflexive []        = []
  reflexive (x ∷ xs≈) = x ∷ ♯ reflexive (♭ xs≈)

  trans : Transitive _⊑_
  trans []        _          = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

  tail : ∀ {x xs y ys} → x ∷ xs ⊑ y ∷ ys → ♭ xs ⊑ ♭ ys
  tail (_ ∷ p) = ♭ p

  antisym : Antisymmetric _≈_ _⊑_
  antisym []       [] = []
  antisym (x ∷ p₁) p₂ = x ∷ ♯ antisym (♭ p₁) (tail p₂)

module ⊑-Reasoning {a} {A : Set a} where
  private module Base = POR (⊑-Poset A)

  open Base public
    hiding (step-<; begin-strict_; step-≤)

  infixr 2 step-⊑
  step-⊑ = Base.step-≤
  syntax step-⊑ x ys⊑zs xs⊑ys = x ⊑⟨ xs⊑ys ⟩ ys⊑zs

-- The subset relation forms a preorder.

⊆-Preorder : ∀ {ℓ} → Set ℓ → Preorder _ _ _
⊆-Preorder A = Ind.preorder (setoid A) _∈_
                 (λ xs≈ys → ⊑⇒⊆ (⊑P.reflexive xs≈ys))
  where module ⊑P = Poset (⊑-Poset A)

module ⊆-Reasoning {A : Set a} where
  private module Base = PreR (⊆-Preorder A)

  open Base public
    hiding (step-∼)

  infixr 2 step-⊆
  infix  1 step-∈

  step-⊆ = Base.step-∼

  step-∈ : ∀ (x : A) {xs ys} → xs IsRelatedTo ys → x ∈ xs → x ∈ ys
  step-∈ x xs⊆ys x∈xs = (begin xs⊆ys) x∈xs

  syntax step-⊆ xs ys⊆zs xs⊆ys = xs ⊆⟨ xs⊆ys ⟩ ys⊆zs
  syntax step-∈ x  xs⊆ys x∈xs  = x  ∈⟨ x∈xs  ⟩ xs⊆ys

-- take returns a prefix.
take-⊑ : ∀ n (xs : Colist A) →
         let toColist = fromList {a} ∘ Vec≤.toList in
         toColist (take n xs) ⊑ xs
take-⊑ zero    xs       = []
take-⊑ (suc n) []       = []
take-⊑ (suc n) (x ∷ xs) = x ∷ ♯ take-⊑ n (♭ xs)

------------------------------------------------------------------------
-- Finiteness and infiniteness

-- Finite xs means that xs has finite length.

data Finite {A : Set a} : Colist A → Set a where
  []  : Finite []
  _∷_ : ∀ x {xs} (fin : Finite (♭ xs)) → Finite (x ∷ xs)

module Finite-injective where

 ∷-injective : ∀ {x : A} {xs p q} → (Finite (x ∷ xs) ∋ x ∷ p) ≡ x ∷ q → p ≡ q
 ∷-injective P.refl = P.refl

-- Infinite xs means that xs has infinite length.

data Infinite {A : Set a} : Colist A → Set a where
  _∷_ : ∀ x {xs} (inf : ∞ (Infinite (♭ xs))) → Infinite (x ∷ xs)

module Infinite-injective where

 ∷-injective : ∀ {x : A} {xs p q} → (Infinite (x ∷ xs) ∋ x ∷ p) ≡ x ∷ q → p ≡ q
 ∷-injective P.refl = P.refl

-- Colists which are not finite are infinite.

not-finite-is-infinite :
  (xs : Colist A) → ¬ Finite xs → Infinite xs
not-finite-is-infinite []       hyp = contradiction [] hyp
not-finite-is-infinite (x ∷ xs) hyp =
  x ∷ ♯ not-finite-is-infinite (♭ xs) (hyp ∘ _∷_ x)

-- Colists are either finite or infinite (classically).

finite-or-infinite :
  (xs : Colist A) → ¬ ¬ (Finite xs ⊎ Infinite xs)
finite-or-infinite xs = helper <$> excluded-middle
  where
  helper : Dec (Finite xs) → Finite xs ⊎ Infinite xs
  helper ( true because  [fin]) = inj₁ (invert [fin])
  helper (false because [¬fin]) =
    inj₂ $ not-finite-is-infinite xs (invert [¬fin])

-- Colists are not both finite and infinite.

not-finite-and-infinite :
  ∀ {xs : Colist A} → Finite xs → Infinite xs → ⊥
not-finite-and-infinite (x ∷ fin) (.x ∷ inf) =
  not-finite-and-infinite fin (♭ inf)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.3

open import Data.BoundedVec.Inefficient as BVec
  using (BoundedVec; []; _∷_)

take′ : (n : ℕ) → Colist A → BoundedVec A n
take′ zero    xs       = []
take′ (suc n) []       = []
take′ (suc n) (x ∷ xs) = x ∷ take′ n (♭ xs)
{-# WARNING_ON_USAGE take′
"Warning: take′ (and Data.BoundedVec) was deprecated in v1.3.
Please use take (and Data.Vec.Bounded) instead."
#-}

take′-⊑ : ∀ n (xs : Colist A) →
         let toColist = fromList {a} ∘ BVec.toList in
         toColist (take′ n xs) ⊑ xs
take′-⊑ zero    xs       = []
take′-⊑ (suc n) []       = []
take′-⊑ (suc n) (x ∷ xs) = x ∷ ♯ take′-⊑ n (♭ xs)
{-# WARNING_ON_USAGE take′-⊑
"Warning: take′-⊑ (and Data.BoundedVec) was deprecated in v1.3.
Please use take-⊑ (and Data.Vec.Bounded) instead."
#-}
