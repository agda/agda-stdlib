------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the Any predicate on colists
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Codata.Musical.Colist.Relation.Unary.Any.Properties where

open import Codata.Musical.Colist.Base
open import Codata.Musical.Colist.Bisimilarity
open import Codata.Musical.Colist.Relation.Unary.Any
open import Codata.Musical.Notation
open import Data.Maybe using (Is-just)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Data.Nat.Base using (suc; _≥′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (s≤′s)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′; [_,_])
open import Function.Base using (_∋_; _∘_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; _↔̇_; Inverse; inverse)
open import Level using (Level; _⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; cong)
open import Relation.Unary using (Pred)

private
  variable
    a b p q : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred A q

------------------------------------------------------------------------
-- Equality properties

here-injective : ∀ {x xs p q} → (Any P (x ∷ xs) ∋ here p) ≡ here q → p ≡ q
here-injective refl = refl

there-injective : ∀ {x xs p q} → (Any P (x ∷ xs) ∋ there p) ≡ there q → p ≡ q
there-injective refl = refl

Any-resp : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
           {xs ys} → (∀ {x} → P x → Q x) → xs ≈ ys →
           Any P xs → Any Q ys
Any-resp f (x ∷ xs≈) (here px) = here (f px)
Any-resp f (x ∷ xs≈) (there p) = there (Any-resp f (♭ xs≈) p)

-- Any maps pointwise isomorphic predicates and equal colists to
-- isomorphic types.

Any-cong : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
           {xs ys} → P ↔̇ Q → xs ≈ ys → Any P xs ↔ Any Q ys
Any-cong {A = A} {P} {Q} {xs} {ys} P↔Q = λ xs≈ys → record
  { to         = P.→-to-⟶ (to xs≈ys)
  ; from       = P.→-to-⟶ (from xs≈ys)
  ; inverse-of = record
    { left-inverse-of  = from∘to _
    ; right-inverse-of = to∘from _
    }
  }
  where
  open Setoid (setoid _) using (sym)

  to : ∀ {xs ys} → xs ≈ ys → Any P xs → Any Q ys
  to xs≈ys = Any-resp (Inverse.to P↔Q ⟨$⟩_) xs≈ys

  from : ∀ {xs ys} → xs ≈ ys → Any Q ys → Any P xs
  from xs≈ys = Any-resp (Inverse.from P↔Q ⟨$⟩_) (sym xs≈ys)

  to∘from : ∀ {xs ys} (xs≈ys : xs ≈ ys) (q : Any Q ys) →
            to xs≈ys (from xs≈ys q) ≡ q
  to∘from (x ∷ xs≈) (there q) = P.cong there (to∘from (♭ xs≈) q)
  to∘from (x ∷ xs≈) (here qx) =
    P.cong here (Inverse.right-inverse-of P↔Q qx)

  from∘to : ∀ {xs ys} (xs≈ys : xs ≈ ys) (p : Any P xs) →
            from xs≈ys (to xs≈ys p) ≡ p
  from∘to (x ∷ xs≈) (there p) = P.cong there (from∘to (♭ xs≈) p)
  from∘to (x ∷ xs≈) (here px) =
    P.cong here (Inverse.left-inverse-of P↔Q px)

------------------------------------------------------------------------
-- map

module _ {f : A → B} where

  map⁻ : ∀ {xs} → Any P (map f xs) → Any (P ∘ f) xs
  map⁻ {xs = x ∷ xs} (here px) = here px
  map⁻ {xs = x ∷ xs} (there p) = there (map⁻ p)

  map⁺ : ∀ {xs} → Any (P ∘ f) xs → Any P (map f xs)
  map⁺ (here px) = here px
  map⁺ (there p) = there (map⁺ p)

  Any-map : ∀ {xs} → Any P (map f xs) ↔ Any (P ∘ f) xs
  Any-map {xs = xs} = inverse map⁻ map⁺ from∘to to∘from where

    from∘to : ∀ {xs} (p : Any P (map f xs)) → map⁺ (map⁻ p) ≡ p
    from∘to {xs = x ∷ xs} (here px) = refl
    from∘to {xs = x ∷ xs} (there p) = cong there (from∘to p)

    to∘from : ∀ {xs} (p : Any (P ∘ f) xs) → map⁻ {P = P} (map⁺ p) ≡ p
    to∘from (here px) = refl
    to∘from (there p) = cong there (to∘from p)

------------------------------------------------------------------------
-- _⋎_

⋎⁻ : ∀ xs {ys} → Any P (xs ⋎ ys) → Any P xs ⊎ Any P ys
⋎⁻ []       p         = inj₂ p
⋎⁻ (x ∷ xs) (here px) = inj₁ (here px)
⋎⁻ (x ∷ xs) (there p) = [ inj₂ , inj₁ ∘ there ]′ (⋎⁻ _ p)

mutual

  ⋎⁺₁ : ∀ {xs ys} → Any P xs → Any P (xs ⋎ ys)
  ⋎⁺₁           (here px) = here px
  ⋎⁺₁ {ys = ys} (there p) = there (⋎⁺₂ ys p)

  ⋎⁺₂ : ∀ xs {ys} → Any P ys → Any P (xs ⋎ ys)
  ⋎⁺₂ []       p = p
  ⋎⁺₂ (x ∷ xs) p = there (⋎⁺₁ p)

⋎⁺ : ∀ xs {ys} → Any P xs ⊎ Any P ys → Any P (xs ⋎ ys)
⋎⁺ xs = [ ⋎⁺₁ , ⋎⁺₂ xs ]

Any-⋎ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} →
        Any P (xs ⋎ ys) ↔ (Any P xs ⊎ Any P ys)
Any-⋎ {P = P} = λ xs → record
  { to         = P.→-to-⟶ (⋎⁻ xs)
  ; from       = P.→-to-⟶ (⋎⁺ xs)
  ; inverse-of = record
    { left-inverse-of  = from∘to xs
    ; right-inverse-of = to∘from xs
    }
  }
  where

  from∘to : ∀ xs {ys} (p : Any P (xs ⋎ ys)) → ⋎⁺ xs (⋎⁻ xs p) ≡ p
  from∘to []                 p                          = refl
  from∘to (x ∷ xs)           (here px)                  = refl
  from∘to (x ∷ xs) {ys = ys} (there p)                  with ⋎⁻ ys p | from∘to ys p
  from∘to (x ∷ xs) {ys = ys} (there .(⋎⁺₁ q))     | inj₁ q | refl = refl
  from∘to (x ∷ xs) {ys = ys} (there .(⋎⁺₂ ys q)) | inj₂ q | refl = refl

  mutual

    to∘from₁ : ∀ {xs ys} (p : Any P xs) →
                   ⋎⁻ xs {ys = ys} (⋎⁺₁ p) ≡ inj₁ p
    to∘from₁           (here px) = refl
    to∘from₁ {ys = ys} (there p)
      rewrite to∘from₂ ys p = refl

    to∘from₂ : ∀ xs {ys} (p : Any P ys) →
                    ⋎⁻ xs (⋎⁺₂ xs p) ≡ inj₂ p
    to∘from₂ []                 p = refl
    to∘from₂ (x ∷ xs) {ys = ys} p
      rewrite to∘from₁ {xs = ys} {ys = ♭ xs} p = refl

  to∘from : ∀ xs {ys} (p : Any P xs ⊎ Any P ys) → ⋎⁻ xs (⋎⁺ xs p) ≡ p
  to∘from xs = [ to∘from₁ , to∘from₂ xs ]

------------------------------------------------------------------------
-- index

-- The position returned by index is guaranteed to be within bounds.

lookup-index : ∀ {xs} (p : Any P xs) → Is-just (lookup (index p) xs)
lookup-index (here px) = just _
lookup-index (there p) = lookup-index p

-- Any-resp preserves the index.

index-Any-resp : ∀ {f : ∀ {x} → P x → Q x} {xs ys}
                 (xs≈ys : xs ≈ ys) (p : Any P xs) →
                 index (Any-resp f xs≈ys p) ≡ index p
index-Any-resp (x ∷ xs≈) (here px) = P.refl
index-Any-resp (x ∷ xs≈) (there p) =
  cong suc (index-Any-resp (♭ xs≈) p)

-- The left-to-right direction of Any-⋎ returns a proof whose size is
-- no larger than that of the input proof.

index-Any-⋎ : ∀ xs {ys} (p : Any P (xs ⋎ ys)) →
              index p ≥′ [ index , index ]′ (Inverse.to (Any-⋎ xs) ⟨$⟩ p)
index-Any-⋎ []                 p         = ≤′-refl
index-Any-⋎ (x ∷ xs)           (here px) = ≤′-refl
index-Any-⋎ (x ∷ xs) {ys = ys} (there p)
  with Inverse.to (Any-⋎ ys) ⟨$⟩ p | index-Any-⋎ ys p
... | inj₁ q | q≤p = ≤′-step q≤p
... | inj₂ q | q≤p = s≤′s    q≤p
