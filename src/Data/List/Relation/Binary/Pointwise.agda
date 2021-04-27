------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Pointwise where

open import Algebra.Core using (Op₂)
open import Function.Base
open import Function.Inverse using (Inverse)
open import Data.Bool.Base using (true; false)
open import Data.Product hiding (map)
open import Data.List.Base as List hiding (map; head; tail; uncons)
open import Data.List.Properties using (≡-dec; length-++)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Fin.Base using (Fin; toℕ; cast) renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties
open import Level
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Negation.Core using (contradiction)
import Relation.Nullary.Decidable as Dec using (map′)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary as U using (Pred)
open import Relation.Binary renaming (Rel to Rel₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private
  variable
    a b c d p q ℓ ℓ₁ ℓ₂ : Level
    A B C D : Set d
    x y z : A
    ws xs ys zs : List A
    R S T : REL A B ℓ

------------------------------------------------------------------------
-- Re-exporting the definition and basic operations
------------------------------------------------------------------------

open import Data.List.Relation.Binary.Pointwise.Base public
open import Data.List.Relation.Binary.Pointwise.Properties public

------------------------------------------------------------------------
-- Structures

isEquivalence : IsEquivalence R → IsEquivalence (Pointwise R)
isEquivalence eq = record
  { refl  = refl       Eq.refl
  ; sym   = symmetric  Eq.sym
  ; trans = transitive Eq.trans
  } where module Eq = IsEquivalence eq

isDecEquivalence : IsDecEquivalence R → IsDecEquivalence (Pointwise R)
isDecEquivalence eq = record
  { isEquivalence = isEquivalence DE.isEquivalence
  ; _≟_           = decidable     DE._≟_
  } where module DE = IsDecEquivalence eq

isPreorder : IsPreorder R S → IsPreorder (Pointwise R) (Pointwise S)
isPreorder pre = record
  { isEquivalence = isEquivalence Pre.isEquivalence
  ; reflexive     = reflexive     Pre.reflexive
  ; trans         = transitive    Pre.trans
  } where module Pre = IsPreorder pre

isPartialOrder : IsPartialOrder R S →
                 IsPartialOrder (Pointwise R) (Pointwise S)
isPartialOrder po = record
  { isPreorder = isPreorder    PO.isPreorder
  ; antisym    = antisymmetric PO.antisym
  } where module PO = IsPartialOrder po

------------------------------------------------------------------------
-- Bundles

setoid : Setoid a ℓ → Setoid a (a ⊔ ℓ)
setoid s = record
  { isEquivalence = isEquivalence (Setoid.isEquivalence s)
  }

decSetoid : DecSetoid a ℓ → DecSetoid a (a ⊔ ℓ)
decSetoid d = record
  { isDecEquivalence = isDecEquivalence (DecSetoid.isDecEquivalence d)
  }

preorder : Preorder a ℓ₁ ℓ₂ → Preorder _ _ _
preorder p = record
  { isPreorder = isPreorder (Preorder.isPreorder p)
  }

poset : Poset a ℓ₁ ℓ₂ → Poset _ _ _
poset p = record
  { isPartialOrder = isPartialOrder (Poset.isPartialOrder p)
  }

------------------------------------------------------------------------
-- Relationships to other list predicates
------------------------------------------------------------------------

All-resp-Pointwise : ∀ {P : Pred A p} → P Respects R →
                     (All P) Respects (Pointwise R)
All-resp-Pointwise resp []         []         = []
All-resp-Pointwise resp (x∼y ∷ xs) (px ∷ pxs) =
  resp x∼y px ∷ All-resp-Pointwise resp xs pxs

Any-resp-Pointwise : ∀ {P : Pred A p} → P Respects R →
                     (Any P) Respects (Pointwise R)
Any-resp-Pointwise resp (x∼y ∷ xs) (here px)   = here (resp x∼y px)
Any-resp-Pointwise resp (x∼y ∷ xs) (there pxs) =
  there (Any-resp-Pointwise resp xs pxs)

AllPairs-resp-Pointwise : R Respects₂ S →
                          (AllPairs R) Respects (Pointwise S)
AllPairs-resp-Pointwise _                    []         []         = []
AllPairs-resp-Pointwise resp@(respₗ , respᵣ) (x∼y ∷ xs) (px ∷ pxs) =
  All-resp-Pointwise respₗ xs (All.map (respᵣ x∼y) px) ∷
  (AllPairs-resp-Pointwise resp xs pxs)

------------------------------------------------------------------------
-- Relationship to functions over lists
------------------------------------------------------------------------
-- length

Pointwise-length : Pointwise R xs ys → length xs ≡ length ys
Pointwise-length []            = P.refl
Pointwise-length (x∼y ∷ xs∼ys) = P.cong ℕ.suc (Pointwise-length xs∼ys)

------------------------------------------------------------------------
-- tabulate

tabulate⁺ : ∀ {n} {f : Fin n → A} {g : Fin n → B} →
            (∀ i → R (f i) (g i)) → Pointwise R (tabulate f) (tabulate g)
tabulate⁺ {n = zero}  f∼g = []
tabulate⁺ {n = suc n} f∼g = f∼g fzero ∷ tabulate⁺ (f∼g ∘ fsuc)

tabulate⁻ : ∀ {n} {f : Fin n → A} {g : Fin n → B} →
            Pointwise R (tabulate f) (tabulate g) → (∀ i → R (f i) (g i))
tabulate⁻ {n = suc n} (x∼y ∷ xs∼ys) fzero    = x∼y
tabulate⁻ {n = suc n} (x∼y ∷ xs∼ys) (fsuc i) = tabulate⁻ xs∼ys i

------------------------------------------------------------------------
-- _++_

++⁺ : Pointwise R ws xs → Pointwise R ys zs →
      Pointwise R (ws ++ ys) (xs ++ zs)
++⁺ []            ys∼zs = ys∼zs
++⁺ (w∼x ∷ ws∼xs) ys∼zs = w∼x ∷ ++⁺ ws∼xs ys∼zs

++-cancelˡ : ∀ xs → Pointwise R (xs ++ ys) (xs ++ zs) → Pointwise R ys zs
++-cancelˡ []       ys∼zs               = ys∼zs
++-cancelˡ (x ∷ xs) (_ ∷ xs++ys∼xs++zs) = ++-cancelˡ xs xs++ys∼xs++zs

++-cancelʳ : ∀ ys zs → Pointwise R (ys ++ xs) (zs ++ xs) → Pointwise R ys zs
++-cancelʳ []       []       _             = []
++-cancelʳ (y ∷ ys) (z ∷ zs) (y∼z ∷ ys∼zs) = y∼z ∷ (++-cancelʳ ys zs ys∼zs)
-- Impossible cases
++-cancelʳ {xs = xs}     []       (z ∷ zs) eq   =
  contradiction (P.trans (Pointwise-length eq) (length-++ (z ∷ zs))) (m≢1+n+m (length xs))
++-cancelʳ {xs = xs}     (y ∷ ys) []       eq   =
  contradiction (P.trans (P.sym (length-++ (y ∷ ys))) (Pointwise-length eq)) (m≢1+n+m (length xs) ∘ P.sym)

------------------------------------------------------------------------
-- concat

concat⁺ : ∀ {xss yss} → Pointwise (Pointwise R) xss yss →
          Pointwise R (concat xss) (concat yss)
concat⁺ []                = []
concat⁺ (xs∼ys ∷ xss∼yss) = ++⁺ xs∼ys (concat⁺ xss∼yss)

------------------------------------------------------------------------
-- reverse

reverseAcc⁺ : Pointwise R ws xs → Pointwise R ys zs →
              Pointwise R (reverseAcc ws ys) (reverseAcc xs zs)
reverseAcc⁺ rs′ []       = rs′
reverseAcc⁺ rs′ (r ∷ rs) = reverseAcc⁺ (r ∷ rs′) rs

ʳ++⁺ : Pointwise R ws xs → Pointwise R ys zs →
       Pointwise R (ws ʳ++ ys) (xs ʳ++ zs)
ʳ++⁺ rs rs′ = reverseAcc⁺ rs′ rs

reverse⁺ : Pointwise R xs ys → Pointwise R (reverse xs) (reverse ys)
reverse⁺ = reverseAcc⁺ []

------------------------------------------------------------------------
-- map

map⁺ : ∀ (f : A → C) (g : B → D) →
       Pointwise (λ a b → R (f a) (g b)) xs ys →
       Pointwise R (List.map f xs) (List.map g ys)
map⁺ f g []       = []
map⁺ f g (r ∷ rs) = r ∷ map⁺ f g rs

map⁻ : ∀ (f : A → C) (g : B → D) →
       Pointwise R (List.map f xs) (List.map g ys) →
       Pointwise (λ a b → R (f a) (g b)) xs ys
map⁻ {xs = []}    {[]}    f g [] = []
map⁻ {xs = _ ∷ _} {_ ∷ _} f g (r ∷ rs) = r ∷ map⁻ f g rs

------------------------------------------------------------------------
-- foldr

foldr⁺ : ∀ {_•_ : Op₂ A} {_◦_ : Op₂ B} →
         (∀ {w x y z} → R w x → R y z → R (w • y) (x ◦ z)) →
         ∀ {e f} → R e f → Pointwise R xs ys →
         R (foldr _•_ e xs) (foldr _◦_ f ys)
foldr⁺ _    e~f []            = e~f
foldr⁺ pres e~f (x~y ∷ xs~ys) = pres x~y (foldr⁺ pres e~f xs~ys)

------------------------------------------------------------------------
-- filter

module _ {P : Pred A p} {Q : Pred B q}
         (P? : U.Decidable P) (Q? : U.Decidable Q)
         (P⇒Q : ∀ {a b} → R a b → P a → Q b)
         (Q⇒P : ∀ {a b} → R a b → Q b → P a)
         where

  filter⁺ : Pointwise R xs ys →
            Pointwise R (filter P? xs) (filter Q? ys)
  filter⁺ []       = []
  filter⁺ {x ∷ _} {y ∷ _} (r ∷ rs) with P? x | Q? y
  ... | true  because _ | true  because _ = r ∷ filter⁺ rs
  ... | false because _ | false because _ = filter⁺ rs
  ... | yes p           | no ¬q = contradiction (P⇒Q r p) ¬q
  ... | no ¬p           | yes q = contradiction (Q⇒P r q) ¬p

------------------------------------------------------------------------
-- replicate

replicate⁺ : R x y → ∀ n → Pointwise R (replicate n x) (replicate n y)
replicate⁺ r 0       = []
replicate⁺ r (suc n) = r ∷ replicate⁺ r n

------------------------------------------------------------------------
-- lookup

lookup⁻ : length xs ≡ length ys →
          (∀ {i j} → toℕ i ≡ toℕ j → R (lookup xs i) (lookup ys j)) →
          Pointwise R xs ys
lookup⁻ {xs = []}    {ys = []}    _             _  = []
lookup⁻ {xs = _ ∷ _} {ys = _ ∷ _} |xs|≡|ys| eq = eq {fzero} P.refl ∷
  lookup⁻ (suc-injective |xs|≡|ys|) (eq ∘ P.cong ℕ.suc)

lookup⁺ : ∀ (Rxys : Pointwise R xs ys) →
          ∀ i → (let j = cast (Pointwise-length Rxys) i) →
          R (lookup xs i) (lookup ys j)
lookup⁺ (Rxy ∷ _)    fzero    = Rxy
lookup⁺ (_   ∷ Rxys) (fsuc i) = lookup⁺ Rxys i

------------------------------------------------------------------------
-- Properties of propositional pointwise
------------------------------------------------------------------------

Pointwise-≡⇒≡ : Pointwise {A = A} _≡_ ⇒ _≡_
Pointwise-≡⇒≡ []               = P.refl
Pointwise-≡⇒≡ (P.refl ∷ xs∼ys) with Pointwise-≡⇒≡ xs∼ys
... | P.refl = P.refl

≡⇒Pointwise-≡ :  _≡_ ⇒ Pointwise {A = A} _≡_
≡⇒Pointwise-≡ P.refl = refl P.refl

Pointwise-≡↔≡ : Inverse (setoid (P.setoid A)) (P.setoid (List A))
Pointwise-≡↔≡ = record
  { to         = record { _⟨$⟩_ = id; cong = Pointwise-≡⇒≡ }
  ; from       = record { _⟨$⟩_ = id; cong = ≡⇒Pointwise-≡ }
  ; inverse-of = record
    { left-inverse-of  = λ _ → refl P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

Rel    = Pointwise
{-# WARNING_ON_USAGE Rel
"Warning: Rel was deprecated in v0.15.
Please use Pointwise instead."
#-}
Rel≡⇒≡ = Pointwise-≡⇒≡
{-# WARNING_ON_USAGE Rel≡⇒≡
"Warning: Rel≡⇒≡ was deprecated in v0.15.
Please use Pointwise-≡⇒≡ instead."
#-}
≡⇒Rel≡ = ≡⇒Pointwise-≡
{-# WARNING_ON_USAGE ≡⇒Rel≡
"Warning: ≡⇒Rel≡ was deprecated in v0.15.
Please use ≡⇒Pointwise-≡ instead."
#-}
Rel↔≡  = Pointwise-≡↔≡
{-# WARNING_ON_USAGE Rel↔≡
"Warning: Rel↔≡ was deprecated in v0.15.
Please use Pointwise-≡↔≡ instead."
#-}

-- Version 1.0

decidable-≡ = ≡-dec
{-# WARNING_ON_USAGE decidable-≡
"Warning: decidable-≡ was deprecated in v1.0.
Please use ≡-dec from `Data.List.Properties` instead."
#-}
