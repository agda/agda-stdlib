------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Pointwise where

open import Function
open import Function.Inverse using (Inverse)
open import Data.Product hiding (map)
open import Data.List.Base as List hiding (map; head; tail)
open import Data.List.Properties using (≡-dec; length-++)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties
open import Level
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Nullary.Decidable as Dec using (map′)
open import Relation.Unary as U using (Pred)
open import Relation.Binary renaming (Rel to Rel₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

private
  variable
    a b c d p q ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

------------------------------------------------------------------------
-- Definition

infixr 5 _∷_

data Pointwise {A : Set a} {B : Set b} (_∼_ : REL A B ℓ)
               : List A → List B → Set (a ⊔ b ⊔ ℓ) where
  []  : Pointwise _∼_ [] []
  _∷_ : ∀ {x xs y ys} (x∼y : x ∼ y) (xs∼ys : Pointwise _∼_ xs ys) →
        Pointwise _∼_ (x ∷ xs) (y ∷ ys)

------------------------------------------------------------------------
-- Operations

module _ {_∼_ : REL A B ℓ} where

  head : ∀ {x y xs ys} → Pointwise _∼_ (x ∷ xs) (y ∷ ys) → x ∼ y
  head (x∼y ∷ xs∼ys) = x∼y

  tail : ∀ {x y xs ys} → Pointwise _∼_ (x ∷ xs) (y ∷ ys) →
         Pointwise _∼_ xs ys
  tail (x∼y ∷ xs∼ys) = xs∼ys

  rec : ∀ (P : ∀ {xs ys} → Pointwise _∼_ xs ys → Set c) →
        (∀ {x y xs ys} {xs∼ys : Pointwise _∼_ xs ys} →
          (x∼y : x ∼ y) → P xs∼ys → P (x∼y ∷ xs∼ys)) →
        P [] →
        ∀ {xs ys} (xs∼ys : Pointwise _∼_ xs ys) → P xs∼ys
  rec P c n []            = n
  rec P c n (x∼y ∷ xs∼ys) = c x∼y (rec P c n xs∼ys)

  map : ∀ {_≈_ : REL A B ℓ₂} → _≈_ ⇒ _∼_ → Pointwise _≈_ ⇒ Pointwise _∼_
  map ≈⇒∼ []            = []
  map ≈⇒∼ (x≈y ∷ xs≈ys) = ≈⇒∼ x≈y ∷ map ≈⇒∼ xs≈ys

------------------------------------------------------------------------
-- Relational properties

reflexive : ∀ {_≈_ : REL A B ℓ₁} {_∼_ : REL A B ℓ₂} →
            _≈_ ⇒ _∼_ → Pointwise _≈_ ⇒ Pointwise _∼_
reflexive ≈⇒∼ []            = []
reflexive ≈⇒∼ (x≈y ∷ xs≈ys) = ≈⇒∼ x≈y ∷ reflexive ≈⇒∼ xs≈ys

refl : ∀ {_∼_ : Rel₂ A ℓ} → Reflexive _∼_ → Reflexive (Pointwise _∼_)
refl rfl {[]}     = []
refl rfl {x ∷ xs} = rfl ∷ refl rfl

symmetric : ∀ {_≈_ : REL A B ℓ₁} {_∼_ : REL B A ℓ₂} →
            Sym _≈_ _∼_ → Sym (Pointwise _≈_) (Pointwise _∼_)
symmetric sym []            = []
symmetric sym (x∼y ∷ xs∼ys) = sym x∼y ∷ symmetric sym xs∼ys

transitive : ∀ {_≋_ : REL A B ℓ₁} {_≈_ : REL B C ℓ₂} {_∼_ : REL A C ℓ₃} →
             Trans _≋_ _≈_ _∼_ →
             Trans (Pointwise _≋_) (Pointwise _≈_) (Pointwise _∼_)
transitive trans []            []            = []
transitive trans (x∼y ∷ xs∼ys) (y∼z ∷ ys∼zs) =
  trans x∼y y∼z ∷ transitive trans xs∼ys ys∼zs

antisymmetric : ∀ {_≤_ : REL A B ℓ₁} {_≤′_ : REL B A ℓ₂} {_≈_ : REL A B ℓ₃} →
                Antisym _≤_ _≤′_ _≈_ →
                Antisym (Pointwise _≤_) (Pointwise _≤′_) (Pointwise _≈_)
antisymmetric antisym []            []            = []
antisymmetric antisym (x∼y ∷ xs∼ys) (y∼x ∷ ys∼xs) =
  antisym x∼y y∼x ∷ antisymmetric antisym xs∼ys ys∼xs

respects₂ : ∀ {_≈_ : Rel₂ A ℓ₁} {_∼_ : Rel₂ A ℓ₂} →
            _∼_ Respects₂ _≈_ → (Pointwise _∼_) Respects₂ (Pointwise _≈_)
respects₂ {_≈_ = _≈_} {_∼_} resp = respʳ , respˡ
  where
  respʳ : (Pointwise _∼_) Respectsʳ (Pointwise _≈_)
  respʳ []            []            = []
  respʳ (x≈y ∷ xs≈ys) (z∼x ∷ zs∼xs) =
    proj₁ resp x≈y z∼x ∷ respʳ xs≈ys zs∼xs

  respˡ : (Pointwise _∼_) Respectsˡ (Pointwise _≈_)
  respˡ []            []            = []
  respˡ (x≈y ∷ xs≈ys) (x∼z ∷ xs∼zs) =
    proj₂ resp x≈y x∼z ∷ respˡ xs≈ys xs∼zs

decidable : ∀ {_∼_ : REL A B ℓ} → Decidable _∼_ → Decidable (Pointwise _∼_)
decidable dec []       []       = yes []
decidable dec []       (y ∷ ys) = no (λ ())
decidable dec (x ∷ xs) []       = no (λ ())
decidable dec (x ∷ xs) (y ∷ ys) with dec x y
... | no ¬x∼y = no (¬x∼y ∘ head)
... | yes x∼y with decidable dec xs ys
...   | no ¬xs∼ys = no (¬xs∼ys ∘ tail)
...   | yes xs∼ys = yes (x∼y ∷ xs∼ys)

module _ {_≈_ : Rel₂ A ℓ} where

  isEquivalence : IsEquivalence _≈_ → IsEquivalence (Pointwise _≈_)
  isEquivalence eq = record
    { refl  = refl       Eq.refl
    ; sym   = symmetric  Eq.sym
    ; trans = transitive Eq.trans
    } where module Eq = IsEquivalence eq

  isDecEquivalence : IsDecEquivalence _≈_ → IsDecEquivalence (Pointwise _≈_)
  isDecEquivalence eq = record
    { isEquivalence = isEquivalence DE.isEquivalence
    ; _≟_           = decidable     DE._≟_
    } where module DE = IsDecEquivalence eq

module _ {_≈_ : Rel₂ A ℓ₁} {_∼_ : Rel₂ A ℓ₂} where

  isPreorder : IsPreorder _≈_ _∼_ → IsPreorder (Pointwise _≈_) (Pointwise _∼_)
  isPreorder pre = record
    { isEquivalence = isEquivalence Pre.isEquivalence
    ; reflexive     = reflexive     Pre.reflexive
    ; trans         = transitive    Pre.trans
    } where module Pre = IsPreorder pre

  isPartialOrder : IsPartialOrder _≈_ _∼_ →
                   IsPartialOrder (Pointwise _≈_) (Pointwise _∼_)
  isPartialOrder po = record
    { isPreorder = isPreorder    PO.isPreorder
    ; antisym    = antisymmetric PO.antisym
    } where module PO = IsPartialOrder po

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
-- length

module _ {_∼_ : REL A B ℓ} where

  Pointwise-length : ∀ {xs ys} → Pointwise _∼_ xs ys →
                     length xs ≡ length ys
  Pointwise-length []            = P.refl
  Pointwise-length (x∼y ∷ xs∼ys) = P.cong ℕ.suc (Pointwise-length xs∼ys)

------------------------------------------------------------------------
-- tabulate

module _ {_∼_ : REL A B ℓ} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} {g : Fin n → B} →
              (∀ i → f i ∼ g i) → Pointwise _∼_ (tabulate f) (tabulate g)
  tabulate⁺ {zero}  f∼g = []
  tabulate⁺ {suc n} f∼g = f∼g fzero ∷ tabulate⁺ (f∼g ∘ fsuc)

  tabulate⁻ : ∀ {n} {f : Fin n → A} {g : Fin n → B} →
              Pointwise _∼_ (tabulate f) (tabulate g) → (∀ i → f i ∼ g i)
  tabulate⁻ {suc n} (x∼y ∷ xs∼ys) fzero    = x∼y
  tabulate⁻ {suc n} (x∼y ∷ xs∼ys) (fsuc i) = tabulate⁻ xs∼ys i

------------------------------------------------------------------------
-- _++_

module _ {_∼_ : REL A B ℓ} where

  ++⁺ : ∀ {ws xs ys zs} → Pointwise _∼_ ws xs → Pointwise _∼_ ys zs →
        Pointwise _∼_ (ws ++ ys) (xs ++ zs)
  ++⁺ []            ys∼zs = ys∼zs
  ++⁺ (w∼x ∷ ws∼xs) ys∼zs = w∼x ∷ ++⁺ ws∼xs ys∼zs

module _ {_∼_ : Rel₂ A ℓ} where

  ++-cancelˡ : ∀ xs {ys zs : List A} → Pointwise _∼_ (xs ++ ys) (xs ++ zs) → Pointwise _∼_ ys zs
  ++-cancelˡ []       ys∼zs               = ys∼zs
  ++-cancelˡ (x ∷ xs) (_ ∷ xs++ys∼xs++zs) = ++-cancelˡ xs xs++ys∼xs++zs

  ++-cancelʳ : ∀ {xs : List A} ys zs → Pointwise _∼_ (ys ++ xs) (zs ++ xs) → Pointwise _∼_ ys zs
  ++-cancelʳ []       []       _             = []
  ++-cancelʳ (y ∷ ys) (z ∷ zs) (y∼z ∷ ys∼zs) = y∼z ∷ (++-cancelʳ ys zs ys∼zs)
  -- Impossible cases
  ++-cancelʳ {xs}     []       (z ∷ zs) eq   =
    contradiction (P.trans (Pointwise-length eq) (length-++ (z ∷ zs))) (m≢1+n+m (length xs))
  ++-cancelʳ {xs}     (y ∷ ys) []       eq   =
    contradiction (P.trans (P.sym (length-++ (y ∷ ys))) (Pointwise-length eq)) (m≢1+n+m (length xs) ∘ P.sym)

------------------------------------------------------------------------
-- concat

module _ {_∼_ : REL A B ℓ} where

  concat⁺ : ∀ {xss yss} → Pointwise (Pointwise _∼_) xss yss →
            Pointwise _∼_ (concat xss) (concat yss)
  concat⁺ []                = []
  concat⁺ (xs∼ys ∷ xss∼yss) = ++⁺ xs∼ys (concat⁺ xss∼yss)

------------------------------------------------------------------------
-- reverse

module _ {R : REL A B ℓ} where

  reverseAcc⁺ : ∀ {as bs as′ bs′} → Pointwise R as′ bs′ → Pointwise R as bs →
                Pointwise R (reverseAcc as′ as) (reverseAcc bs′ bs)
  reverseAcc⁺ rs′ []       = rs′
  reverseAcc⁺ rs′ (r ∷ rs) = reverseAcc⁺ (r ∷ rs′) rs

  reverse⁺ : ∀ {as bs} → Pointwise R as bs → Pointwise R (reverse as) (reverse bs)
  reverse⁺ = reverseAcc⁺ []

------------------------------------------------------------------------
-- map

module _ {R : REL C D ℓ} where

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Pointwise (λ a b → R (f a) (g b)) as bs →
         Pointwise R (List.map f as) (List.map g bs)
  map⁺ f g []       = []
  map⁺ f g (r ∷ rs) = r ∷ map⁺ f g rs

  map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
         Pointwise R (List.map f as) (List.map g bs) →
         Pointwise (λ a b → R (f a) (g b)) as bs
  map⁻ {as = []}     {[]}     f g [] = []
  map⁻ {as = []}     {b ∷ bs} f g rs = contradiction (Pointwise-length rs) λ()
  map⁻ {as = a ∷ as} {[]}     f g rs = contradiction (Pointwise-length rs) λ()
  map⁻ {as = a ∷ as} {b ∷ bs} f g (r ∷ rs) = r ∷ map⁻ f g rs

------------------------------------------------------------------------
-- filter

module _ {R : REL A B ℓ} {P : Pred A p} {Q : Pred B q}
         (P? : U.Decidable P) (Q? : U.Decidable Q)
         (P⇒Q : ∀ {a b} → R a b → P a → Q b)
         (Q⇒P : ∀ {a b} → R a b → Q b → P a)
         where

  filter⁺ : ∀ {as bs} → Pointwise R as bs → Pointwise R (filter P? as) (filter Q? bs)
  filter⁺ []       = []
  filter⁺ {a ∷ _} {b ∷ _} (r ∷ rs) with P? a | Q? b
  ... | yes p | yes q = r ∷ filter⁺ rs
  ... | yes p | no ¬q = contradiction (P⇒Q r p) ¬q
  ... | no ¬p | yes q = contradiction (Q⇒P r q) ¬p
  ... | no ¬p | no ¬q = filter⁺ rs

------------------------------------------------------------------------
-- replicate

module _ {R : REL A B ℓ} where

  replicate⁺ : ∀ {a b} → R a b → ∀ n → Pointwise R (replicate n a) (replicate n b)
  replicate⁺ r 0       = []
  replicate⁺ r (suc n) = r ∷ replicate⁺ r n

------------------------------------------------------------------------
-- Irrelevance

module _ {R : REL A B ℓ} where

  irrelevant : Irrelevant R → Irrelevant (Pointwise R)
  irrelevant R-irr [] [] = P.refl
  irrelevant R-irr (r ∷ rs) (r₁ ∷ rs₁) =
    P.cong₂ _∷_ (R-irr r r₁) (irrelevant R-irr rs rs₁)

------------------------------------------------------------------------
-- Properties of propositional pointwise

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
