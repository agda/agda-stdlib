------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

module Data.List.All.Properties where

open import Data.Bool.Base using (Bool; T)
open import Data.Bool.Properties
open import Data.Empty
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.All as All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Sublist.Extensional.Propositional using (_⊆_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; z≤n; s≤s; _<_)
open import Data.Product as Prod using (_×_; _,_; uncurry; uncurry′)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Function.Inverse using (_↔_; inverse)
open import Function.Surjection using (_↠_; surjection)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Unary
  using (Decidable; Universal) renaming (_⊆_ to _⋐_)

------------------------------------------------------------------------
-- Lemmas relating Any, All and negation.

module _ {a p} {A : Set a} {P : A → Set p} where

  ¬Any⇒All¬ : ∀ xs → ¬ Any P xs → All (¬_ ∘ P) xs
  ¬Any⇒All¬ []       ¬p = []
  ¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ∷ ¬Any⇒All¬ xs (¬p ∘ there)

  All¬⇒¬Any : ∀ {xs} → All (¬_ ∘ P) xs → ¬ Any P xs
  All¬⇒¬Any []        ()
  All¬⇒¬Any (¬p ∷ _)  (here  p) = ¬p p
  All¬⇒¬Any (_  ∷ ¬p) (there p) = All¬⇒¬Any ¬p p

  ¬All⇒Any¬ : Decidable P → ∀ xs → ¬ All P xs → Any (¬_ ∘ P) xs
  ¬All⇒Any¬ dec []       ¬∀ = ⊥-elim (¬∀ [])
  ¬All⇒Any¬ dec (x ∷ xs) ¬∀ with dec x
  ... | yes p = there (¬All⇒Any¬ dec xs (¬∀ ∘ _∷_ p))
  ... | no ¬p = here ¬p

  Any¬→¬All : ∀ {xs} → Any (¬_ ∘ P) xs → ¬ All P xs
  Any¬→¬All (here  ¬p) = ¬p           ∘ All.head
  Any¬→¬All (there ¬p) = Any¬→¬All ¬p ∘ All.tail

  ¬Any↠All¬ : ∀ {xs} → (¬ Any P xs) ↠ All (¬_ ∘ P) xs
  ¬Any↠All¬ = surjection (¬Any⇒All¬ _) All¬⇒¬Any to∘from
    where
    to∘from : ∀ {xs} (¬p : All (¬_ ∘ P) xs) → ¬Any⇒All¬ xs (All¬⇒¬Any ¬p) ≡ ¬p
    to∘from []         = P.refl
    to∘from (¬p ∷ ¬ps) = P.cong₂ _∷_ P.refl (to∘from ¬ps)

    -- If equality of functions were extensional, then the surjection
    -- could be strengthened to a bijection.

    from∘to : P.Extensionality _ _ →
              ∀ xs → (¬p : ¬ Any P xs) → All¬⇒¬Any (¬Any⇒All¬ xs ¬p) ≡ ¬p
    from∘to ext []       ¬p = ext λ ()
    from∘to ext (x ∷ xs) ¬p = ext λ
      { (here p)  → P.refl
      ; (there p) → P.cong (λ f → f p) $ from∘to ext xs (¬p ∘ there)
      }

  Any¬⇔¬All : ∀ {xs} → Decidable P → Any (¬_ ∘ P) xs ⇔ (¬ All P xs)
  Any¬⇔¬All dec = equivalence Any¬→¬All (¬All⇒Any¬ dec _)
    where
    -- If equality of functions were extensional, then the logical
    -- equivalence could be strengthened to a surjection.
    to∘from : P.Extensionality _ _ →
              ∀ {xs} (¬∀ : ¬ All P xs) → Any¬→¬All (¬All⇒Any¬ dec xs ¬∀) ≡ ¬∀
    to∘from ext ¬∀ = ext (⊥-elim ∘ ¬∀)

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {a b p} {A : Set a} {B : Set b} {P : B → Set p} {f : A → B} where

  map⁺ : ∀ {xs} → All (P ∘ f) xs → All P (map f xs)
  map⁺ []       = []
  map⁺ (p ∷ ps) = p ∷ map⁺ ps

  map⁻ : ∀ {xs} → All P (map f xs) → All (P ∘ f) xs
  map⁻ {xs = []}    []       = []
  map⁻ {xs = _ ∷ _} (p ∷ ps) = p ∷ map⁻ ps

-- A variant of All.map.

module _ {a b p q} {A : Set a} {B : Set b} {f : A → B}
         {P : A → Set p} {Q : B → Set q} where

  gmap : P ⋐ Q ∘ f → All P ⋐ All Q ∘ map f
  gmap g = map⁺ ∘ All.map g

------------------------------------------------------------------------
-- mapMaybe

module _ {a b p} {A : Set a} {B : Set b}
         (P : B → Set p) {f : A → Maybe B} where

  mapMaybe⁺ : ∀ {xs} → All (Maybe.All P) (map f xs) → All P (mapMaybe f xs)
  mapMaybe⁺ {[]}     [] = []
  mapMaybe⁺ {x ∷ xs} (px ∷ pxs) with f x
  ... | nothing = mapMaybe⁺ pxs
  ... | just v with px
  ...   | just pv = pv ∷ mapMaybe⁺ pxs

------------------------------------------------------------------------
-- _++_

module _ {a p} {A : Set a} {P : A → Set p} where

  ++⁺ : ∀ {xs ys} → All P xs → All P ys → All P (xs ++ ys)
  ++⁺ []         pys = pys
  ++⁺ (px ∷ pxs) pys = px ∷ ++⁺ pxs pys

  ++⁻ˡ : ∀ xs {ys} → All P (xs ++ ys) → All P xs
  ++⁻ˡ []       p          = []
  ++⁻ˡ (x ∷ xs) (px ∷ pxs) = px ∷ (++⁻ˡ _ pxs)

  ++⁻ʳ : ∀ xs {ys} → All P (xs ++ ys) → All P ys
  ++⁻ʳ []       p          = p
  ++⁻ʳ (x ∷ xs) (px ∷ pxs) = ++⁻ʳ xs pxs

  ++⁻ : ∀ xs {ys} → All P (xs ++ ys) → All P xs × All P ys
  ++⁻ []       p          = [] , p
  ++⁻ (x ∷ xs) (px ∷ pxs) = Prod.map (px ∷_) id (++⁻ _ pxs)

  ++↔ : ∀ {xs ys} → (All P xs × All P ys) ↔ All P (xs ++ ys)
  ++↔ {xs} = inverse (uncurry ++⁺) (++⁻ xs) ++⁻∘++⁺ (++⁺∘++⁻ xs)
    where
    ++⁺∘++⁻ : ∀ xs {ys} (p : All P (xs ++ ys)) →
              uncurry′ ++⁺ (++⁻ xs p) ≡ p
    ++⁺∘++⁻ []       p          = P.refl
    ++⁺∘++⁻ (x ∷ xs) (px ∷ pxs) = P.cong (_∷_ px) $ ++⁺∘++⁻ xs pxs

    ++⁻∘++⁺ : ∀ {xs ys} (p : All P xs × All P ys) →
              ++⁻ xs (uncurry ++⁺ p) ≡ p
    ++⁻∘++⁺ ([]       , pys) = P.refl
    ++⁻∘++⁺ (px ∷ pxs , pys) rewrite ++⁻∘++⁺ (pxs , pys) = P.refl

------------------------------------------------------------------------
-- concat

module _ {a p} {A : Set a} {P : A → Set p} where

  concat⁺ : ∀ {xss} → All (All P) xss → All P (concat xss)
  concat⁺ []           = []
  concat⁺ (pxs ∷ pxss) = ++⁺ pxs (concat⁺ pxss)

  concat⁻ : ∀ {xss} → All P (concat xss) → All (All P) xss
  concat⁻ {[]}       []  = []
  concat⁻ {xs ∷ xss} pxs = ++⁻ˡ xs pxs ∷ concat⁻ (++⁻ʳ xs pxs)

------------------------------------------------------------------------
-- take and drop

module _ {a p} {A : Set a} {P : A → Set p} where

  drop⁺ : ∀ {xs} n → All P xs → All P (drop n xs)
  drop⁺ zero    pxs        = pxs
  drop⁺ (suc n) []         = []
  drop⁺ (suc n) (px ∷ pxs) = drop⁺ n pxs

  take⁺ : ∀ {xs} n → All P xs → All P (take n xs)
  take⁺ zero    pxs        = []
  take⁺ (suc n) []         = []
  take⁺ (suc n) (px ∷ pxs) = px ∷ take⁺ n pxs

------------------------------------------------------------------------
-- applyUpTo

module _ {a p} {A : Set a} {P : A → Set p} where

  applyUpTo⁺₁ : ∀ f n → (∀ {i} → i < n → P (f i)) → All P (applyUpTo f n)
  applyUpTo⁺₁ f zero    Pf = []
  applyUpTo⁺₁ f (suc n) Pf = Pf (s≤s z≤n) ∷ applyUpTo⁺₁ (f ∘ suc) n (Pf ∘ s≤s)

  applyUpTo⁺₂ : ∀ f n → (∀ i → P (f i)) → All P (applyUpTo f n)
  applyUpTo⁺₂ f n Pf = applyUpTo⁺₁ f n (λ _ → Pf _)

  applyUpTo⁻ : ∀ f n → All P (applyUpTo f n) → ∀ {i} → i < n → P (f i)
  applyUpTo⁻ f zero    pxs        ()
  applyUpTo⁻ f (suc n) (px ∷ _)   (s≤s z≤n)       = px
  applyUpTo⁻ f (suc n) (_  ∷ pxs) (s≤s (s≤s i<n)) =
    applyUpTo⁻ (f ∘ suc) n pxs (s≤s i<n)

------------------------------------------------------------------------
-- tabulate

module _ {a p} {A : Set a} {P : A → Set p} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} →
              (∀ i → P (f i)) → All P (tabulate f)
  tabulate⁺ {zero}  Pf = []
  tabulate⁺ {suc n} Pf = Pf fzero ∷ tabulate⁺ (Pf ∘ fsuc)

  tabulate⁻ : ∀ {n} {f : Fin n → A} →
              All P (tabulate f) → (∀ i → P (f i))
  tabulate⁻ {zero}  pf       ()
  tabulate⁻ {suc n} (px ∷ _) fzero    = px
  tabulate⁻ {suc n} (_ ∷ pf) (fsuc i) = tabulate⁻ pf i

------------------------------------------------------------------------
-- filter

module _ {a p} {A : Set a} {P : A → Set p} (P? : Decidable P) where

  filter⁺₁ : ∀ xs → All P (filter P? xs)
  filter⁺₁ []       = []
  filter⁺₁ (x ∷ xs) with P? x
  ... | yes Px = Px ∷ filter⁺₁ xs
  ... | no  _  = filter⁺₁ xs

  filter⁺₂ : ∀ {q} {Q : A → Set q} {xs} →
             All Q xs → All Q (filter P? xs)
  filter⁺₂ {xs = _}     [] = []
  filter⁺₂ {xs = x ∷ _} (Qx ∷ Qxs) with P? x
  ... | no  _ = filter⁺₂ Qxs
  ... | yes _ = Qx ∷ filter⁺₂ Qxs

------------------------------------------------------------------------
-- zipWith

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

  zipWith⁺ : ∀ {p} (P : C → Set p) (f : A → B → C) {xs ys} →
             Pointwise (λ x y → P (f x y)) xs ys →
             All P (zipWith f xs ys)
  zipWith⁺ P f []              = []
  zipWith⁺ P f (Pfxy ∷ Pfxsys) = Pfxy ∷ zipWith⁺ P f Pfxsys

------------------------------------------------------------------------
-- Operations for constructing lists
------------------------------------------------------------------------
-- singleton

module _ {a p} {A : Set a} {P : A → Set p} where

  singleton⁻ : ∀ {x} → All P [ x ] → P x
  singleton⁻ (px ∷ []) = px

------------------------------------------------------------------------
-- fromMaybe

  fromMaybe⁺ : ∀ {mx} → Maybe.All P mx → All P (fromMaybe mx)
  fromMaybe⁺ (just px) = px ∷ []
  fromMaybe⁺ nothing   = []

  fromMaybe⁻ : ∀ mx → All P (fromMaybe mx) → Maybe.All P mx
  fromMaybe⁻ (just x) (px ∷ []) = just px
  fromMaybe⁻ nothing  p         = nothing

------------------------------------------------------------------------
-- replicate

  replicate⁺ : ∀ n {x} → P x → All P (replicate n x)
  replicate⁺ zero    px = []
  replicate⁺ (suc n) px = px ∷ replicate⁺ n px

  replicate⁻ : ∀ {n x} → All P (replicate (suc n) x) → P x
  replicate⁻ (px ∷ _) = px

module _ {a p} {A : Set a} {P : A → Set p} where

------------------------------------------------------------------------
-- inits

  inits⁺ : ∀ {xs} → All P xs → All (All P) (inits xs)
  inits⁺ []         = [] ∷ []
  inits⁺ (px ∷ pxs) = [] ∷ gmap (px ∷_) (inits⁺ pxs)

  inits⁻ : ∀ xs → All (All P) (inits xs) → All P xs
  inits⁻ []               pxs                   = []
  inits⁻ (x ∷ [])         ([] ∷ p[x] ∷ [])      = p[x]
  inits⁻ (x ∷ xs@(_ ∷ _)) ([] ∷ pxs@(p[x] ∷ _)) =
    singleton⁻ p[x] ∷ inits⁻ xs (All.map (drop⁺ 1) (map⁻ pxs))

------------------------------------------------------------------------
-- tails

  tails⁺ : ∀ {xs} → All P xs → All (All P) (tails xs)
  tails⁺ []             = [] ∷ []
  tails⁺ pxxs@(_ ∷ pxs) = pxxs ∷ tails⁺ pxs

  tails⁻ : ∀ xs → All (All P) (tails xs) → All P xs
  tails⁻ []       pxs        = []
  tails⁻ (x ∷ xs) (pxxs ∷ _) = pxxs

------------------------------------------------------------------------
-- all

module _ {a} {A : Set a} (p : A → Bool) where

  all⁺ : ∀ xs → T (all p xs) → All (T ∘ p) xs
  all⁺ []       _     = []
  all⁺ (x ∷ xs) px∷xs with Equivalence.to (T-∧ {p x}) ⟨$⟩ px∷xs
  ... | (px , pxs) = px ∷ all⁺ xs pxs

  all⁻ : ∀ {xs} → All (T ∘ p) xs → T (all p xs)
  all⁻ []         = _
  all⁻ (px ∷ pxs) = Equivalence.from T-∧ ⟨$⟩ (px , all⁻ pxs)

------------------------------------------------------------------------
-- All is anti-monotone.

anti-mono : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
            xs ⊆ ys → All P ys → All P xs
anti-mono xs⊆ys pys = All.tabulate (All.lookup pys ∘ xs⊆ys)

all-anti-mono : ∀ {a} {A : Set a} (p : A → Bool) {xs ys} →
                xs ⊆ ys → T (all p ys) → T (all p xs)
all-anti-mono p xs⊆ys = all⁻ p ∘ anti-mono xs⊆ys ∘ all⁺ p _

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

All-all = all⁻
all-All = all⁺

All-map = map⁺
map-All = map⁻

