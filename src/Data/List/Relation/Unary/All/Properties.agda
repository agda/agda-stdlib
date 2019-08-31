------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.All.Properties where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Bool.Base using (Bool; T)
open import Data.Bool.Properties using (T-∧)
open import Data.Empty
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Binary.Equality.Setoid as ListEq using (_≋_; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All as MAll using (just; nothing)
open import Data.Nat using (zero; suc; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Data.Product as Prod using (_×_; _,_; uncurry; uncurry′)
open import Function.Core
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Function.Inverse using (_↔_; inverse)
open import Function.Surjection using (_↠_; surjection)
open import Level using (Level)
open import Relation.Binary using (REL; Setoid; _Respects_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Unary
  using (Decidable; Pred; Universal) renaming (_⊆_ to _⋐_)

private
  variable
    a b c p q ℓ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Lemmas relating Any, All and negation.

module _ {P : A → Set p} where

  ¬Any⇒All¬ : ∀ xs → ¬ Any P xs → All (¬_ ∘ P) xs
  ¬Any⇒All¬ []       ¬p = []
  ¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ∷ ¬Any⇒All¬ xs (¬p ∘ there)

  All¬⇒¬Any : ∀ {xs} → All (¬_ ∘ P) xs → ¬ Any P xs
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

    from∘to : Extensionality _ _ →
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
    to∘from : Extensionality _ _ →
              ∀ {xs} (¬∀ : ¬ All P xs) → Any¬→¬All (¬All⇒Any¬ dec xs ¬∀) ≡ ¬∀
    to∘from ext ¬∀ = ext (⊥-elim ∘ ¬∀)

module _ {_~_ : REL (List A) B ℓ} where

  All-swap : ∀ {xss ys} →
             All (λ xs → All (xs ~_) ys) xss →
             All (λ y → All (_~ y) xss) ys
  All-swap {ys = []}     _   = []
  All-swap {ys = y ∷ ys} []  = All.universal (λ _ → []) (y ∷ ys)
  All-swap {ys = y ∷ ys} ((x~y ∷ x~ys) ∷ pxss) =
    (x~y ∷ (All.map All.head pxss)) ∷
    All-swap (x~ys ∷ (All.map All.tail pxss))

------------------------------------------------------------------------
-- Properties of operations over `All`
------------------------------------------------------------------------
-- map

module _ {P : Pred A p} {Q : Pred A q} {f : P ⋐ Q} where

  map-cong : ∀ {xs} {g : P ⋐ Q} (ps : All P xs) →
             (∀ {x} → f {x} P.≗ g) → All.map f ps ≡ All.map g ps
  map-cong []        _   = P.refl
  map-cong (px ∷ ps) feq = P.cong₂ _∷_ (feq px) (map-cong ps feq)

  map-id : ∀ {xs} (ps : All P xs) → All.map id ps ≡ ps
  map-id []        = P.refl
  map-id (px ∷ ps) = P.cong (px ∷_)  (map-id ps)

  map-compose : ∀ {r} {R : Pred A r} {xs} {g : Q ⋐ R} (ps : All P xs) →
                All.map g (All.map f ps) ≡ All.map (g ∘ f) ps
  map-compose []        = P.refl
  map-compose (px ∷ ps) = P.cong (_ ∷_) (map-compose ps)

  lookup-map : ∀ {xs x} (ps : All P xs) (i : x ∈ xs) →
               All.lookup (All.map f ps) i ≡ f (All.lookup ps i)
  lookup-map (px ∷ pxs) (here P.refl) = P.refl
  lookup-map (px ∷ pxs) (there i) = lookup-map pxs i

------------------------------------------------------------------------
-- _[_]%=_/updateAt

module _ {P : Pred A p} where

  updateAt-updates : ∀ {x xs px} (pxs : All P xs) (i : x ∈ xs)
                     {f : P x → P x} → All.lookup pxs i ≡ px →
                     All.lookup (pxs All.[ i ]%= f) i ≡ f px
  updateAt-updates (px ∷ pxs) (here P.refl) P.refl = P.refl
  updateAt-updates (px ∷ pxs) (there i) = updateAt-updates pxs i

  updateAt-cong : ∀ {x xs} (pxs : All P xs) (i : x ∈ xs)
                  {f g : P x → P x} →
                  f (All.lookup pxs i) ≡ g (All.lookup pxs i) →
                  (pxs All.[ i ]%= f) ≡ (pxs All.[ i ]%= g)
  updateAt-cong (px ∷ pxs) (here P.refl)     = P.cong (_∷ pxs)
  updateAt-cong (px ∷ pxs) (there i)     f≗g = P.cong (px ∷_) (updateAt-cong pxs i f≗g)

  updateAt-id : ∀ {x xs} (pxs : All P xs) (i : x ∈ xs) →
                (pxs All.[ i ]%= id) ≡ pxs
  updateAt-id (px ∷ pxs) (here P.refl) = P.refl
  updateAt-id (px ∷ pxs) (there i)     = P.cong (px ∷_) (updateAt-id pxs i)

  updateAt-compose : ∀ {x xs} (pxs : All P xs) (i : x ∈ xs) {f g : P x → P x} →
                     (pxs All.[ i ]%= f All.[ i ]%= g) ≡ pxs All.[ i ]%= (g ∘ f)
  updateAt-compose (px ∷ pxs) (here P.refl) = P.refl
  updateAt-compose (px ∷ pxs) (there i)     = P.cong (px ∷_) (updateAt-compose pxs i)

module _ {P : Pred A p} {Q : Pred A q} where

  map-updateAt : ∀ {x xs} {f : P ⋐ Q} {g : P x → P x} {h : Q x → Q x}
                 (pxs : All P xs) (i : x ∈ xs) →
                 f (g (All.lookup pxs i)) ≡ h (f (All.lookup pxs i)) →
                 All.map f (pxs All.[ i ]%= g) ≡ (All.map f pxs) All.[ i ]%= h
  map-updateAt (px ∷ pxs) (here P.refl) = P.cong (_∷ _)
  map-updateAt (px ∷ pxs) (there i) feq = P.cong (_ ∷_) (map-updateAt pxs i feq)

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- map

module _ {P : B → Set p} {f : A → B} where

  map⁺ : ∀ {xs} → All (P ∘ f) xs → All P (map f xs)
  map⁺ []       = []
  map⁺ (p ∷ ps) = p ∷ map⁺ ps

  map⁻ : ∀ {xs} → All P (map f xs) → All (P ∘ f) xs
  map⁻ {xs = []}    []       = []
  map⁻ {xs = _ ∷ _} (p ∷ ps) = p ∷ map⁻ ps

-- A variant of All.map.

module _ {P : A → Set p} {Q : B → Set q} {f : A → B} where

  gmap : P ⋐ Q ∘ f → All P ⋐ All Q ∘ map f
  gmap g = map⁺ ∘ All.map g

------------------------------------------------------------------------
-- mapMaybe

module _ (P : B → Set p) {f : A → Maybe B} where

  mapMaybe⁺ : ∀ {xs} → All (MAll.All P) (map f xs) → All P (mapMaybe f xs)
  mapMaybe⁺ {[]}     [] = []
  mapMaybe⁺ {x ∷ xs} (px ∷ pxs) with f x
  ... | nothing = mapMaybe⁺ pxs
  ... | just v with px
  ...   | just pv = pv ∷ mapMaybe⁺ pxs

------------------------------------------------------------------------
-- _++_

module _ {P : A → Set p} where

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

module _ {P : A → Set p} where

  concat⁺ : ∀ {xss} → All (All P) xss → All P (concat xss)
  concat⁺ []           = []
  concat⁺ (pxs ∷ pxss) = ++⁺ pxs (concat⁺ pxss)

  concat⁻ : ∀ {xss} → All P (concat xss) → All (All P) xss
  concat⁻ {[]}       []  = []
  concat⁻ {xs ∷ xss} pxs = ++⁻ˡ xs pxs ∷ concat⁻ (++⁻ʳ xs pxs)

------------------------------------------------------------------------
-- take and drop

module _ {P : A → Set p} where

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

module _ {P : A → Set p} where

  applyUpTo⁺₁ : ∀ f n → (∀ {i} → i < n → P (f i)) → All P (applyUpTo f n)
  applyUpTo⁺₁ f zero    Pf = []
  applyUpTo⁺₁ f (suc n) Pf = Pf (s≤s z≤n) ∷ applyUpTo⁺₁ (f ∘ suc) n (Pf ∘ s≤s)

  applyUpTo⁺₂ : ∀ f n → (∀ i → P (f i)) → All P (applyUpTo f n)
  applyUpTo⁺₂ f n Pf = applyUpTo⁺₁ f n (λ _ → Pf _)

  applyUpTo⁻ : ∀ f n → All P (applyUpTo f n) → ∀ {i} → i < n → P (f i)
  applyUpTo⁻ f (suc n) (px ∷ _)   (s≤s z≤n)       = px
  applyUpTo⁻ f (suc n) (_  ∷ pxs) (s≤s (s≤s i<n)) =
    applyUpTo⁻ (f ∘ suc) n pxs (s≤s i<n)

------------------------------------------------------------------------
-- applyDownFrom

module _ {P : A → Set p} where

  applyDownFrom⁺₁ : ∀ f n → (∀ {i} → i < n → P (f i)) → All P (applyDownFrom f n)
  applyDownFrom⁺₁ f zero    Pf = []
  applyDownFrom⁺₁ f (suc n) Pf = Pf ≤-refl ∷ applyDownFrom⁺₁ f n (Pf ∘ ≤-step)

  applyDownFrom⁺₂ : ∀ f n → (∀ i → P (f i)) → All P (applyDownFrom f n)
  applyDownFrom⁺₂ f n Pf = applyDownFrom⁺₁ f n (λ _ → Pf _)

------------------------------------------------------------------------
-- tabulate

module _ {P : A → Set p} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} →
              (∀ i → P (f i)) → All P (tabulate f)
  tabulate⁺ {zero}  Pf = []
  tabulate⁺ {suc n} Pf = Pf fzero ∷ tabulate⁺ (Pf ∘ fsuc)

  tabulate⁻ : ∀ {n} {f : Fin n → A} →
              All P (tabulate f) → (∀ i → P (f i))
  tabulate⁻ {suc n} (px ∷ _) fzero    = px
  tabulate⁻ {suc n} (_ ∷ pf) (fsuc i) = tabulate⁻ pf i

------------------------------------------------------------------------
-- remove

module _ {P : A → Set p} {Q : A → Set q} where

  ─⁺ : ∀ {xs} (p : Any P xs) → All Q xs → All Q (xs Any.─ p)
  ─⁺ (here px) (_ ∷ qs) = qs
  ─⁺ (there p) (q ∷ qs) = q ∷ ─⁺ p qs

  ─⁻ : ∀ {xs} (p : Any P xs) → Q (Any.lookup p) → All Q (xs Any.─ p) → All Q xs
  ─⁻ (here px) q qs        = q ∷ qs
  ─⁻ (there p) q (q′ ∷ qs) = q′ ∷ ─⁻ p q qs

------------------------------------------------------------------------
-- filter

module _ {P : A → Set p} (P? : Decidable P) where

  all-filter : ∀ xs → All P (filter P? xs)
  all-filter []       = []
  all-filter (x ∷ xs) with P? x
  ... | yes Px = Px ∷ all-filter xs
  ... | no  _  = all-filter xs

module _ {P : A → Set p} {Q : A → Set q} (P? : Decidable P) where

  filter⁺ : ∀ {xs} → All Q xs → All Q (filter P? xs)
  filter⁺ {xs = _}     [] = []
  filter⁺ {xs = x ∷ _} (Qx ∷ Qxs) with P? x
  ... | no  _ = filter⁺ Qxs
  ... | yes _ = Qx ∷ filter⁺ Qxs

------------------------------------------------------------------------
-- zipWith

module _ (P : C → Set p) (f : A → B → C) where

  zipWith⁺ : ∀ {xs ys} → Pointwise (λ x y → P (f x y)) xs ys →
             All P (zipWith f xs ys)
  zipWith⁺ []              = []
  zipWith⁺ (Pfxy ∷ Pfxsys) = Pfxy ∷ zipWith⁺ Pfxsys

------------------------------------------------------------------------
-- Operations for constructing lists
------------------------------------------------------------------------
-- singleton

module _ {P : A → Set p} where

  singleton⁻ : ∀ {x} → All P [ x ] → P x
  singleton⁻ (px ∷ []) = px

------------------------------------------------------------------------
-- snoc

module _ {P : A → Set p} {x xs} where

  ∷ʳ⁺ : All P xs → P x → All P (xs ∷ʳ x)
  ∷ʳ⁺ pxs px = ++⁺ pxs (px ∷ [])

  ∷ʳ⁻ : All P (xs ∷ʳ x) → All P xs × P x
  ∷ʳ⁻ pxs = Prod.map₂ singleton⁻ $ ++⁻ xs pxs

------------------------------------------------------------------------
-- fromMaybe

module _ {P : A → Set p} where

  fromMaybe⁺ : ∀ {mx} → MAll.All P mx → All P (fromMaybe mx)
  fromMaybe⁺ (just px) = px ∷ []
  fromMaybe⁺ nothing   = []

  fromMaybe⁻ : ∀ mx → All P (fromMaybe mx) → MAll.All P mx
  fromMaybe⁻ (just x) (px ∷ []) = just px
  fromMaybe⁻ nothing  p         = nothing

------------------------------------------------------------------------
-- replicate

module _ {P : A → Set p} where

  replicate⁺ : ∀ n {x} → P x → All P (replicate n x)
  replicate⁺ zero    px = []
  replicate⁺ (suc n) px = px ∷ replicate⁺ n px

  replicate⁻ : ∀ {n x} → All P (replicate (suc n) x) → P x
  replicate⁻ (px ∷ _) = px

------------------------------------------------------------------------
-- inits

module _ {P : A → Set p} where

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

module _ {P : A → Set p} where

  tails⁺ : ∀ {xs} → All P xs → All (All P) (tails xs)
  tails⁺ []             = [] ∷ []
  tails⁺ pxxs@(_ ∷ pxs) = pxxs ∷ tails⁺ pxs

  tails⁻ : ∀ xs → All (All P) (tails xs) → All P xs
  tails⁻ []       pxs        = []
  tails⁻ (x ∷ xs) (pxxs ∷ _) = pxxs

------------------------------------------------------------------------
-- all

module _ (p : A → Bool) where

  all⁺ : ∀ xs → T (all p xs) → All (T ∘ p) xs
  all⁺ []       _     = []
  all⁺ (x ∷ xs) px∷xs with Equivalence.to (T-∧ {p x}) ⟨$⟩ px∷xs
  ... | (px , pxs) = px ∷ all⁺ xs pxs

  all⁻ : ∀ {xs} → All (T ∘ p) xs → T (all p xs)
  all⁻ []         = _
  all⁻ (px ∷ pxs) = Equivalence.from T-∧ ⟨$⟩ (px , all⁻ pxs)

------------------------------------------------------------------------
-- All is anti-monotone.

anti-mono : ∀ {P : A → Set p} {xs ys} → xs ⊆ ys → All P ys → All P xs
anti-mono xs⊆ys pys = All.tabulate (All.lookup pys ∘ xs⊆ys)

all-anti-mono : ∀ (p : A → Bool) {xs ys} →
                xs ⊆ ys → T (all p ys) → T (all p xs)
all-anti-mono p xs⊆ys = all⁻ p ∘ anti-mono xs⊆ys ∘ all⁺ p _

------------------------------------------------------------------------
-- Interactions with pointwise equality
------------------------------------------------------------------------

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S
  open ListEq S

  respects : {P : Pred Carrier p} → P Respects _≈_ → (All P) Respects _≋_
  respects p≈ []            []         = []
  respects p≈ (x≈y ∷ xs≈ys) (px ∷ pxs) = p≈ x≈y px ∷ respects p≈ xs≈ys pxs


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.16

All-all = all⁻
{-# WARNING_ON_USAGE All-all
"Warning: All-all was deprecated in v0.16.
Please use all⁻ instead."
#-}
all-All = all⁺
{-# WARNING_ON_USAGE all-All
"Warning: all-All was deprecated in v0.16.
Please use all⁺ instead."
#-}
All-map = map⁺
{-# WARNING_ON_USAGE All-map
"Warning: All-map was deprecated in v0.16.
Please use map⁺ instead."
#-}
map-All = map⁻
{-# WARNING_ON_USAGE map-All
"Warning: map-All was deprecated in v0.16.
Please use map⁻ instead."
#-}

-- Version 1.0

filter⁺₁ = all-filter
{-# WARNING_ON_USAGE filter⁺₁
"Warning: filter⁺₁ was deprecated in v1.0.
Please use all-filter instead."
#-}
filter⁺₂ = filter⁺
{-# WARNING_ON_USAGE filter⁺₂
"Warning: filter⁺₂ was deprecated in v1.0.
Please use filter⁺ instead."
#-}
