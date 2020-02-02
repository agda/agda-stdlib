------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.All.Properties where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Bool.Base using (Bool; T; true; false)
open import Data.Bool.Properties using (T-∧)
open import Data.Empty
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base as List using
  ( List; []; _∷_; [_]; _∷ʳ_; fromMaybe; null; _++_; concat; map; mapMaybe
  ; inits; tails; drop; take; applyUpTo; applyDownFrom; replicate; tabulate
  ; filter; zipWith; all; derun; deduplicate
  )
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All as All using
  ( All; []; _∷_; lookup; updateAt
  ; _[_]=_; here; there
  ; Null
  )
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Binary.Equality.Setoid as ListEq using (_≋_; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All as MAll using (just; nothing)
open import Data.Nat.Base using (zero; suc; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Data.Product as Prod using (_×_; _,_; uncurry; uncurry′)
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Function.Inverse using (_↔_; inverse)
open import Function.Surjection using (_↠_; surjection)
open import Level using (Level)
open import Relation.Binary as B using (REL; Setoid; _Respects_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; _≗_)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary
open import Relation.Nullary.Negation using (¬?; contradiction; decidable-stable)
open import Relation.Unary
  using (Decidable; Pred; Universal) renaming (_⊆_ to _⋐_)

private
  variable
    a b c p q r ℓ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Properties regarding Null

Null⇒null : ∀ {xs : List A} → Null xs → T (null xs)
Null⇒null [] = _

null⇒Null : ∀ {xs : List A} → T (null xs) → Null xs
null⇒Null {xs = []   } _ = []
null⇒Null {xs = _ ∷ _} ()

------------------------------------------------------------------------
-- Properties of the "points-to" relation _[_]=_

module _ {p} {P : Pred A p} where

  -- Relation _[_]=_ is deterministic: each index points to a single value.

  []=-injective : ∀ {x xs} {px qx : P x} {pxs : All P xs} {i : x ∈ xs} →
                  pxs [ i ]= px →
                  pxs [ i ]= qx →
                  px ≡ qx
  []=-injective here          here          = refl
  []=-injective (there x↦px) (there x↦qx) = []=-injective x↦px x↦qx

  -- See also Data.List.Relation.Unary.All.Properties.WithK.[]=-irrelevant.

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
  ... |  true because  [p] = there (¬All⇒Any¬ dec xs (¬∀ ∘ _∷_ (invert [p])))
  ... | false because [¬p] = here (invert [¬p])

  Any¬⇒¬All : ∀ {xs} → Any (¬_ ∘ P) xs → ¬ All P xs
  Any¬⇒¬All (here  ¬p) = ¬p           ∘ All.head
  Any¬⇒¬All (there ¬p) = Any¬⇒¬All ¬p ∘ All.tail

  ¬Any↠All¬ : ∀ {xs} → (¬ Any P xs) ↠ All (¬_ ∘ P) xs
  ¬Any↠All¬ = surjection (¬Any⇒All¬ _) All¬⇒¬Any to∘from
    where
    to∘from : ∀ {xs} (¬p : All (¬_ ∘ P) xs) → ¬Any⇒All¬ xs (All¬⇒¬Any ¬p) ≡ ¬p
    to∘from []         = refl
    to∘from (¬p ∷ ¬ps) = cong₂ _∷_ refl (to∘from ¬ps)

    -- If equality of functions were extensional, then the surjection
    -- could be strengthened to a bijection.

    from∘to : Extensionality _ _ →
              ∀ xs → (¬p : ¬ Any P xs) → All¬⇒¬Any (¬Any⇒All¬ xs ¬p) ≡ ¬p
    from∘to ext []       ¬p = ext λ ()
    from∘to ext (x ∷ xs) ¬p = ext λ
      { (here p)  → refl
      ; (there p) → cong (λ f → f p) $ from∘to ext xs (¬p ∘ there)
      }

  Any¬⇔¬All : ∀ {xs} → Decidable P → Any (¬_ ∘ P) xs ⇔ (¬ All P xs)
  Any¬⇔¬All dec = equivalence Any¬⇒¬All (¬All⇒Any¬ dec _)
    where
    -- If equality of functions were extensional, then the logical
    -- equivalence could be strengthened to a surjection.
    to∘from : Extensionality _ _ →
              ∀ {xs} (¬∀ : ¬ All P xs) → Any¬⇒¬All (¬All⇒Any¬ dec xs ¬∀) ≡ ¬∀
    to∘from ext ¬∀ = ext (⊥-elim ∘ ¬∀)

module _ {_~_ : REL A B ℓ} where

  All-swap : ∀ {xs ys} →
             All (λ x → All (x ~_) ys) xs →
             All (λ y → All (_~ y) xs) ys
  All-swap {ys = []}     _   = []
  All-swap {ys = y ∷ ys} []  = All.universal (λ _ → []) (y ∷ ys)
  All-swap {ys = y ∷ ys} ((x~y ∷ x~ys) ∷ pxs) =
    (x~y ∷ (All.map All.head pxs)) ∷
    All-swap (x~ys ∷ (All.map All.tail pxs))

------------------------------------------------------------------------
-- Defining properties of lookup and _[_]=_
--
-- pxs [ i ]= px  if and only if  lookup pxs i = px.

module _ {P : A → Set p} where

  -- `i` points to `lookup pxs i` in `pxs`.

  []=lookup : ∀ {x xs} (pxs : All P xs) (i : x ∈ xs) →
              pxs [ i ]= lookup pxs i
  []=lookup (px ∷ pxs) (here refl) = here
  []=lookup (px ∷ pxs) (there i)   = there ([]=lookup pxs i)

  -- If `i` points to `px` in `pxs`, then `lookup pxs i ≡ px`.

  []=⇒lookup : ∀ {x xs} {px : P x} {pxs : All P xs} {i : x ∈ xs} →
               pxs [ i ]= px →
               lookup pxs i ≡ px
  []=⇒lookup x↦px = []=-injective ([]=lookup _ _) x↦px

  -- If `lookup pxs i ≡ px`, then `i` points to `px` in `pxs`.

  lookup⇒[]= : ∀{x xs} {px : P x} (pxs : All P xs) (i : x ∈ xs) →
               lookup pxs i ≡ px →
               pxs [ i ]= px
  lookup⇒[]= pxs i refl = []=lookup pxs i

------------------------------------------------------------------------
-- Properties of operations over `All`
------------------------------------------------------------------------
-- map

module _ {P : Pred A p} {Q : Pred A q} {f : P ⋐ Q} where

  map-cong : ∀ {xs} {g : P ⋐ Q} (pxs : All P xs) →
             (∀ {x} → f {x} ≗ g) → All.map f pxs ≡ All.map g pxs
  map-cong []         _   = refl
  map-cong (px ∷ pxs) feq = cong₂ _∷_ (feq px) (map-cong pxs feq)

  map-id : ∀ {xs} (pxs : All P xs) → All.map id pxs ≡ pxs
  map-id []         = refl
  map-id (px ∷ pxs) = cong (px ∷_)  (map-id pxs)

  map-compose : ∀ {r} {R : Pred A r} {xs} {g : Q ⋐ R} (pxs : All P xs) →
                All.map g (All.map f pxs) ≡ All.map (g ∘ f) pxs
  map-compose []         = refl
  map-compose (px ∷ pxs) = cong (_ ∷_) (map-compose pxs)

  lookup-map : ∀ {xs x} (pxs : All P xs) (i : x ∈ xs) →
               lookup (All.map f pxs) i ≡ f (lookup pxs i)
  lookup-map (px ∷ pxs) (here refl) = refl
  lookup-map (px ∷ pxs) (there i)   = lookup-map pxs i

------------------------------------------------------------------------
-- _[_]%=_ / updateAt

module _ {P : Pred A p} where

  -- Defining properties of updateAt:

  -- (+) updateAt actually updates the element at the given index.

  updateAt-updates : ∀ {x xs} (i : x ∈ xs) {f : P x → P x} {px : P x} (pxs : All P xs) →
                     pxs              [ i ]= px →
                     updateAt i f pxs [ i ]= f px
  updateAt-updates (here  refl) (px ∷ pxs) here         = here
  updateAt-updates (there i)    (px ∷ pxs) (there x↦px) =
    there (updateAt-updates i pxs x↦px)

  -- (-) updateAt i does not touch the elements at other indices.

  updateAt-minimal : ∀ {x y xs} (i : x ∈ xs) (j : y ∈ xs) →
                     ∀ {f : P y → P y} {px : P x} (pxs : All P xs) →
                     i ≢∈ j →
                     pxs              [ i ]= px →
                     updateAt j f pxs [ i ]= px
  updateAt-minimal (here .refl) (here refl) (px ∷ pxs) i≢j here        =
    ⊥-elim (i≢j refl refl)
  updateAt-minimal (here .refl) (there j)   (px ∷ pxs) i≢j here        = here
  updateAt-minimal (there i)    (here refl) (px ∷ pxs) i≢j (there val) = there val
  updateAt-minimal (there i)    (there j)   (px ∷ pxs) i≢j (there val) =
    there (updateAt-minimal i j pxs (there-injective-≢∈ i≢j) val)

  -- lookup after updateAt reduces.

  -- For same index this is an easy consequence of updateAt-updates
  -- using []=↔lookup.

  lookup∘updateAt : ∀ {x xs} (pxs : All P xs) (i : x ∈ xs) {f : P x → P x} →
                    lookup (updateAt i f pxs) i ≡ f (lookup pxs i)
  lookup∘updateAt pxs i =
    []=⇒lookup (updateAt-updates i pxs (lookup⇒[]= pxs i refl))

  -- For different indices it easily follows from updateAt-minimal.

  lookup∘updateAt′ : ∀ {x y xs} (i : x ∈ xs) (j : y ∈ xs) →
                     ∀ {f : P y → P y} {px : P x} (pxs : All P xs) →
                     i ≢∈ j →
                     lookup (updateAt j f pxs) i ≡ lookup pxs i
  lookup∘updateAt′ i j pxs i≢j =
    []=⇒lookup (updateAt-minimal i j pxs i≢j (lookup⇒[]= pxs i refl))

  -- The other properties are consequences of (+) and (-).
  -- We spell the most natural properties out.
  -- Direct inductive proofs are in most cases easier than just using
  -- the defining properties.

  -- In the explanations, we make use of shorthand  f = g ↾ x
  -- meaning that f and g agree at point x, i.e.  f x ≡ g x.

  -- updateAt (i : x ∈ xs)  is a morphism
  -- from the monoid of endofunctions  P x → P x
  -- to the monoid of endofunctions  All P xs → All P xs.

  -- 1a. relative identity:  f = id ↾ (lookup pxs i)
  --                implies  updateAt i f = id ↾ pxs

  updateAt-id-relative : ∀ {x xs} (i : x ∈ xs) {f : P x → P x} (pxs : All P xs) →
                         f (lookup pxs i) ≡ lookup pxs i →
                         updateAt i f pxs ≡ pxs
  updateAt-id-relative (here refl)(px ∷ pxs) eq = cong (_∷ pxs) eq
  updateAt-id-relative (there i)  (px ∷ pxs) eq = cong (px ∷_) (updateAt-id-relative i pxs eq)

  -- 1b. identity:  updateAt i id ≗ id

  updateAt-id : ∀ {x xs} (i : x ∈ xs) (pxs : All P xs) →
                updateAt i id pxs ≡ pxs
  updateAt-id i pxs = updateAt-id-relative i pxs refl

  -- 2a. relative composition:  f ∘ g = h ↾ (lookup i pxs)
  --                   implies  updateAt i f ∘ updateAt i g = updateAt i h ↾ pxs

  updateAt-compose-relative : ∀ {x xs} (i : x ∈ xs) {f g h : P x → P x} (pxs : All P xs) →
                              f (g (lookup pxs i)) ≡ h (lookup pxs i) →
                              updateAt i f (updateAt i g pxs) ≡ updateAt i h pxs
  updateAt-compose-relative (here refl) (px ∷ pxs) fg=h = cong (_∷ pxs) fg=h
  updateAt-compose-relative (there i)   (px ∷ pxs) fg=h =
    cong (px ∷_) (updateAt-compose-relative i pxs fg=h)

  -- 2b. composition:  updateAt i f ∘ updateAt i g ≗ updateAt i (f ∘ g)

  updateAt-compose : ∀ {x xs} (i : x ∈ xs) {f g : P x → P x} →
                     updateAt {P = P} i f ∘ updateAt i g ≗ updateAt i (f ∘ g)
  updateAt-compose (here refl) (px ∷ pxs) = refl
  updateAt-compose (there i)   (px ∷ pxs) = cong (px ∷_) (updateAt-compose i pxs)

  -- 3. congruence:  updateAt i  is a congruence wrt. extensional equality.

  -- 3a.  If    f = g ↾ (lookup pxs i)
  --      then  updateAt i f = updateAt i g ↾ pxs

  updateAt-cong-relative : ∀ {x xs} (i : x ∈ xs) {f g : P x → P x} (pxs : All P xs) →
                           f (lookup pxs i) ≡ g (lookup pxs i) →
                           updateAt i f pxs ≡ updateAt i g pxs
  updateAt-cong-relative (here refl) (px ∷ pxs) f=g = cong (_∷ pxs) f=g
  updateAt-cong-relative (there i)   (px ∷ pxs) f=g = cong (px ∷_) (updateAt-cong-relative i pxs f=g)

  -- 3b. congruence:  f ≗ g → updateAt i f ≗ updateAt i g

  updateAt-cong : ∀ {x xs} (i : x ∈ xs) {f g : P x → P x} →
                  f ≗ g →
                  updateAt i f ≗ updateAt i g
  updateAt-cong i f≗g pxs = updateAt-cong-relative i pxs (f≗g (lookup pxs i))


  -- The order of updates at different indices i ≢ j does not matter.

  -- This a consequence of updateAt-updates and updateAt-minimal
  -- but easier to prove inductively.

  updateAt-commutes : ∀ {x y xs} (i : x ∈ xs) (j : y ∈ xs) →
                      ∀ {f : P x → P x} {g : P y → P y} →
                      i ≢∈ j →
                      updateAt i f ∘ updateAt j g ≗ updateAt j g ∘ updateAt i f
  updateAt-commutes (here refl) (here refl) i≢j (px ∷ pxs) =
    ⊥-elim (i≢j refl refl)
  updateAt-commutes (here refl) (there j)   i≢j (px ∷ pxs) = refl
  updateAt-commutes (there i)   (here refl) i≢j (px ∷ pxs) = refl
  updateAt-commutes (there i)   (there j)   i≢j (px ∷ pxs) =
    cong (px ∷_) (updateAt-commutes i j (there-injective-≢∈ i≢j) pxs)

module _ {P : Pred A p} {Q : Pred A q} where

  map-updateAt : ∀ {x xs} {f : P ⋐ Q} {g : P x → P x} {h : Q x → Q x}
                 (pxs : All P xs) (i : x ∈ xs) →
                 f (g (lookup pxs i)) ≡ h (f (lookup pxs i)) →
                 All.map f (pxs All.[ i ]%= g) ≡ (All.map f pxs) All.[ i ]%= h
  map-updateAt (px ∷ pxs) (here refl) = cong (_∷ _)
  map-updateAt (px ∷ pxs) (there i) feq = cong (_ ∷_) (map-updateAt pxs i feq)

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
    ++⁺∘++⁻ []       p          = refl
    ++⁺∘++⁻ (x ∷ xs) (px ∷ pxs) = cong (_∷_ px) $ ++⁺∘++⁻ xs pxs

    ++⁻∘++⁺ : ∀ {xs ys} (p : All P xs × All P ys) →
              ++⁻ xs (uncurry ++⁺ p) ≡ p
    ++⁻∘++⁺ ([]       , pys) = refl
    ++⁻∘++⁺ (px ∷ pxs , pys) rewrite ++⁻∘++⁺ (pxs , pys) = refl

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
  ... |  true because [Px] = invert [Px] ∷ all-filter xs
  ... | false because  _   = all-filter xs

module _ {P : A → Set p} {Q : A → Set q} (P? : Decidable P) where

  filter⁺ : ∀ {xs} → All Q xs → All Q (filter P? xs)
  filter⁺ {xs = _}     [] = []
  filter⁺ {xs = x ∷ _} (Qx ∷ Qxs) with does (P? x)
  ... | false = filter⁺ Qxs
  ... | true  = Qx ∷ filter⁺ Qxs

  filter⁻ : ∀ {xs} → All Q (filter P? xs) → All Q (filter (¬? ∘ P?) xs) → All Q xs
  filter⁻ {[]}         []          []                           = []
  filter⁻ {x ∷ xs}       all⁺        all⁻ with P? x  | ¬? (P? x)
  filter⁻ {x ∷ xs}       all⁺        all⁻  | yes  Px | yes  ¬Px = contradiction Px ¬Px
  filter⁻ {x ∷ xs} (qx ∷ all⁺)       all⁻  | yes  Px | no  ¬¬Px = qx ∷ filter⁻ all⁺ all⁻
  filter⁻ {x ∷ xs}       all⁺  (qx ∷ all⁻) | no    _ | yes  ¬Px = qx ∷ filter⁻ all⁺ all⁻
  filter⁻ {x ∷ xs}       all⁺        all⁻  | no  ¬Px | no  ¬¬Px = contradiction ¬Px ¬¬Px

------------------------------------------------------------------------
-- derun and deduplicate

module _ {P : A → Set p} {R : A → A → Set q} (R? : B.Decidable R) where

  derun⁺ : ∀ {xs} → All P xs → All P (derun R? xs)
  derun⁺ {[]} [] = []
  derun⁺ {x ∷ []} (px ∷ []) = px ∷ []
  derun⁺ {x ∷ y ∷ xs} (px ∷ all[P,y∷xs]) with does (R? x y)
  ... | false = px ∷ derun⁺ all[P,y∷xs]
  ... | true  = derun⁺ all[P,y∷xs]

  deduplicate⁺ : ∀ {xs} → All P xs → All P (deduplicate R? xs)
  deduplicate⁺ [] = []
  deduplicate⁺ {x ∷ _} (px ∷ all[P,xs]) = px ∷ filter⁺ (¬? ∘ R? x) (deduplicate⁺ all[P,xs])

  derun⁻ : P B.Respects (flip R) → ∀ xs → All P (derun R? xs) → All P xs
  derun⁻ P-resp-R []       []          = []
  derun⁻ P-resp-R (x ∷ xs) all[P,x∷xs] = aux x xs all[P,x∷xs] where
    aux : ∀ x xs → All P (derun R? (x ∷ xs)) → All P (x ∷ xs)
    aux x []       (px ∷ []) = px ∷ []
    aux x (y ∷ xs) all[P,x∷y∷xs] with R? x y
    aux x (y ∷ xs) all[P,y∷xs]        | yes Rxy with aux y xs all[P,y∷xs]
    aux x (y ∷ xs) all[P,y∷xs]        | yes Rxy | r@(py ∷ _) = P-resp-R Rxy py ∷ r
    aux x (y ∷ xs) (px ∷ all[P,y∷xs]) | no _ = px ∷ aux y xs all[P,y∷xs]

  module _ (P-resp-R : P B.Respects R) where

    deduplicate⁻ : ∀ xs → All P (deduplicate R? xs) → All P xs
    deduplicate⁻ [] [] = []
    deduplicate⁻ (x ∷ xs) (px ∷ app[P,dedup[xs]]) = px ∷ deduplicate⁻ xs (filter⁻ (¬? ∘ R? x) app[P,dedup[xs]] (All.tabulate aux)) where
      aux : ∀ {z} → z ∈ filter (¬? ∘ ¬? ∘ R? x) (deduplicate R? xs) → P z
      aux {z} z∈filter = P-resp-R (decidable-stable (R? x z) (Prod.proj₂ (∈-filter⁻ (¬? ∘ ¬? ∘ R? x) {z} {deduplicate R? xs} z∈filter))) px

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
anti-mono xs⊆ys pys = All.tabulate (lookup pys ∘ xs⊆ys)

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

-- Version 1.3

Any¬→¬All = Any¬⇒¬All
{-# WARNING_ON_USAGE Any¬→¬All
"Warning: Any¬→¬All was deprecated in v1.3.
Please use Any¬⇒¬All instead."
#-}
