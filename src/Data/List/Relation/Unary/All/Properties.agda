------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.All.Properties where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Bool.Base using (Bool; T; true; false)
open import Data.Bool.Properties using (T-∧)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base as List hiding (lookup; updateAt)
open import Data.List.Membership.Propositional using (_∈_; _≢∈_)
open import Data.List.Membership.Propositional.Properties
  using (there-injective-≢∈; ∈-filter⁻)
import Data.List.Membership.Setoid as SetoidMembership
import Data.List.Properties as List
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.All as All using
  ( All; []; _∷_; lookup; updateAt
  ; _[_]=_; here; there
  ; Null
  )
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All as Maybe using (just; nothing; fromAny)
open import Data.Maybe.Relation.Unary.Any as Maybe using (just)
open import Data.Nat.Base using (zero; suc; s≤s; _<_; z<s; s<s)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
open import Data.Product.Base as Product using (_×_; _,_; uncurry; uncurry′)
open import Function.Base using (_∘_; _$_; id; case_of_; flip)
open import Function.Bundles using (_↠_; mk↠ₛ; _⇔_; mk⇔; _↔_; mk↔ₛ′; Equivalence)
open import Level using (Level)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Definitions as B
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂; _≗_)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Decidable
  using (Dec; does; yes; no; _because_; ¬?; decidable-stable)
open import Relation.Unary
  using (Decidable; Pred; Universal; ∁; _∩_; _⟨×⟩_) renaming (_⊆_ to _⋐_)
open import Relation.Unary.Properties using (∁?)

private
  variable
    a b c p q r ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b
    C : Set c
    P : Pred A p
    Q : Pred B q
    R : Pred C r
    x y : A
    xs ys : List A

------------------------------------------------------------------------
-- Properties regarding Null

Null⇒null : Null xs → T (null xs)
Null⇒null [] = _

null⇒Null : T (null xs) → Null xs
null⇒Null {xs = []   } _ = []
null⇒Null {xs = _ ∷ _} ()

------------------------------------------------------------------------
-- Properties of the "points-to" relation _[_]=_

-- Relation _[_]=_ is deterministic: each index points to a single value.

[]=-injective : ∀ {px qx : P x} {pxs : All P xs} {i : x ∈ xs} →
                pxs [ i ]= px →
                pxs [ i ]= qx →
                px ≡ qx
[]=-injective here          here          = refl
[]=-injective (there x↦px) (there x↦qx) = []=-injective x↦px x↦qx

-- See also Data.List.Relation.Unary.All.Properties.WithK.[]=-irrelevant.

------------------------------------------------------------------------
-- Lemmas relating Any, All and negation.

¬Any⇒All¬ : ∀ xs → ¬ Any P xs → All (¬_ ∘ P) xs
¬Any⇒All¬ []       ¬p = []
¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ∷ ¬Any⇒All¬ xs (¬p ∘ there)

All¬⇒¬Any : ∀ {xs} → All (¬_ ∘ P) xs → ¬ Any P xs
All¬⇒¬Any (¬p ∷ _)  (here  p) = ¬p p
All¬⇒¬Any (_  ∷ ¬p) (there p) = All¬⇒¬Any ¬p p

¬All⇒Any¬ : Decidable P → ∀ xs → ¬ All P xs → Any (¬_ ∘ P) xs
¬All⇒Any¬ dec []       ¬∀ = contradiction [] ¬∀
¬All⇒Any¬ dec (x ∷ xs) ¬∀ with dec x
... |  true because  [p] = there (¬All⇒Any¬ dec xs (¬∀ ∘ _∷_ (invert [p])))
... | false because [¬p] = here (invert [¬p])

Any¬⇒¬All : ∀ {xs} → Any (¬_ ∘ P) xs → ¬ All P xs
Any¬⇒¬All (here  ¬p) = ¬p           ∘ All.head
Any¬⇒¬All (there ¬p) = Any¬⇒¬All ¬p ∘ All.tail

¬Any↠All¬ : ∀ {xs} → (¬ Any P xs) ↠ All (¬_ ∘ P) xs
¬Any↠All¬ = mk↠ₛ {to = ¬Any⇒All¬ _} (λ y → All¬⇒¬Any y , to∘from y)
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
Any¬⇔¬All dec = mk⇔ Any¬⇒¬All (¬All⇒Any¬ dec _)

private
  -- If equality of functions were extensional, then the logical
  -- equivalence could be strengthened to a surjection.
  to∘from : Extensionality _ _ → (dec : Decidable P) →
            (¬∀ : ¬ All P xs) → Any¬⇒¬All (¬All⇒Any¬ dec xs ¬∀) ≡ ¬∀
  to∘from ext P ¬∀ = ext λ ∀P → contradiction ∀P ¬∀

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

-- `i` points to `lookup pxs i` in `pxs`.

[]=lookup : (pxs : All P xs) (i : x ∈ xs) →
            pxs [ i ]= lookup pxs i
[]=lookup (px ∷ pxs) (here refl) = here
[]=lookup (px ∷ pxs) (there i)   = there ([]=lookup pxs i)

-- If `i` points to `px` in `pxs`, then `lookup pxs i ≡ px`.

[]=⇒lookup : ∀ {px : P x} {pxs : All P xs} {i : x ∈ xs} →
             pxs [ i ]= px →
             lookup pxs i ≡ px
[]=⇒lookup x↦px = []=-injective ([]=lookup _ _) x↦px

-- If `lookup pxs i ≡ px`, then `i` points to `px` in `pxs`.

lookup⇒[]= : ∀ {px : P x} (pxs : All P xs) (i : x ∈ xs) →
             lookup pxs i ≡ px →
             pxs [ i ]= px
lookup⇒[]= pxs i refl = []=lookup pxs i

------------------------------------------------------------------------
-- Properties of operations over `All`
------------------------------------------------------------------------
-- map

map-cong : ∀ {f : P ⋐ Q} {g : P ⋐ Q} (pxs : All P xs) →
           (∀ {x} → f {x} ≗ g) → All.map f pxs ≡ All.map g pxs
map-cong []         _   = refl
map-cong (px ∷ pxs) feq = cong₂ _∷_ (feq px) (map-cong pxs feq)

map-id : ∀ (pxs : All P xs) → All.map id pxs ≡ pxs
map-id []         = refl
map-id (px ∷ pxs) = cong (px ∷_)  (map-id pxs)

map-∘ : ∀ {f : P ⋐ Q} {g : Q ⋐ R} (pxs : All P xs) →
        All.map g (All.map f pxs) ≡ All.map (g ∘ f) pxs
map-∘ []         = refl
map-∘ (px ∷ pxs) = cong (_ ∷_) (map-∘ pxs)

lookup-map : ∀ {f : P ⋐ Q} (pxs : All P xs) (i : x ∈ xs) →
             lookup (All.map f pxs) i ≡ f (lookup pxs i)
lookup-map (px ∷ pxs) (here refl) = refl
lookup-map (px ∷ pxs) (there i)   = lookup-map pxs i

------------------------------------------------------------------------
-- _[_]%=_ / updateAt

  -- Defining properties of updateAt:

-- (+) updateAt actually updates the element at the given index.

updateAt-updates : ∀ (i : x ∈ xs) {f : P x → P x} {px : P x} (pxs : All P xs) →
                   pxs              [ i ]= px →
                   updateAt i f pxs [ i ]= f px
updateAt-updates (here  refl) (px ∷ pxs) here         = here
updateAt-updates (there i)    (px ∷ pxs) (there x↦px) =
  there (updateAt-updates i pxs x↦px)

-- (-) updateAt i does not touch the elements at other indices.

updateAt-minimal : ∀ (i : x ∈ xs) (j : y ∈ xs) →
                   ∀ {f : P y → P y} {px : P x} (pxs : All P xs) →
                   i ≢∈ j →
                   pxs              [ i ]= px →
                   updateAt j f pxs [ i ]= px
updateAt-minimal (here .refl) (here refl) (px ∷ pxs) i≢j here        =
  contradiction refl (i≢j refl)
updateAt-minimal (here .refl) (there j)   (px ∷ pxs) i≢j here        = here
updateAt-minimal (there i)    (here refl) (px ∷ pxs) i≢j (there val) = there val
updateAt-minimal (there i)    (there j)   (px ∷ pxs) i≢j (there val) =
  there (updateAt-minimal i j pxs (there-injective-≢∈ i≢j) val)

-- lookup after updateAt reduces.

-- For same index this is an easy consequence of updateAt-updates
-- using []=↔lookup.

lookup∘updateAt : ∀ (pxs : All P xs) (i : x ∈ xs) {f : P x → P x} →
                  lookup (updateAt i f pxs) i ≡ f (lookup pxs i)
lookup∘updateAt pxs i =
  []=⇒lookup (updateAt-updates i pxs (lookup⇒[]= pxs i refl))

-- For different indices it easily follows from updateAt-minimal.

lookup∘updateAt′ : ∀ (i : x ∈ xs) (j : y ∈ xs) →
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
-- meaning that f and g agree locally at point x, i.e.  f x ≡ g x.

-- updateAt (i : x ∈ xs)  is a morphism
-- from the monoid of endofunctions  P x → P x
-- to the monoid of endofunctions  All P xs → All P xs.

-- 1a. local identity:  f = id ↾ (lookup pxs i)
--             implies  updateAt i f = id ↾ pxs

updateAt-id-local : ∀ (i : x ∈ xs) {f : P x → P x} (pxs : All P xs) →
                    f (lookup pxs i) ≡ lookup pxs i →
                    updateAt i f pxs ≡ pxs
updateAt-id-local (here refl)(px ∷ pxs) eq = cong (_∷ pxs) eq
updateAt-id-local (there i)  (px ∷ pxs) eq = cong (px ∷_) (updateAt-id-local i pxs eq)

-- 1b. identity:  updateAt i id ≗ id

updateAt-id : ∀ (i : x ∈ xs) (pxs : All P xs) → updateAt i id pxs ≡ pxs
updateAt-id i pxs = updateAt-id-local i pxs refl

-- 2a. relative composition:  f ∘ g = h ↾ (lookup i pxs)
--                   implies  updateAt i f ∘ updateAt i g = updateAt i h ↾ pxs

updateAt-∘-local : ∀ (i : x ∈ xs) {f g h : P x → P x} (pxs : All P xs) →
                   f (g (lookup pxs i)) ≡ h (lookup pxs i) →
                   updateAt i f (updateAt i g pxs) ≡ updateAt i h pxs
updateAt-∘-local (here refl) (px ∷ pxs) fg=h = cong (_∷ pxs) fg=h
updateAt-∘-local (there i)   (px ∷ pxs) fg=h = cong (px ∷_) (updateAt-∘-local i pxs fg=h)

-- 2b. composition:  updateAt i f ∘ updateAt i g ≗ updateAt i (f ∘ g)

updateAt-∘ : ∀ (i : x ∈ xs) {f g : P x → P x} →
             updateAt {P = P} i f ∘ updateAt i g ≗ updateAt i (f ∘ g)
updateAt-∘ i pxs = updateAt-∘-local i pxs refl

-- 3. congruence:  updateAt i  is a congruence wrt. extensional equality.

-- 3a.  If    f = g ↾ (lookup pxs i)
--      then  updateAt i f = updateAt i g ↾ pxs

updateAt-cong-local : ∀ (i : x ∈ xs) {f g : P x → P x} (pxs : All P xs) →
                      f (lookup pxs i) ≡ g (lookup pxs i) →
                      updateAt i f pxs ≡ updateAt i g pxs
updateAt-cong-local (here refl) (px ∷ pxs) f=g = cong (_∷ pxs) f=g
updateAt-cong-local (there i)   (px ∷ pxs) f=g = cong (px ∷_) (updateAt-cong-local i pxs f=g)

-- 3b. congruence:  f ≗ g → updateAt i f ≗ updateAt i g

updateAt-cong : ∀ (i : x ∈ xs) {f g : P x → P x} →
                f ≗ g → updateAt {P = P} i f ≗ updateAt i g
updateAt-cong i f≗g pxs = updateAt-cong-local i pxs (f≗g (lookup pxs i))

-- The order of updates at different indices i ≢ j does not matter.

-- This a consequence of updateAt-updates and updateAt-minimal
-- but easier to prove inductively.

updateAt-commutes : ∀ (i : x ∈ xs) (j : y ∈ xs) →
                    ∀ {f : P x → P x} {g : P y → P y} →
                    i ≢∈ j →
                    updateAt {P = P} i f ∘ updateAt j g ≗ updateAt j g ∘ updateAt i f
updateAt-commutes (here refl) (here refl) i≢j (px ∷ pxs) =
  contradiction refl (i≢j refl)
updateAt-commutes (here refl) (there j)   i≢j (px ∷ pxs) = refl
updateAt-commutes (there i)   (here refl) i≢j (px ∷ pxs) = refl
updateAt-commutes (there i)   (there j)   i≢j (px ∷ pxs) =
  cong (px ∷_) (updateAt-commutes i j (there-injective-≢∈ i≢j) pxs)

map-updateAt : ∀ {f : P ⋐ Q} {g : P x → P x} {h : Q x → Q x}
               (pxs : All P xs) (i : x ∈ xs) →
               f (g (lookup pxs i)) ≡ h (f (lookup pxs i)) →
               All.map f (pxs All.[ i ]%= g) ≡ (All.map f pxs) All.[ i ]%= h
map-updateAt (px ∷ pxs) (here refl) = cong (_∷ _)
map-updateAt (px ∷ pxs) (there i) feq = cong (_ ∷_) (map-updateAt pxs i feq)

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for list operations
------------------------------------------------------------------------
-- singleton

singleton⁻ : All P [ x ] → P x
singleton⁻ (px ∷ []) = px

-- head

head⁺ : All P xs → Maybe.All P (head xs)
head⁺ []       = nothing
head⁺ (px ∷ _) = just px

-- tail

tail⁺ : All P xs → Maybe.All (All P) (tail xs)
tail⁺ []        = nothing
tail⁺ (_ ∷ pxs) = just pxs

-- last

last⁺ : All P xs → Maybe.All P (last xs)
last⁺ []                 = nothing
last⁺ (px ∷ [])          = just px
last⁺ (px ∷ pxs@(_ ∷ _)) = last⁺ pxs

-- uncons

uncons⁺ : All P xs → Maybe.All (P ⟨×⟩ All P) (uncons xs)
uncons⁺ []         = nothing
uncons⁺ (px ∷ pxs) = just (px , pxs)

uncons⁻ : Maybe.All (P ⟨×⟩ All P) (uncons xs) → All P xs
uncons⁻ {xs = []}     nothing           = []
uncons⁻ {xs = x ∷ xs} (just (px , pxs)) = px ∷ pxs

-- map

map⁺ : ∀ {f : A → B} → All (P ∘ f) xs → All P (map f xs)
map⁺ []       = []
map⁺ (p ∷ ps) = p ∷ map⁺ ps

map⁻ : ∀ {f : A → B} → All P (map f xs) → All (P ∘ f) xs
map⁻ {xs = []}    []       = []
map⁻ {xs = _ ∷ _} (p ∷ ps) = p ∷ map⁻ ps

-- A variant of All.map.

gmap⁺ : ∀ {f : A → B} → P ⋐ Q ∘ f → All P ⋐ All Q ∘ map f
gmap⁺ g = map⁺ ∘ All.map g

gmap⁻ : ∀ {f : A → B} → Q ∘ f ⋐ P → All Q ∘ map f ⋐ All P
gmap⁻ g = All.map g ∘ map⁻

------------------------------------------------------------------------
-- mapMaybe

mapMaybe⁺ : ∀ {f : A → Maybe B} →
            All (Maybe.All P) (map f xs) → All P (mapMaybe f xs)
mapMaybe⁺ {xs = []}     {f = f} []         = []
mapMaybe⁺ {xs = x ∷ xs} {f = f} (px ∷ pxs) with f x
... | nothing = mapMaybe⁺ pxs
... | just v with just pv ← px = pv ∷ mapMaybe⁺ pxs

------------------------------------------------------------------------
-- catMaybes

All-catMaybes⁺ : All (Maybe.All P) xs → All P (catMaybes xs)
All-catMaybes⁺ [] = []
All-catMaybes⁺ (just px ∷ pxs) = px ∷ All-catMaybes⁺ pxs
All-catMaybes⁺ (nothing ∷ pxs) = All-catMaybes⁺ pxs

Any-catMaybes⁺ : All (Maybe.Any P) xs → All P (catMaybes xs)
Any-catMaybes⁺ = All-catMaybes⁺ ∘ All.map fromAny

------------------------------------------------------------------------
-- _++_

++⁺ : All P xs → All P ys → All P (xs ++ ys)
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
++⁻ (x ∷ xs) (px ∷ pxs) = Product.map (px ∷_) id (++⁻ _ pxs)

++↔ : (All P xs × All P ys) ↔ All P (xs ++ ys)
++↔ {xs = zs} = mk↔ₛ′ (uncurry ++⁺) (++⁻ zs) (++⁺∘++⁻ zs) ++⁻∘++⁺
  where
  ++⁺∘++⁻ : ∀ xs (p : All P (xs ++ ys)) → uncurry′ ++⁺ (++⁻ xs p) ≡ p
  ++⁺∘++⁻ []       p          = refl
  ++⁺∘++⁻ (x ∷ xs) (px ∷ pxs) = cong (_∷_ px) $ ++⁺∘++⁻ xs pxs

  ++⁻∘++⁺ : ∀ (p : All P xs × All P ys) → ++⁻ xs (uncurry ++⁺ p) ≡ p
  ++⁻∘++⁺ ([]       , pys) = refl
  ++⁻∘++⁺ (px ∷ pxs , pys) rewrite ++⁻∘++⁺ (pxs , pys) = refl

------------------------------------------------------------------------
-- concat

concat⁺ : ∀ {xss} → All (All P) xss → All P (concat xss)
concat⁺ []           = []
concat⁺ (pxs ∷ pxss) = ++⁺ pxs (concat⁺ pxss)

concat⁻ : ∀ {xss} → All P (concat xss) → All (All P) xss
concat⁻ {xss = []}       []  = []
concat⁻ {xss = xs ∷ xss} pxs = ++⁻ˡ xs pxs ∷ concat⁻ (++⁻ʳ xs pxs)

------------------------------------------------------------------------
-- snoc

∷ʳ⁺ : All P xs → P x → All P (xs ∷ʳ x)
∷ʳ⁺ pxs px = ++⁺ pxs (px ∷ [])

∷ʳ⁻ : All P (xs ∷ʳ x) → All P xs × P x
∷ʳ⁻ pxs = Product.map₂ singleton⁻ $ ++⁻ _ pxs

-- unsnoc

unsnoc⁺ : All P xs → Maybe.All (All P ⟨×⟩ P) (unsnoc xs)
unsnoc⁺ {xs = xs} pxs with initLast xs
unsnoc⁺ {xs = .[]}        pxs | []       = nothing
unsnoc⁺ {xs = .(xs ∷ʳ x)} pxs | xs ∷ʳ′ x = just (∷ʳ⁻ pxs)

unsnoc⁻ : Maybe.All (All P ⟨×⟩ P) (unsnoc xs) → All P xs
unsnoc⁻ {xs = xs} pxs with initLast xs
unsnoc⁻ {xs = .[]}        nothing           | []       = []
unsnoc⁻ {xs = .(xs ∷ʳ x)} (just (pxs , px)) | xs ∷ʳ′ x = ∷ʳ⁺ pxs px

------------------------------------------------------------------------
-- cartesianProductWith and cartesianProduct

module _ (S₁ : Setoid a ℓ₁) (S₂ : Setoid b ℓ₂) where
  open SetoidMembership S₁ using () renaming (_∈_ to _∈₁_)
  open SetoidMembership S₂ using () renaming (_∈_ to _∈₂_)

  cartesianProductWith⁺ : ∀ f xs ys →
                          (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (f x y)) →
                          All P (cartesianProductWith f xs ys)
  cartesianProductWith⁺ f []       ys pres = []
  cartesianProductWith⁺ f (x ∷ xs) ys pres = ++⁺
    (map⁺ (All.tabulateₛ S₂ (pres (here (Setoid.refl S₁)))))
    (cartesianProductWith⁺ f xs ys (pres ∘ there))

  cartesianProduct⁺ : ∀ xs ys →
                      (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (x , y)) →
                      All P (cartesianProduct xs ys)
  cartesianProduct⁺ = cartesianProductWith⁺ _,_

------------------------------------------------------------------------
-- take and drop

drop⁺ : ∀ n → All P xs → All P (drop n xs)
drop⁺ zero    pxs        = pxs
drop⁺ (suc n) []         = []
drop⁺ (suc n) (px ∷ pxs) = drop⁺ n pxs

dropWhile⁺ : (Q? : Decidable Q) → All P xs → All P (dropWhile Q? xs)
dropWhile⁺               Q? []         = []
dropWhile⁺ {xs = x ∷ xs} Q? (px ∷ pxs) with does (Q? x)
... | true  = dropWhile⁺ Q? pxs
... | false = px ∷ pxs

dropWhile⁻ : (P? : Decidable P) → dropWhile P? xs ≡ [] → All P xs
dropWhile⁻ {xs = []}     P? eq = []
dropWhile⁻ {xs = x ∷ xs} P? eq with P? x
... | yes px = px ∷ (dropWhile⁻ P? eq)
... | no ¬px = case eq of λ ()

all-head-dropWhile : (P? : Decidable P) →
                     ∀ xs → Maybe.All (∁ P) (head (dropWhile P? xs))
all-head-dropWhile P? []       = nothing
all-head-dropWhile P? (x ∷ xs) with P? x
... | yes px = all-head-dropWhile P? xs
... | no ¬px = just ¬px

take⁺ : ∀ n → All P xs → All P (take n xs)
take⁺ zero    pxs        = []
take⁺ (suc n) []         = []
take⁺ (suc n) (px ∷ pxs) = px ∷ take⁺ n pxs

takeWhile⁺ : (Q? : Decidable Q) → All P xs → All P (takeWhile Q? xs)
takeWhile⁺               Q? []         = []
takeWhile⁺ {xs = x ∷ xs} Q? (px ∷ pxs) with does (Q? x)
... | true  = px ∷ takeWhile⁺ Q? pxs
... | false = []

takeWhile⁻ : (P? : Decidable P) → takeWhile P? xs ≡ xs → All P xs
takeWhile⁻ {xs = []}     P? eq = []
takeWhile⁻ {xs = x ∷ xs} P? eq with P? x
... | yes px = px ∷ takeWhile⁻ P? (List.∷-injectiveʳ eq)
... | no ¬px = case eq of λ ()

all-takeWhile : (P? : Decidable P) → ∀ xs → All P (takeWhile P? xs)
all-takeWhile P? []       = []
all-takeWhile P? (x ∷ xs) with P? x
... | yes px = px ∷ all-takeWhile P? xs
... | no ¬px = []

------------------------------------------------------------------------
-- applyUpTo

applyUpTo⁺₁ : ∀ f n → (∀ {i} → i < n → P (f i)) → All P (applyUpTo f n)
applyUpTo⁺₁ f zero    Pf = []
applyUpTo⁺₁ f (suc n) Pf = Pf z<s ∷ applyUpTo⁺₁ (f ∘ suc) n (Pf ∘ s<s)

applyUpTo⁺₂ : ∀ f n → (∀ i → P (f i)) → All P (applyUpTo f n)
applyUpTo⁺₂ f n Pf = applyUpTo⁺₁ f n (λ _ → Pf _)

applyUpTo⁻ : ∀ f n → All P (applyUpTo f n) → ∀ {i} → i < n → P (f i)
applyUpTo⁻ f (suc n) (px ∷ _)   z<s       = px
applyUpTo⁻ f (suc n) (_  ∷ pxs) (s<s i<n@(s≤s _)) =
  applyUpTo⁻ (f ∘ suc) n pxs i<n

------------------------------------------------------------------------
-- upTo

all-upTo : ∀ n → All (_< n) (upTo n)
all-upTo n = applyUpTo⁺₁ id n id

------------------------------------------------------------------------
-- applyDownFrom

applyDownFrom⁺₁ : ∀ f n → (∀ {i} → i < n → P (f i)) → All P (applyDownFrom f n)
applyDownFrom⁺₁ f zero    Pf = []
applyDownFrom⁺₁ f (suc n) Pf = Pf ≤-refl ∷ applyDownFrom⁺₁ f n (Pf ∘ m≤n⇒m≤1+n)

applyDownFrom⁺₂ : ∀ f n → (∀ i → P (f i)) → All P (applyDownFrom f n)
applyDownFrom⁺₂ f n Pf = applyDownFrom⁺₁ f n (λ _ → Pf _)

------------------------------------------------------------------------
-- tabulate

tabulate⁺ : ∀ {n} {f : Fin n → A} →
            (∀ i → P (f i)) → All P (tabulate f)
tabulate⁺ {n = zero}  Pf = []
tabulate⁺ {n = suc _} Pf = Pf zero ∷ tabulate⁺ (Pf ∘ suc)

tabulate⁻ : ∀ {n} {f : Fin n → A} →
            All P (tabulate f) → (∀ i → P (f i))
tabulate⁻ (px ∷ _) zero    = px
tabulate⁻ (_ ∷ pf) (suc i) = tabulate⁻ pf i

------------------------------------------------------------------------
-- remove

─⁺ : ∀ (p : Any P xs) → All Q xs → All Q (xs Any.─ p)
─⁺ (here px) (_ ∷ qs) = qs
─⁺ (there p) (q ∷ qs) = q ∷ ─⁺ p qs

─⁻ : ∀ (p : Any P xs) → Q (Any.lookup p) → All Q (xs Any.─ p) → All Q xs
─⁻ (here px) q qs        = q ∷ qs
─⁻ (there p) q (q′ ∷ qs) = q′ ∷ ─⁻ p q qs

------------------------------------------------------------------------
-- filter

module _ (P? : Decidable P) where

  all-filter : ∀ xs → All P (filter P? xs)
  all-filter []       = []
  all-filter (x ∷ xs) with P? x
  ... | true  because [Px] = invert [Px] ∷ all-filter xs
  ... | false because  _   = all-filter xs

  filter⁺ : All Q xs → All Q (filter P? xs)
  filter⁺ {xs = _}     [] = []
  filter⁺ {xs = x ∷ _} (Qx ∷ Qxs) with does (P? x)
  ... | false = filter⁺ Qxs
  ... | true  = Qx ∷ filter⁺ Qxs

  filter⁻ : All Q (filter P? xs) → All Q (filter (¬? ∘ P?) xs) → All Q xs
  filter⁻ {xs = []}          []          []                         = []
  filter⁻ {xs = x ∷ _}       all⁺        all⁻ with P? x  | ¬? (P? x)
  filter⁻ {xs = x ∷ _}       all⁺        all⁻  | yes  Px | yes  ¬Px = contradiction Px ¬Px
  filter⁻ {xs = x ∷ _} (qx ∷ all⁺)       all⁻  | yes  Px | no  ¬¬Px = qx ∷ filter⁻ all⁺ all⁻
  filter⁻ {xs = x ∷ _}       all⁺  (qx ∷ all⁻) | no    _ | yes  ¬Px = qx ∷ filter⁻ all⁺ all⁻
  filter⁻ {xs = x ∷ _}       all⁺        all⁻  | no  ¬Px | no  ¬¬Px = contradiction ¬Px ¬¬Px

------------------------------------------------------------------------
-- partition

module _ {P : A → Set p} (P? : Decidable P) where

  partition-All : ∀ xs → (let ys , zs = partition P? xs) →
                  All P ys × All (∁ P) zs
  partition-All xs rewrite List.partition-defn P? xs =
    all-filter P? xs , all-filter (∁? P?) xs

------------------------------------------------------------------------
-- derun and deduplicate

module _ {R : A → A → Set q} (R? : B.Decidable R) where

  derun⁺ : All P xs → All P (derun R? xs)
  derun⁺ {xs = []}         []                 = []
  derun⁺ {xs = x ∷ []}     (px ∷ [])          = px ∷ []
  derun⁺ {xs = x ∷ y ∷ xs} (px ∷ all[P,y∷xs]) with does (R? x y)
  ... | false = px ∷ derun⁺ all[P,y∷xs]
  ... | true  = derun⁺ all[P,y∷xs]

  deduplicate⁺ : All P xs → All P (deduplicate R? xs)
  deduplicate⁺ []         = []
  deduplicate⁺ (px ∷ pxs) = px ∷ filter⁺ (¬? ∘ R? _) (deduplicate⁺ pxs)

  derun⁻ : P B.Respects (flip R) → ∀ xs → All P (derun R? xs) → All P xs
  derun⁻ {P = P} P-resp-R []       []          = []
  derun⁻ {P = P} P-resp-R (x ∷ xs) all[P,x∷xs] = aux x xs all[P,x∷xs]
    where
    aux : ∀ x xs → All P (derun R? (x ∷ xs)) → All P (x ∷ xs)
    aux x []       (px ∷ []) = px ∷ []
    aux x (y ∷ xs) all[P,x∷y∷xs] with R? x y
    aux x (y ∷ xs) all[P,y∷xs]        | yes Rxy
      with r@(py ∷ _) ← aux y xs all[P,y∷xs] = P-resp-R Rxy py ∷ r
    aux x (y ∷ xs) (px ∷ all[P,y∷xs]) | no _ = px ∷ aux y xs all[P,y∷xs]

  deduplicate⁻ : P B.Respects R → ∀ xs → All P (deduplicate R? xs) → All P xs
  deduplicate⁻ {P = P} resp []       [] = []
  deduplicate⁻ {P = P} resp (x ∷ xs) (px ∷ pxs!) =
    px ∷ deduplicate⁻ resp xs (filter⁻ (¬? ∘ R? x) pxs! (All.tabulate aux))
    where
    aux : ∀ {z} → z ∈ filter (¬? ∘ ¬? ∘ R? x) (deduplicate R? xs) → P z
    aux {z = z} z∈filter = resp (decidable-stable (R? x z)
      (Product.proj₂ (∈-filter⁻ (¬? ∘ ¬? ∘ R? x) {z} {deduplicate R? xs} z∈filter))) px

------------------------------------------------------------------------
-- zipWith

zipWith⁺ : ∀ (f : A → B → C) → Pointwise (λ x y → P (f x y)) xs ys →
           All P (zipWith f xs ys)
zipWith⁺ f []              = []
zipWith⁺ f (Pfxy ∷ Pfxsys) = Pfxy ∷ zipWith⁺ f Pfxsys

------------------------------------------------------------------------
-- Operations for constructing lists
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

replicate⁺ : ∀ n → P x → All P (replicate n x)
replicate⁺ zero    px = []
replicate⁺ (suc n) px = px ∷ replicate⁺ n px

replicate⁻ : ∀ {n} → All P (replicate (suc n) x) → P x
replicate⁻ (px ∷ _) = px

------------------------------------------------------------------------
-- inits

inits⁺ : All P xs → All (All P) (inits xs)
inits⁺ []         = [] ∷ []
inits⁺ (px ∷ pxs) = [] ∷ gmap⁺ (px ∷_) (inits⁺ pxs)

inits⁻ : ∀ xs → All (All P) (inits xs) → All P xs
inits⁻ []               pxs                   = []
inits⁻ (x ∷ [])         ([] ∷ p[x] ∷ [])      = p[x]
inits⁻ (x ∷ xs@(_ ∷ _)) ([] ∷ pxs@(p[x] ∷ _)) =
  singleton⁻ p[x] ∷ inits⁻ xs (All.map (drop⁺ 1) (map⁻ pxs))

------------------------------------------------------------------------
-- tails

tails⁺ : All P xs → All (All P) (tails xs)
tails⁺ []             = [] ∷ []
tails⁺ pxxs@(_ ∷ pxs) = pxxs ∷ tails⁺ pxs

tails⁻ : ∀ xs → All (All P) (tails xs) → All P xs
tails⁻ []       pxs        = []
tails⁻ (x ∷ xs) (pxxs ∷ _) = pxxs

------------------------------------------------------------------------
-- all

module _ (p : A → Bool) where

  all⁺ : ∀ xs → T (all p xs) → All (T ∘ p) xs
  all⁺ []       _      = []
  all⁺ (x ∷ xs) px∷pxs =
    let px , pxs = Equivalence.to (T-∧ {p x}) px∷pxs
    in px ∷ all⁺ xs pxs

  all⁻ : All (T ∘ p) xs → T (all p xs)
  all⁻ []         = _
  all⁻ (px ∷ pxs) = Equivalence.from T-∧ (px , all⁻ pxs)

------------------------------------------------------------------------
-- All is anti-monotone.

anti-mono : xs ⊆ ys → All P ys → All P xs
anti-mono xs⊆ys pys = All.tabulate (lookup pys ∘ xs⊆ys)

all-anti-mono : ∀ (p : A → Bool) → xs ⊆ ys → T (all p ys) → T (all p xs)
all-anti-mono p xs⊆ys = all⁻ p ∘ anti-mono xs⊆ys ∘ all⁺ p _

------------------------------------------------------------------------
-- Interactions with pointwise equality
------------------------------------------------------------------------

module _ (S : Setoid c ℓ) where

  open Setoid S
  open ≋ S

  respects : P B.Respects _≈_ → (All P) B.Respects _≋_
  respects p≈ []            []         = []
  respects p≈ (x≈y ∷ xs≈ys) (px ∷ pxs) = p≈ x≈y px ∷ respects p≈ xs≈ys pxs

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

updateAt-id-relative = updateAt-id-local
{-# WARNING_ON_USAGE updateAt-id-relative
"Warning: updateAt-id-relative was deprecated in v2.0.
Please use updateAt-id-local instead."
#-}

updateAt-compose-relative = updateAt-∘-local
{-# WARNING_ON_USAGE updateAt-compose-relative
"Warning: updateAt-compose-relative was deprecated in v2.0.
Please use updateAt-∘-local instead."
#-}

updateAt-compose = updateAt-∘
{-# WARNING_ON_USAGE updateAt-compose
"Warning: updateAt-compose was deprecated in v2.0.
Please use updateAt-∘ instead."
#-}

updateAt-cong-relative = updateAt-cong-local
{-# WARNING_ON_USAGE updateAt-cong-relative
"Warning: updateAt-cong-relative was deprecated in v2.0.
Please use updateAt-cong-local instead."
#-}

gmap = gmap⁺
{-# WARNING_ON_USAGE gmap
"Warning: gmap was deprecated in v2.0.
Please use gmap⁺ instead."
#-}

-- Version 2.1

map-compose = map-∘
{-# WARNING_ON_USAGE map-compose
"Warning: map-compose was deprecated in v2.1.
Please use map-∘ instead."
#-}
