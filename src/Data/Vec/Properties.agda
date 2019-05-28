------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vec-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Properties where

open import Algebra.FunctionProperties
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ)
open import Data.List.Base as List using (List)
open import Data.Nat
open import Data.Nat.Properties using (+-assoc; ≤-step)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; <_,_>; uncurry)
open import Data.Vec
open import Function
open import Function.Inverse using (_↔_; inverse)
open import Level using (Level)
open import Relation.Binary as B hiding (Decidable)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; _≗_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no)

private
  variable
    a b c d p : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

------------------------------------------------------------------------
-- Properties of propositional equality over vectors

module _ {n} {x y : A} {xs ys : Vec A n} where

 ∷-injectiveˡ : x ∷ xs ≡ y ∷ ys → x ≡ y
 ∷-injectiveˡ refl = refl

 ∷-injectiveʳ : x ∷ xs ≡ y ∷ ys → xs ≡ ys
 ∷-injectiveʳ refl = refl

 ∷-injective : (x ∷ xs) ≡ (y ∷ ys) → x ≡ y × xs ≡ ys
 ∷-injective refl = refl , refl

≡-dec : B.Decidable _≡_ → ∀ {n} → B.Decidable {A = Vec A n} _≡_
≡-dec _≟_ []       []       = yes refl
≡-dec _≟_ (x ∷ xs) (y ∷ ys) with x ≟ y | ≡-dec _≟_ xs ys
... | yes refl | yes refl = yes refl
... | no  x≢y  | _        = no (x≢y   ∘ ∷-injectiveˡ)
... | yes _    | no xs≢ys = no (xs≢ys ∘ ∷-injectiveʳ)

------------------------------------------------------------------------
-- _[_]=_

[]=-injective : ∀ {n} {xs : Vec A n} {i x y} →
                xs [ i ]= x → xs [ i ]= y → x ≡ y
[]=-injective here          here          = refl
[]=-injective (there xsᵢ≡x) (there xsᵢ≡y) = []=-injective xsᵢ≡x xsᵢ≡y

-- See also Data.Vec.Properties.WithK.[]=-irrelevant.

------------------------------------------------------------------------
-- lookup

[]=⇒lookup : ∀ {n} {x : A} {xs} {i : Fin n} →
             xs [ i ]= x → lookup xs i ≡ x
[]=⇒lookup here            = refl
[]=⇒lookup (there xs[i]=x) = []=⇒lookup xs[i]=x

lookup⇒[]= : ∀ {n} (i : Fin n) {x : A} xs →
             lookup xs i ≡ x → xs [ i ]= x
lookup⇒[]= zero    (_ ∷ _)  refl = here
lookup⇒[]= (suc i) (_ ∷ xs) p    = there (lookup⇒[]= i xs p)

[]=↔lookup : ∀ {n i} {x} {xs : Vec A n} →
             xs [ i ]= x ↔ lookup xs i ≡ x
[]=↔lookup {i = i} =
  inverse []=⇒lookup (lookup⇒[]= _ _)
          lookup⇒[]=∘[]=⇒lookup ([]=⇒lookup∘lookup⇒[]= _ i)
  where
  lookup⇒[]=∘[]=⇒lookup :
    ∀ {n x xs} {i : Fin n} (p : xs [ i ]= x) →
    lookup⇒[]= i xs ([]=⇒lookup p) ≡ p
  lookup⇒[]=∘[]=⇒lookup here      = refl
  lookup⇒[]=∘[]=⇒lookup (there p) =
    P.cong there (lookup⇒[]=∘[]=⇒lookup p)

  []=⇒lookup∘lookup⇒[]= :
    ∀ {n} xs (i : Fin n) {x} (p : lookup xs i ≡ x) →
    []=⇒lookup (lookup⇒[]= i xs p) ≡ p
  []=⇒lookup∘lookup⇒[]= (x ∷ xs) zero    refl = refl
  []=⇒lookup∘lookup⇒[]= (x ∷ xs) (suc i) p    =
    []=⇒lookup∘lookup⇒[]= xs i p

------------------------------------------------------------------------
-- updateAt (_[_]%=_)

-- (+) updateAt i actually updates the element at index i.

updateAt-updates : ∀ {n} (i : Fin n) {f : A → A} (xs : Vec A n) {x : A} →
                   xs [ i ]= x → (updateAt i f xs) [ i ]= f x
updateAt-updates zero    (x ∷ xs) here        = here
updateAt-updates (suc i) (x ∷ xs) (there loc) = there (updateAt-updates i xs loc)

-- (-) updateAt i does not touch the elements at other indices.

updateAt-minimal : ∀ {n} (i j : Fin n) {f : A → A} {x : A} (xs : Vec A n) →
                   i ≢ j → xs [ i ]= x → (updateAt j f xs) [ i ]= x
updateAt-minimal zero    zero    (x ∷ xs) 0≢0 here        = ⊥-elim (0≢0 refl)
updateAt-minimal zero    (suc j) (x ∷ xs) _   here        = here
updateAt-minimal (suc i) zero    (x ∷ xs) _   (there loc) = there loc
updateAt-minimal (suc i) (suc j) (x ∷ xs) i≢j (there loc) =
  there (updateAt-minimal i j xs (i≢j ∘ P.cong suc) loc)

-- The other properties are consequences of (+) and (-).
-- We spell the most natural properties out.
-- Direct inductive proofs are in most cases easier than just using
-- the defining properties.

-- In the explanations, we make use of shorthand  f = g ↾ x
-- meaning that f and g agree at point x, i.e.  f x ≡ g x.

-- updateAt i  is a morphism from the monoid of endofunctions  A → A
-- to the monoid of endofunctions  Vec A n → Vec A n

-- 1a. relative identity:  f = id ↾ (lookup xs i)
--                implies  updateAt i f = id ↾ xs

updateAt-id-relative : ∀ {n} (i : Fin n) (xs : Vec A n) {f : A → A} →
                       f (lookup xs i) ≡ lookup xs i →
                       updateAt i f xs ≡ xs
updateAt-id-relative zero    (x ∷ xs) eq = P.cong (_∷ xs) eq
updateAt-id-relative (suc i) (x ∷ xs) eq = P.cong (x ∷_) (updateAt-id-relative i xs eq)

-- 1b. identity:  updateAt i id ≗ id

updateAt-id : ∀ {n} (i : Fin n) (xs : Vec A n) →
              updateAt i id xs ≡ xs
updateAt-id i xs = updateAt-id-relative i xs refl

-- 2a. relative composition:  f ∘ g = h ↾ (lookup i xs)
--                   implies  updateAt i f ∘ updateAt i g ≗ updateAt i h

updateAt-compose-relative : ∀ {n} (i : Fin n) {f g h : A → A} (xs : Vec A n) →
                            f (g (lookup xs i)) ≡ h (lookup xs i) →
                            updateAt i f (updateAt i g xs) ≡ updateAt i h xs
updateAt-compose-relative zero    (x ∷ xs) fg=h = P.cong (_∷ xs) fg=h
updateAt-compose-relative (suc i) (x ∷ xs) fg=h =
  P.cong (x ∷_) (updateAt-compose-relative i xs fg=h)

-- 2b. composition:  updateAt i f ∘ updateAt i g ≗ updateAt i (f ∘ g)

updateAt-compose : ∀ {n} (i : Fin n) {f g : A → A} →
                   updateAt i f ∘ updateAt i g ≗ updateAt i (f ∘ g)
updateAt-compose i xs = updateAt-compose-relative i xs refl

-- 3. congruence:  updateAt i  is a congruence wrt. extensional equality.

-- 3a.  If    f = g ↾ (lookup i xs)
--      then  updateAt i f = updateAt i g ↾ xs

updateAt-cong-relative : ∀ {n} (i : Fin n) {f g : A → A} (xs : Vec A n) →
                         f (lookup xs i) ≡ g (lookup xs i) →
                         updateAt i f xs ≡ updateAt i g xs
updateAt-cong-relative zero    (x ∷ xs) f=g = P.cong (_∷ xs) f=g
updateAt-cong-relative (suc i) (x ∷ xs) f=g = P.cong (x ∷_) (updateAt-cong-relative i xs f=g)

-- 3b. congruence:  f ≗ g → updateAt i f ≗ updateAt i g

updateAt-cong : ∀ {n} (i : Fin n) {f g : A → A} →
                f ≗ g → updateAt i f ≗ updateAt i g
updateAt-cong i f≗g xs = updateAt-cong-relative i xs (f≗g (lookup xs i))

-- The order of updates at different indices i ≢ j does not matter.

-- This a consequence of updateAt-updates and updateAt-minimal
-- but easier to prove inductively.

updateAt-commutes : ∀ {n} (i j : Fin n) {f g : A → A} → i ≢ j →
                    updateAt i f ∘ updateAt j g ≗ updateAt j g ∘ updateAt i f
updateAt-commutes zero    zero    0≢0 (x ∷ xs) = ⊥-elim (0≢0 refl)
updateAt-commutes zero    (suc j) i≢j (x ∷ xs) = refl
updateAt-commutes (suc i) zero    i≢j (x ∷ xs) = refl
updateAt-commutes (suc i) (suc j) i≢j (x ∷ xs) =
  P.cong (x ∷_) (updateAt-commutes i j (i≢j ∘ P.cong suc) xs)

-- lookup after updateAt reduces.

-- For same index this is an easy consequence of updateAt-updates
-- using []=↔lookup.

lookup∘updateAt : ∀ {n} (i : Fin n) {f : A → A} →
                  ∀ xs → lookup (updateAt i f xs) i ≡ f (lookup xs i)
lookup∘updateAt i xs =
  []=⇒lookup (updateAt-updates i xs (lookup⇒[]= i _ refl))

-- For different indices it easily follows from updateAt-minimal.

lookup∘updateAt′ : ∀ {n} (i j : Fin n) {f : A → A} → i ≢ j →
                   ∀ xs → lookup (updateAt j f xs) i ≡ lookup xs i
lookup∘updateAt′ i j xs i≢j =
  []=⇒lookup (updateAt-minimal i j i≢j xs (lookup⇒[]= i _ refl))

-- Aliases for notation _[_]%=_

[]%=-id : ∀ {n} (xs : Vec A n) (i : Fin n) → xs [ i ]%= id ≡ xs
[]%=-id xs i = updateAt-id i xs

[]%=-compose : ∀ {n} (xs : Vec A n) (i : Fin n) {f g : A → A} →
     xs [ i ]%= f
        [ i ]%= g
   ≡ xs [ i ]%= g ∘ f
[]%=-compose xs i = updateAt-compose i xs

------------------------------------------------------------------------
-- _[_]≔_ (update)
--
-- _[_]≔_ is defined in terms of updateAt, and all of its properties
-- are special cases of the ones for updateAt.

[]≔-idempotent : ∀ {n} (xs : Vec A n) (i : Fin n) {x₁ x₂ : A} →
                 (xs [ i ]≔ x₁) [ i ]≔ x₂ ≡ xs [ i ]≔ x₂
[]≔-idempotent xs i = updateAt-compose i xs

[]≔-commutes : ∀ {n} (xs : Vec A n) (i j : Fin n) {x y : A} → i ≢ j →
               (xs [ i ]≔ x) [ j ]≔ y ≡ (xs [ j ]≔ y) [ i ]≔ x
[]≔-commutes xs i j i≢j = updateAt-commutes j i (i≢j ∘ P.sym) xs

[]≔-updates : ∀ {n} (xs : Vec A n) (i : Fin n) {x : A} →
              (xs [ i ]≔ x) [ i ]= x
[]≔-updates xs i = updateAt-updates i xs (lookup⇒[]= i xs refl)

[]≔-minimal : ∀ {n} (xs : Vec A n) (i j : Fin n) {x y : A} → i ≢ j →
              xs [ i ]= x → (xs [ j ]≔ y) [ i ]= x
[]≔-minimal xs i j i≢j loc = updateAt-minimal i j xs i≢j loc

[]≔-lookup : ∀ {n} (xs : Vec A n) (i : Fin n) →
             xs [ i ]≔ lookup xs i ≡ xs
[]≔-lookup xs i = updateAt-id-relative i xs refl

[]≔-++-inject+ : ∀ {m n x} (xs : Vec A m) (ys : Vec A n) i →
                 (xs ++ ys) [ Fin.inject+ n i ]≔ x ≡ (xs [ i ]≔ x) ++ ys
[]≔-++-inject+ (x ∷ xs) ys zero    = refl
[]≔-++-inject+ (x ∷ xs) ys (suc i) =
  P.cong (x ∷_) $ []≔-++-inject+ xs ys i

lookup∘update : ∀ {n} (i : Fin n) (xs : Vec A n) x →
                lookup (xs [ i ]≔ x) i ≡ x
lookup∘update i xs x = lookup∘updateAt i xs

lookup∘update′ : ∀ {n} {i j : Fin n} → i ≢ j → ∀ (xs : Vec A n) y →
                 lookup (xs [ j ]≔ y) i ≡ lookup xs i
lookup∘update′ {i = i} {j} i≢j xs y = lookup∘updateAt′ i j i≢j xs

------------------------------------------------------------------------
-- map

map-id : ∀ {n} → map {A = A} {n = n} id ≗ id
map-id []       = refl
map-id (x ∷ xs) = P.cong (x ∷_) (map-id xs)

map-cong : ∀ {n} {f g : A → B} → f ≗ g → map {n = n} f ≗ map g
map-cong f≗g []       = refl
map-cong f≗g (x ∷ xs) = P.cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

map-∘ : ∀ {n} (f : B → C) (g : A → B) →
        map {n = n} (f ∘ g) ≗ map f ∘ map g
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) = P.cong (f (g x) ∷_) (map-∘ f g xs)

lookup-map : ∀ {n} (i : Fin n) (f : A → B) (xs : Vec A n) →
             lookup (map f xs) i ≡ f (lookup xs i)
lookup-map zero    f (x ∷ xs) = refl
lookup-map (suc i) f (x ∷ xs) = lookup-map i f xs

map-updateAt : ∀ {n} {f : A → B} {g : A → A} {h : B → B}
               (xs : Vec A n) (i : Fin n) →
               f (g (lookup xs i)) ≡ h (f (lookup xs i)) →
               map f (updateAt i g xs) ≡ updateAt i h (map f xs)
map-updateAt (x ∷ xs) zero    eq = P.cong (_∷ _) eq
map-updateAt (x ∷ xs) (suc i) eq = P.cong (_ ∷_) (map-updateAt xs i eq)

map-[]≔ : ∀ {n} (f : A → B) (xs : Vec A n) (i : Fin n) {x : A} →
          map f (xs [ i ]≔ x) ≡ map f xs [ i ]≔ f x
map-[]≔ f xs i = map-updateAt xs i refl

------------------------------------------------------------------------
-- _++_

module _ {m} {ys ys' : Vec A m} where

  -- See also Data.Vec.Properties.WithK.++-assoc.

  ++-injectiveˡ : ∀ {n} (xs xs' : Vec A n) →
                  xs ++ ys ≡ xs' ++ ys' → xs ≡ xs'
  ++-injectiveˡ []       []         _  = refl
  ++-injectiveˡ (x ∷ xs) (x' ∷ xs') eq =
    P.cong₂ _∷_ (∷-injectiveˡ eq) (++-injectiveˡ _ _ (∷-injectiveʳ eq))

  ++-injectiveʳ : ∀ {n} (xs xs' : Vec A n) →
                  xs ++ ys ≡ xs' ++ ys' → ys ≡ ys'
  ++-injectiveʳ []       []         eq = eq
  ++-injectiveʳ (x ∷ xs) (x' ∷ xs') eq =
    ++-injectiveʳ xs xs' (∷-injectiveʳ eq)

  ++-injective  : ∀ {n} (xs xs' : Vec A n) →
                  xs ++ ys ≡ xs' ++ ys' → xs ≡ xs' × ys ≡ ys'
  ++-injective xs xs' eq =
    (++-injectiveˡ xs xs' eq , ++-injectiveʳ xs xs' eq)

lookup-++-< : ∀ {m n} (xs : Vec A m) (ys : Vec A n) →
              ∀ i (i<m : toℕ i < m) →
              lookup (xs ++ ys) i  ≡ lookup xs (Fin.fromℕ≤ i<m)
lookup-++-< (x ∷ xs) ys zero    (s≤s z≤n)       = refl
lookup-++-< (x ∷ xs) ys (suc i) (s≤s (s≤s i<m)) =
  lookup-++-< xs ys i (s≤s i<m)

lookup-++-≥ : ∀ {m n} (xs : Vec A m) (ys : Vec A n) →
              ∀ i (i≥m : toℕ i ≥ m) →
              lookup (xs ++ ys) i ≡ lookup ys (Fin.reduce≥ i i≥m)
lookup-++-≥ []       ys i       i≥m       = refl
lookup-++-≥ (x ∷ xs) ys (suc i) (s≤s i≥m) = lookup-++-≥ xs ys i i≥m

lookup-++ˡ : ∀ {m n} (xs : Vec A m) (ys : Vec A n) i →
             lookup (xs ++ ys) (Fin.inject+ n i) ≡ lookup xs i
lookup-++ˡ (x ∷ xs) ys zero    = refl
lookup-++ˡ (x ∷ xs) ys (suc i) = lookup-++ˡ xs ys i

lookup-++ʳ : ∀ {m n} (xs : Vec A m) (ys : Vec A n) i →
             lookup (xs ++ ys) (Fin.raise m i) ≡ lookup ys i
lookup-++ʳ []       ys       zero    = refl
lookup-++ʳ []       (y ∷ xs) (suc i) = lookup-++ʳ [] xs i
lookup-++ʳ (x ∷ xs) ys       i       = lookup-++ʳ xs ys i

------------------------------------------------------------------------
-- zipWith

module _ {f : A → A → A} where

  zipWith-assoc : Associative _≡_ f → ∀ {n} →
                  Associative _≡_ (zipWith {n = n} f)
  zipWith-assoc assoc []       []       []       = refl
  zipWith-assoc assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    P.cong₂ _∷_ (assoc x y z) (zipWith-assoc assoc xs ys zs)

  zipWith-idem : Idempotent _≡_ f → ∀ {n} →
                 Idempotent _≡_ (zipWith {n = n} f)
  zipWith-idem idem []       = refl
  zipWith-idem idem (x ∷ xs) =
    P.cong₂ _∷_ (idem x) (zipWith-idem idem xs)

module _ {f : A → A → A} {e : A} where

  zipWith-identityˡ : LeftIdentity _≡_ e f → ∀ {n} →
                      LeftIdentity _≡_ (replicate e) (zipWith {n = n} f)
  zipWith-identityˡ idˡ []       = refl
  zipWith-identityˡ idˡ (x ∷ xs) =
    P.cong₂ _∷_ (idˡ x) (zipWith-identityˡ idˡ xs)

  zipWith-identityʳ : RightIdentity _≡_ e f → ∀ {n} →
                      RightIdentity _≡_ (replicate e) (zipWith {n = n} f)
  zipWith-identityʳ idʳ []       = refl
  zipWith-identityʳ idʳ (x ∷ xs) =
    P.cong₂ _∷_ (idʳ x) (zipWith-identityʳ idʳ xs)

  zipWith-zeroˡ : LeftZero _≡_ e f → ∀ {n} →
                  LeftZero _≡_ (replicate e) (zipWith {n = n} f)
  zipWith-zeroˡ zeˡ []       = refl
  zipWith-zeroˡ zeˡ (x ∷ xs) =
    P.cong₂ _∷_ (zeˡ x) (zipWith-zeroˡ zeˡ xs)

  zipWith-zeroʳ : RightZero _≡_ e f → ∀ {n} →
                  RightZero _≡_ (replicate e) (zipWith {n = n} f)
  zipWith-zeroʳ zeʳ []       = refl
  zipWith-zeroʳ zeʳ (x ∷ xs) =
    P.cong₂ _∷_ (zeʳ x) (zipWith-zeroʳ zeʳ xs)

  zipWith-inverseˡ : ∀ {⁻¹} → LeftInverse _≡_ e ⁻¹ f → ∀ {n} →
                     LeftInverse _≡_ (replicate {n = n} e) (map ⁻¹) (zipWith f)
  zipWith-inverseˡ invˡ []       = refl
  zipWith-inverseˡ invˡ (x ∷ xs) =
    P.cong₂ _∷_ (invˡ x) (zipWith-inverseˡ invˡ xs)

  zipWith-inverseʳ : ∀ {⁻¹} → RightInverse _≡_ e ⁻¹ f → ∀ {n} →
                     RightInverse _≡_ (replicate {n = n} e) (map ⁻¹) (zipWith f)
  zipWith-inverseʳ invʳ []       = refl
  zipWith-inverseʳ invʳ (x ∷ xs) =
    P.cong₂ _∷_ (invʳ x) (zipWith-inverseʳ invʳ xs)

module _ {f g : A → A → A} where

  zipWith-distribˡ : _DistributesOverˡ_ _≡_ f g → ∀ {n} →
                     _DistributesOverˡ_ _≡_ (zipWith {n = n} f) (zipWith g)
  zipWith-distribˡ distribˡ []        []      []       = refl
  zipWith-distribˡ distribˡ (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    P.cong₂ _∷_ (distribˡ x y z) (zipWith-distribˡ distribˡ xs ys zs)

  zipWith-distribʳ : _DistributesOverʳ_ _≡_ f g → ∀ {n} →
                     _DistributesOverʳ_ _≡_ (zipWith {n = n} f) (zipWith g)
  zipWith-distribʳ distribʳ []        []      []       = refl
  zipWith-distribʳ distribʳ (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    P.cong₂ _∷_ (distribʳ x y z) (zipWith-distribʳ distribʳ xs ys zs)

  zipWith-absorbs : _Absorbs_ _≡_ f g → ∀ {n} →
                   _Absorbs_ _≡_ (zipWith {n = n} f) (zipWith g)
  zipWith-absorbs abs []       []       = refl
  zipWith-absorbs abs (x ∷ xs) (y ∷ ys) =
    P.cong₂ _∷_ (abs x y) (zipWith-absorbs abs xs ys)

module _ {f : A → A → B} where

  zipWith-comm : (∀ x y → f x y ≡ f y x) → ∀ {n}
                 (xs ys : Vec A n) → zipWith f xs ys ≡ zipWith f ys xs
  zipWith-comm comm []       []       = refl
  zipWith-comm comm (x ∷ xs) (y ∷ ys) =
    P.cong₂ _∷_ (comm x y) (zipWith-comm comm xs ys)

zipWith-map₁ : ∀ {n} (_⊕_ : B → C → D) (f : A → B)
               (xs : Vec A n) (ys : Vec C n) →
               zipWith _⊕_ (map f xs) ys ≡ zipWith (λ x y → f x ⊕ y) xs ys
zipWith-map₁ _⊕_ f []       []       = refl
zipWith-map₁ _⊕_ f (x ∷ xs) (y ∷ ys) =
  P.cong (f x ⊕ y ∷_) (zipWith-map₁ _⊕_ f xs ys)

zipWith-map₂ : ∀ {n} (_⊕_ : A → C → D) (f : B → C)
               (xs : Vec A n) (ys : Vec B n) →
               zipWith _⊕_ xs (map f ys) ≡ zipWith (λ x y → x ⊕ f y) xs ys
zipWith-map₂ _⊕_ f []       []       = refl
zipWith-map₂ _⊕_ f (x ∷ xs) (y ∷ ys) =
  P.cong (x ⊕ f y ∷_) (zipWith-map₂ _⊕_ f xs ys)

lookup-zipWith : ∀ (f : A → B → C) {n} (i : Fin n) xs ys →
                 lookup (zipWith f xs ys) i ≡ f (lookup xs i) (lookup ys i)
lookup-zipWith _ zero    (x ∷ _)  (y ∷ _)   = refl
lookup-zipWith _ (suc i) (_ ∷ xs) (_ ∷ ys)  = lookup-zipWith _ i xs ys

------------------------------------------------------------------------
-- zip

lookup-zip : ∀ {n} (i : Fin n) (xs : Vec A n) (ys : Vec B n) →
             lookup (zip xs ys) i ≡ (lookup xs i , lookup ys i)
lookup-zip = lookup-zipWith _,_

-- map lifts projections to vectors of products.

map-proj₁-zip : ∀ {n} (xs : Vec A n) (ys : Vec B n) →
                map proj₁ (zip xs ys) ≡ xs
map-proj₁-zip []       []       = refl
map-proj₁-zip (x ∷ xs) (y ∷ ys) = P.cong (x ∷_) (map-proj₁-zip xs ys)

map-proj₂-zip : ∀ {n} (xs : Vec A n) (ys : Vec B n) →
                map proj₂ (zip xs ys) ≡ ys
map-proj₂-zip []       []       = refl
map-proj₂-zip (x ∷ xs) (y ∷ ys) = P.cong (y ∷_) (map-proj₂-zip xs ys)

-- map lifts pairing to vectors of products.

map-<,>-zip : ∀ {n} (f : A → B) (g : A → C) (xs : Vec A n) →
              map < f , g > xs ≡ zip (map f xs) (map g xs)
map-<,>-zip f g []       = P.refl
map-<,>-zip f g (x ∷ xs) = P.cong (_ ∷_) (map-<,>-zip f g xs)

map-zip : ∀ {n} (f : A → B) (g : C → D) (xs : Vec A n) (ys : Vec C n) →
          map (Prod.map f g) (zip xs ys) ≡ zip (map f xs) (map g ys)
map-zip f g []       []       = refl
map-zip f g (x ∷ xs) (y ∷ ys) = P.cong (_ ∷_) (map-zip f g xs ys)

------------------------------------------------------------------------
-- unzip

lookup-unzip : ∀ {n} (i : Fin n) (xys : Vec (A × B) n) →
               let xs , ys = unzip xys
               in (lookup xs i , lookup ys i) ≡ lookup xys i
lookup-unzip ()      []
lookup-unzip zero    ((x , y) ∷ xys) = refl
lookup-unzip (suc i) ((x , y) ∷ xys) = lookup-unzip i xys

map-unzip : ∀ {n} (f : A → B) (g : C → D) (xys : Vec (A × C) n) →
            let xs , ys = unzip xys
            in (map f xs , map g ys) ≡ unzip (map (Prod.map f g) xys)
map-unzip f g []              = refl
map-unzip f g ((x , y) ∷ xys) =
  P.cong (Prod.map (f x ∷_) (g y ∷_)) (map-unzip f g xys)

-- Products of vectors are isomorphic to vectors of products.

unzip∘zip : ∀ {n} (xs : Vec A n) (ys : Vec B n) →
            unzip (zip xs ys) ≡ (xs , ys)
unzip∘zip [] []             = refl
unzip∘zip (x ∷ xs) (y ∷ ys) =
  P.cong (Prod.map (x ∷_) (y ∷_)) (unzip∘zip xs ys)

zip∘unzip : ∀ {n} (xys : Vec (A × B) n) →
            uncurry zip (unzip xys) ≡ xys
zip∘unzip []              = refl
zip∘unzip ((x , y) ∷ xys) = P.cong ((x , y) ∷_) (zip∘unzip xys)

×v↔v× : ∀ {n} → (Vec A n × Vec B n) ↔ Vec (A × B) n
×v↔v× = inverse (uncurry zip) unzip (uncurry unzip∘zip) zip∘unzip

------------------------------------------------------------------------
-- _⊛_

lookup-⊛ : ∀ {n} i (fs : Vec (A → B) n) (xs : Vec A n) →
           lookup (fs ⊛ xs) i ≡ (lookup fs i $ lookup xs i)
lookup-⊛ zero    (f ∷ fs) (x ∷ xs) = refl
lookup-⊛ (suc i) (f ∷ fs) (x ∷ xs) = lookup-⊛ i fs xs

map-is-⊛ : ∀ {n} (f : A → B) (xs : Vec A n) →
           map f xs ≡ (replicate f ⊛ xs)
map-is-⊛ f []       = refl
map-is-⊛ f (x ∷ xs) = P.cong (_ ∷_) (map-is-⊛ f xs)

⊛-is-zipWith : ∀ {n} (fs : Vec (A → B) n) (xs : Vec A n) →
               (fs ⊛ xs) ≡ zipWith _$_ fs xs
⊛-is-zipWith []       []       = refl
⊛-is-zipWith (f ∷ fs) (x ∷ xs) = P.cong (f x ∷_) (⊛-is-zipWith fs xs)

zipWith-is-⊛ : ∀ {n} (f : A → B → C) (xs : Vec A n) (ys : Vec B n) →
               zipWith f xs ys ≡ (replicate f ⊛ xs ⊛ ys)
zipWith-is-⊛ f []       []       = refl
zipWith-is-⊛ f (x ∷ xs) (y ∷ ys) = P.cong (_ ∷_) (zipWith-is-⊛ f xs ys)

------------------------------------------------------------------------
-- foldr

-- See also Data.Vec.Properties.WithK.foldr-cong.

-- The (uniqueness part of the) universality property for foldr.

foldr-universal : ∀ {A : Set a} (B : ℕ → Set b)
                  (f : ∀ {n} → A → B n → B (suc n)) {e}
                  (h : ∀ {n} → Vec A n → B n) →
                  h [] ≡ e →
                  (∀ {n} x → h ∘ (x ∷_) ≗ f {n} x ∘ h) →
                  ∀ {n} → h ≗ foldr B {n} f e
foldr-universal B f {_} h base step []       = base
foldr-universal B f {e} h base step (x ∷ xs) = begin
  h (x ∷ xs)
    ≡⟨ step x xs ⟩
  f x (h xs)
    ≡⟨ P.cong (f x) (foldr-universal B f h base step xs) ⟩
  f x (foldr B f e xs)
    ∎
  where open P.≡-Reasoning

foldr-fusion : ∀ {A : Set a}
               {B : ℕ → Set b} {f : ∀ {n} → A → B n → B (suc n)} e
               {C : ℕ → Set c} {g : ∀ {n} → A → C n → C (suc n)}
               (h : ∀ {n} → B n → C n) →
               (∀ {n} x → h ∘ f {n} x ≗ g x ∘ h) →
               ∀ {n} → h ∘ foldr B {n} f e ≗ foldr C g (h e)
foldr-fusion {B = B} {f} e {C} h fuse =
  foldr-universal C _ _ refl (λ x xs → fuse x (foldr B f e xs))

idIsFold : ∀ {n} → id ≗ foldr (Vec A) {n} _∷_ []
idIsFold = foldr-universal _ _ id refl (λ _ _ → refl)

------------------------------------------------------------------------
-- sum

sum-++-commute : ∀ {m n} (xs : Vec ℕ m) {ys : Vec ℕ n} →
                 sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []       {_}  = refl
sum-++-commute (x ∷ xs) {ys} = begin
  x + sum (xs ++ ys)     ≡⟨ P.cong (x +_) (sum-++-commute xs) ⟩
  x + (sum xs + sum ys)  ≡⟨ P.sym (+-assoc x (sum xs) (sum ys)) ⟩
  sum (x ∷ xs) + sum ys  ∎
  where open P.≡-Reasoning

------------------------------------------------------------------------
-- replicate

lookup-replicate : ∀ {n} (i : Fin n) (x : A) →
                   lookup (replicate x) i ≡ x
lookup-replicate zero    = λ _ → refl
lookup-replicate (suc i) = lookup-replicate i

map-replicate :  ∀ (f : A → B) (x : A) n →
                 map f (replicate x) ≡ replicate {n = n} (f x)
map-replicate f x zero = refl
map-replicate f x (suc n) = P.cong (f x ∷_) (map-replicate f x n)

zipWith-replicate₁ : ∀ {n} (_⊕_ : A → B → C) (x : A) (ys : Vec B n) →
                   zipWith _⊕_ (replicate x) ys ≡ map (x ⊕_) ys
zipWith-replicate₁ _⊕_ x []       = refl
zipWith-replicate₁ _⊕_ x (y ∷ ys) =
  P.cong (x ⊕ y ∷_) (zipWith-replicate₁ _⊕_ x ys)

zipWith-replicate₂ : ∀ {n} (_⊕_ : A → B → C) (xs : Vec A n) (y : B) →
                   zipWith _⊕_ xs (replicate y) ≡ map (_⊕ y) xs
zipWith-replicate₂ _⊕_ []       y = refl
zipWith-replicate₂ _⊕_ (x ∷ xs) y =
  P.cong (x ⊕ y ∷_) (zipWith-replicate₂ _⊕_ xs y)

------------------------------------------------------------------------
-- tabulate

lookup∘tabulate : ∀ {n} (f : Fin n → A) (i : Fin n) →
                  lookup (tabulate f) i ≡ f i
lookup∘tabulate f zero    = refl
lookup∘tabulate f (suc i) = lookup∘tabulate (f ∘ suc) i

tabulate∘lookup : ∀ {n} (xs : Vec A n) → tabulate (lookup xs) ≡ xs
tabulate∘lookup []       = refl
tabulate∘lookup (x ∷ xs) = P.cong (x ∷_) (tabulate∘lookup xs)

tabulate-∘ : ∀ {n} (f : A → B) (g : Fin n → A) →
             tabulate (f ∘ g) ≡ map f (tabulate g)
tabulate-∘ {n = zero}  f g = refl
tabulate-∘ {n = suc n} f g = P.cong (f (g zero) ∷_) (tabulate-∘ f (g ∘ suc))

tabulate-cong : ∀ {n} {f g : Fin n → A} → f ≗ g → tabulate f ≡ tabulate g
tabulate-cong {n = zero}  p = refl
tabulate-cong {n = suc n} p = P.cong₂ _∷_ (p zero) (tabulate-cong (p ∘ suc))

------------------------------------------------------------------------
-- allFin

lookup-allFin : ∀ {n} (i : Fin n) → lookup (allFin n) i ≡ i
lookup-allFin = lookup∘tabulate id

allFin-map : ∀ n → allFin (suc n) ≡ zero ∷ map suc (allFin n)
allFin-map n = P.cong (zero ∷_) $ tabulate-∘ suc id

tabulate-allFin : ∀ {n} (f : Fin n → A) → tabulate f ≡ map f (allFin n)
tabulate-allFin f = tabulate-∘ f id

-- If you look up every possible index, in increasing order, then you
-- get back the vector you started with.

map-lookup-allFin : ∀ {n} (xs : Vec A n) →
                    map (lookup xs) (allFin n) ≡ xs
map-lookup-allFin {n = n} xs = begin
  map (lookup xs) (allFin n) ≡˘⟨ tabulate-∘ (lookup xs) id ⟩
  tabulate (lookup xs)       ≡⟨ tabulate∘lookup xs ⟩
  xs                         ∎
  where open P.≡-Reasoning

------------------------------------------------------------------------
-- count

module _ {P : Pred A p} (P? : Decidable P) where

  count≤n : ∀ {n} (xs : Vec A n) → count P? xs ≤ n
  count≤n []       = z≤n
  count≤n (x ∷ xs) with P? x
  ... | yes _ = s≤s (count≤n xs)
  ... | no  _ = ≤-step (count≤n xs)

------------------------------------------------------------------------
-- insert

insert-lookup : ∀ {n} (xs : Vec A n) (i : Fin (suc n)) (v : A) →
                lookup (insert xs i v) i ≡ v
insert-lookup xs       zero     v = refl
insert-lookup (x ∷ xs) (suc i)  v = insert-lookup xs i v

insert-punchIn : ∀ {n} (xs : Vec A n) (i : Fin (suc n)) (v : A)
                 (j : Fin n) →
                 lookup (insert xs i v) (Fin.punchIn i j) ≡ lookup xs j
insert-punchIn xs       zero     v j       = refl
insert-punchIn (x ∷ xs) (suc i)  v zero    = refl
insert-punchIn (x ∷ xs) (suc i)  v (suc j) = insert-punchIn xs i v j

remove-punchOut : ∀ {n} (xs : Vec A (suc n))
                  {i : Fin (suc n)} {j : Fin (suc n)} (i≢j : i ≢ j) →
                  lookup (remove xs i) (Fin.punchOut i≢j) ≡ lookup xs j
remove-punchOut (x ∷ xs) {zero} {zero} i≢j = ⊥-elim (i≢j refl)
remove-punchOut (x ∷ xs) {zero} {suc j} i≢j = refl
remove-punchOut (x ∷ y ∷ xs) {suc i} {zero} i≢j = refl
remove-punchOut (x ∷ y ∷ xs) {suc i} {suc j} i≢j =
  remove-punchOut (y ∷ xs) (i≢j ∘ P.cong suc)

------------------------------------------------------------------------
-- remove

remove-insert : ∀ {n} (xs : Vec A n) (i : Fin (suc n)) (v : A) →
                remove (insert xs i v) i ≡ xs
remove-insert xs           zero           v = refl
remove-insert (x ∷ xs)     (suc zero)     v = refl
remove-insert (x ∷ y ∷ xs) (suc (suc i))  v =
  P.cong (x ∷_) (remove-insert (y ∷ xs) (suc i) v)

insert-remove : ∀ {n} (xs : Vec A (suc n)) (i : Fin (suc n)) →
                insert (remove xs i) i (lookup xs i) ≡ xs
insert-remove (x ∷ xs)     zero     = refl
insert-remove (x ∷ y ∷ xs) (suc i)  =
  P.cong (x ∷_) (insert-remove (y ∷ xs) i)

------------------------------------------------------------------------
-- Conversion function

toList∘fromList : (xs : List A) → toList (fromList xs) ≡ xs
toList∘fromList List.[]       = refl
toList∘fromList (x List.∷ xs) = P.cong (x List.∷_) (toList∘fromList xs)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

lookup-++-inject+ = lookup-++ˡ
{-# WARNING_ON_USAGE lookup-++-inject+
"Warning: lookup-++-inject+ was deprecated in v1.1.
Please use lookup-++ˡ instead."
#-}
lookup-++-+′ = lookup-++ʳ
{-# WARNING_ON_USAGE lookup-++-+′
"Warning: lookup-++-+′ was deprecated in v1.1.
Please use lookup-++ʳ instead."
#-}
