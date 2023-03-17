------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vec-related properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Properties where

open import Algebra.Definitions
open import Data.Bool.Base using (true; false)
open import Data.Fin.Base as Fin using (Fin; zero; suc; toℕ; fromℕ<; _↑ˡ_; _↑ʳ_)
open import Data.List.Base as List using (List)
open import Data.Nat.Base
open import Data.Nat.Properties
  using (+-assoc; m≤n⇒m≤1+n; ≤-refl; ≤-trans; suc-injective)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; <_,_>; uncurry)
open import Data.Sum.Base using ([_,_]′)
open import Data.Sum.Properties using ([,]-map)
open import Data.Vec.Base
open import Function.Base
open import Function.Inverse using (_↔_; inverse)
open import Level using (Level)
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; _≗_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Decidable using (Dec; does; yes; no; _×-dec_; map′)
open import Relation.Nullary.Negation using (contradiction)

open ≡-Reasoning

private
  variable
    a b c d p : Level
    A B C D : Set a
    w x y z : A
    m n o : ℕ
    ws xs ys zs : Vec A n

------------------------------------------------------------------------
-- Properties of propositional equality over vectors

∷-injectiveˡ : x ∷ xs ≡ y ∷ ys → x ≡ y
∷-injectiveˡ refl = refl

∷-injectiveʳ : x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-injectiveʳ refl = refl

∷-injective : (x ∷ xs) ≡ (y ∷ ys) → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

≡-dec : DecidableEquality A → DecidableEquality (Vec A n)
≡-dec _≟_ []       []       = yes refl
≡-dec _≟_ (x ∷ xs) (y ∷ ys) = map′ (uncurry (cong₂ _∷_))
  ∷-injective (x ≟ y ×-dec ≡-dec _≟_ xs ys)

------------------------------------------------------------------------
-- _[_]=_

[]=-injective : ∀ {i} → xs [ i ]= x → xs [ i ]= y → x ≡ y
[]=-injective here          here          = refl
[]=-injective (there xsᵢ≡x) (there xsᵢ≡y) = []=-injective xsᵢ≡x xsᵢ≡y

-- See also Data.Vec.Properties.WithK.[]=-irrelevant.

------------------------------------------------------------------------
-- take

unfold-take : ∀ n x (xs : Vec A (n + m)) → take (suc n) (x ∷ xs) ≡ x ∷ take n xs
unfold-take n x xs with splitAt n xs
... | xs , ys , refl = refl

take-distr-zipWith : ∀ (f : A → B → C) →
                     (xs : Vec A (m + n)) (ys : Vec B (m + n)) →
                     take m (zipWith f xs ys) ≡ zipWith f (take m xs) (take m ys)
take-distr-zipWith {m = zero}  f xs       ys       = refl
take-distr-zipWith {m = suc m} f (x ∷ xs) (y ∷ ys) = begin
    take (suc m) (zipWith f (x ∷ xs) (y ∷ ys))
  ≡⟨⟩
    take (suc m) (f x y ∷ (zipWith f xs ys))
  ≡⟨ unfold-take m (f x y) (zipWith f xs ys) ⟩
    f x y ∷ take m (zipWith f xs ys)
  ≡⟨ cong (f x y ∷_) (take-distr-zipWith f xs ys) ⟩
    f x y ∷ (zipWith f (take m xs) (take m ys))
  ≡⟨⟩
    zipWith f (x ∷ (take m xs)) (y ∷ (take m ys))
  ≡˘⟨ cong₂ (zipWith f) (unfold-take m x xs) (unfold-take m y ys) ⟩
    zipWith f (take (suc m) (x ∷ xs)) (take (suc m) (y ∷ ys))
  ∎

take-distr-map : ∀ (f : A → B) (m : ℕ) (xs : Vec A (m + n)) →
                 take m (map f xs) ≡ map f (take m xs)
take-distr-map f zero xs = refl
take-distr-map f (suc m) (x ∷ xs) = begin
  take (suc m) (map f (x ∷ xs)) ≡⟨⟩
  take (suc m) (f x ∷ map f xs) ≡⟨ unfold-take m (f x) (map f xs) ⟩
  f x ∷ (take m (map f xs))     ≡⟨ cong (f x ∷_) (take-distr-map f m xs) ⟩
  f x ∷ (map f (take m xs))     ≡⟨⟩
  map f (x ∷ take m xs)         ≡˘⟨ cong (map f) (unfold-take m x xs) ⟩
  map f (take (suc m) (x ∷ xs)) ∎

------------------------------------------------------------------------
-- drop

unfold-drop : ∀ n x (xs : Vec A (n + m)) →
              drop (suc n) (x ∷ xs) ≡ drop n xs
unfold-drop n x xs with splitAt n xs
... | xs , ys , refl = refl

drop-distr-zipWith : (f : A → B → C) →
                     (x : Vec A (m + n)) (y : Vec B (m + n)) →
                     drop m (zipWith f x y) ≡ zipWith f (drop m x) (drop m y)
drop-distr-zipWith {m = zero} f   xs       ys = refl
drop-distr-zipWith {m = suc m} f (x ∷ xs) (y ∷ ys) = begin
    drop (suc m) (zipWith f (x ∷ xs) (y ∷ ys))
  ≡⟨⟩
    drop (suc m) (f x y ∷ (zipWith f xs ys))
  ≡⟨ unfold-drop m (f x y) (zipWith f xs ys) ⟩
    drop m (zipWith f xs ys)
  ≡⟨ drop-distr-zipWith f xs ys ⟩
    zipWith f (drop m xs) (drop m ys)
  ≡˘⟨ cong₂ (zipWith f) (unfold-drop m x xs) (unfold-drop m y ys) ⟩
    zipWith f (drop (suc m) (x ∷ xs)) (drop (suc m) (y ∷ ys))
  ∎

drop-distr-map : ∀ (f : A → B) (m : ℕ) (x : Vec A (m + n)) →
                 drop m (map f x) ≡ map f (drop m x)
drop-distr-map f zero x = refl
drop-distr-map f (suc m) (x ∷ xs) = begin
  drop (suc m) (map f (x ∷ xs)) ≡⟨⟩
  drop (suc m) (f x ∷ map f xs) ≡⟨  unfold-drop m (f x) (map f xs) ⟩
  drop m (map f xs)             ≡⟨  drop-distr-map f m xs ⟩
  map f (drop m xs)             ≡˘⟨ cong (map f) (unfold-drop m x xs) ⟩
  map f (drop (suc m) (x ∷ xs)) ∎

------------------------------------------------------------------------
-- take and drop together

take-drop-id : ∀ (m : ℕ) (x : Vec A (m + n)) → take m x ++ drop m x ≡ x
take-drop-id zero x = refl
take-drop-id (suc m) (x ∷ xs) = begin
    take (suc m) (x ∷ xs) ++ drop (suc m) (x ∷ xs)
  ≡⟨ cong₂ _++_ (unfold-take m x xs) (unfold-drop m x xs) ⟩
    (x ∷ take m xs) ++ (drop m xs)
  ≡⟨⟩
    x ∷ (take m xs ++ drop m xs)
  ≡⟨ cong (x ∷_) (take-drop-id m xs) ⟩
    x ∷ xs
  ∎

--------------------------------------------------------------------------------
-- truncate

truncate-refl : (xs : Vec A n) → truncate ≤-refl xs ≡ xs
truncate-refl []       = refl
truncate-refl (x ∷ xs) = cong (x ∷_) (truncate-refl xs)

truncate-trans : ∀ {p} (m≤n : m ≤ n) (n≤p : n ≤ p) (xs : Vec A p) →
                 truncate (≤-trans m≤n n≤p) xs ≡ truncate m≤n (truncate n≤p xs)
truncate-trans z≤n       n≤p       xs = refl
truncate-trans (s≤s m≤n) (s≤s n≤p) (x ∷ xs) = cong (x ∷_) (truncate-trans m≤n n≤p xs)

--------------------------------------------------------------------------------
-- pad

padRight-refl : (a : A) (xs : Vec A n) → padRight ≤-refl a xs ≡ xs
padRight-refl a []       = refl
padRight-refl a (x ∷ xs) = cong (x ∷_) (padRight-refl a xs)

padRight-replicate : (m≤n : m ≤ n) (a : A) → replicate a ≡ padRight m≤n a (replicate a)
padRight-replicate z≤n       a = refl
padRight-replicate (s≤s m≤n) a = cong (a ∷_) (padRight-replicate m≤n a)

padRight-trans : ∀ {p} (m≤n : m ≤ n) (n≤p : n ≤ p) (a : A) (xs : Vec A m) →
            padRight (≤-trans m≤n n≤p) a xs ≡ padRight n≤p a (padRight m≤n a xs)
padRight-trans z≤n       n≤p       a []       = padRight-replicate n≤p a
padRight-trans (s≤s m≤n) (s≤s n≤p) a (x ∷ xs) = cong (x ∷_) (padRight-trans m≤n n≤p a xs)

--------------------------------------------------------------------------------
-- truncate and padRight together

truncate-padRight : (m≤n : m ≤ n) (a : A) (xs : Vec A m) →
                    truncate m≤n (padRight m≤n a xs) ≡ xs
truncate-padRight z≤n       a []       = refl
truncate-padRight (s≤s m≤n) a (x ∷ xs) = cong (x ∷_) (truncate-padRight m≤n a xs)

------------------------------------------------------------------------
-- lookup

[]=⇒lookup : ∀ {i} → xs [ i ]= x → lookup xs i ≡ x
[]=⇒lookup here            = refl
[]=⇒lookup (there xs[i]=x) = []=⇒lookup xs[i]=x

lookup⇒[]= : ∀ (i : Fin n) xs → lookup xs i ≡ x → xs [ i ]= x
lookup⇒[]= zero    (_ ∷ _)  refl = here
lookup⇒[]= (suc i) (_ ∷ xs) p    = there (lookup⇒[]= i xs p)

[]=↔lookup : ∀ {i} → xs [ i ]= x ↔ lookup xs i ≡ x
[]=↔lookup {i = i} =
  inverse []=⇒lookup (lookup⇒[]= _ _)
          lookup⇒[]=∘[]=⇒lookup ([]=⇒lookup∘lookup⇒[]= _ i)
  where
  lookup⇒[]=∘[]=⇒lookup : ∀ {i} (p : xs [ i ]= x) →
                          lookup⇒[]= i xs ([]=⇒lookup p) ≡ p
  lookup⇒[]=∘[]=⇒lookup here      = refl
  lookup⇒[]=∘[]=⇒lookup (there p) = cong there (lookup⇒[]=∘[]=⇒lookup p)

  []=⇒lookup∘lookup⇒[]= : ∀ xs (i : Fin n) (p : lookup xs i ≡ x) →
                          []=⇒lookup (lookup⇒[]= i xs p) ≡ p
  []=⇒lookup∘lookup⇒[]= (x ∷ xs) zero    refl = refl
  []=⇒lookup∘lookup⇒[]= (x ∷ xs) (suc i) p    = []=⇒lookup∘lookup⇒[]= xs i p

lookup-inject≤-take : ∀ m (m≤m+n : m ≤ m + n) (i : Fin m) (xs : Vec A (m + n)) →
                      lookup xs (Fin.inject≤ i m≤m+n) ≡ lookup (take m xs) i
lookup-inject≤-take (suc m) m≤m+n zero (x ∷ xs)
  rewrite unfold-take m x xs = refl
lookup-inject≤-take (suc (suc m)) (s≤s m≤m+n) (suc zero) (x ∷ y ∷ xs)
  rewrite unfold-take (suc m) x (y ∷ xs) | unfold-take m y xs = refl
lookup-inject≤-take (suc (suc m)) (s≤s (s≤s m≤m+n)) (suc (suc i)) (x ∷ y ∷ xs)
  rewrite unfold-take (suc m) x (y ∷ xs) | unfold-take m y xs = lookup-inject≤-take m m≤m+n i xs

------------------------------------------------------------------------
-- updateAt (_[_]%=_)

-- (+) updateAt i actually updates the element at index i.

updateAt-updates : ∀ (i : Fin n) {f : A → A} (xs : Vec A n) →
                   xs [ i ]= x → (updateAt i f xs) [ i ]= f x
updateAt-updates zero    (x ∷ xs) here        = here
updateAt-updates (suc i) (x ∷ xs) (there loc) = there (updateAt-updates i xs loc)

-- (-) updateAt i does not touch the elements at other indices.

updateAt-minimal : ∀ (i j : Fin n) {f : A → A} (xs : Vec A n) →
                   i ≢ j → xs [ i ]= x → (updateAt j f xs) [ i ]= x
updateAt-minimal zero    zero    (x ∷ xs) 0≢0 here        = contradiction refl 0≢0
updateAt-minimal zero    (suc j) (x ∷ xs) _   here        = here
updateAt-minimal (suc i) zero    (x ∷ xs) _   (there loc) = there loc
updateAt-minimal (suc i) (suc j) (x ∷ xs) i≢j (there loc) =
  there (updateAt-minimal i j xs (i≢j ∘ cong suc) loc)

-- The other properties are consequences of (+) and (-).
-- We spell the most natural properties out.
-- Direct inductive proofs are in most cases easier than just using
-- the defining properties.

-- In the explanations, we make use of shorthand  f = g ↾ x
-- meaning that f and g agree locally at point x, i.e.  f x ≡ g x.

-- updateAt i  is a morphism from the monoid of endofunctions  A → A
-- to the monoid of endofunctions  Vec A n → Vec A n

-- 1a. local identity:  f = id ↾ (lookup xs i)
--             implies  updateAt i f = id ↾ xs

updateAt-id-local : ∀ (i : Fin n) {f : A → A} (xs : Vec A n) →
                    f (lookup xs i) ≡ lookup xs i →
                    updateAt i f xs ≡ xs
updateAt-id-local zero    (x ∷ xs) eq = cong (_∷ xs) eq
updateAt-id-local (suc i) (x ∷ xs) eq = cong (x ∷_) (updateAt-id-local i xs eq)

-- 1b. identity:  updateAt i id ≗ id

updateAt-id : ∀ (i : Fin n) (xs : Vec A n) → updateAt i id xs ≡ xs
updateAt-id i xs = updateAt-id-local i xs refl

-- 2a. local composition:  f ∘ g = h ↾ (lookup xs i)
--                implies  updateAt i f ∘ updateAt i g = updateAt i h ↾ xs

updateAt-∘-local : ∀ (i : Fin n) {f g h : A → A} (xs : Vec A n) →
                         f (g (lookup xs i)) ≡ h (lookup xs i) →
                         updateAt i f (updateAt i g xs) ≡ updateAt i h xs
updateAt-∘-local zero    (x ∷ xs) fg=h = cong (_∷ xs) fg=h
updateAt-∘-local (suc i) (x ∷ xs) fg=h = cong (x ∷_) (updateAt-∘-local i xs fg=h)

-- 2b. composition:  updateAt i f ∘ updateAt i g ≗ updateAt i (f ∘ g)

updateAt-∘ : ∀ (i : Fin n) {f g : A → A} →
                   updateAt i f ∘ updateAt i g ≗ updateAt i (f ∘ g)
updateAt-∘ i xs = updateAt-∘-local i xs refl

-- 3. congruence:  updateAt i  is a congruence wrt. extensional equality.

-- 3a.  If    f = g ↾ (lookup xs i)
--      then  updateAt i f = updateAt i g ↾ xs

updateAt-cong-local : ∀ (i : Fin n) {f g : A → A} (xs : Vec A n) →
                      f (lookup xs i) ≡ g (lookup xs i) →
                      updateAt i f xs ≡ updateAt i g xs
updateAt-cong-local zero    (x ∷ xs) f=g = cong (_∷ xs) f=g
updateAt-cong-local (suc i) (x ∷ xs) f=g = cong (x ∷_) (updateAt-cong-local i xs f=g)

-- 3b. congruence:  f ≗ g → updateAt i f ≗ updateAt i g

updateAt-cong : ∀ (i : Fin n) {f g : A → A} →
                f ≗ g → updateAt i f ≗ updateAt i g
updateAt-cong i f≗g xs = updateAt-cong-local i xs (f≗g (lookup xs i))

-- The order of updates at different indices i ≢ j does not matter.

-- This a consequence of updateAt-updates and updateAt-minimal
-- but easier to prove inductively.

updateAt-commutes : ∀ (i j : Fin n) {f g : A → A} → i ≢ j →
                    updateAt i f ∘ updateAt j g ≗ updateAt j g ∘ updateAt i f
updateAt-commutes zero    zero    0≢0 (x ∷ xs) = contradiction refl 0≢0
updateAt-commutes zero    (suc j) i≢j (x ∷ xs) = refl
updateAt-commutes (suc i) zero    i≢j (x ∷ xs) = refl
updateAt-commutes (suc i) (suc j) i≢j (x ∷ xs) =
  cong (x ∷_) (updateAt-commutes i j (i≢j ∘ cong suc) xs)

-- lookup after updateAt reduces.

-- For same index this is an easy consequence of updateAt-updates
-- using []=↔lookup.

lookup∘updateAt : ∀ (i : Fin n) {f : A → A} xs →
                  lookup (updateAt i f xs) i ≡ f (lookup xs i)
lookup∘updateAt i xs =
  []=⇒lookup (updateAt-updates i xs (lookup⇒[]= i _ refl))

-- For different indices it easily follows from updateAt-minimal.

lookup∘updateAt′ : ∀ (i j : Fin n) {f : A → A} → i ≢ j → ∀ xs →
                   lookup (updateAt j f xs) i ≡ lookup xs i
lookup∘updateAt′ i j xs i≢j =
  []=⇒lookup (updateAt-minimal i j i≢j xs (lookup⇒[]= i _ refl))

-- Aliases for notation _[_]%=_

[]%=-id : ∀ (xs : Vec A n) (i : Fin n) → xs [ i ]%= id ≡ xs
[]%=-id xs i = updateAt-id i xs

[]%=-∘ : ∀ (xs : Vec A n) (i : Fin n) {f g : A → A} →
     xs [ i ]%= f
        [ i ]%= g
   ≡ xs [ i ]%= g ∘ f
[]%=-∘ xs i = updateAt-∘ i xs


------------------------------------------------------------------------
-- _[_]≔_ (update)
--
-- _[_]≔_ is defined in terms of updateAt, and all of its properties
-- are special cases of the ones for updateAt.

[]≔-idempotent : ∀ (xs : Vec A n) (i : Fin n) →
                 (xs [ i ]≔ x) [ i ]≔ y ≡ xs [ i ]≔ y
[]≔-idempotent xs i = updateAt-∘ i xs

[]≔-commutes : ∀ (xs : Vec A n) (i j : Fin n) → i ≢ j →
               (xs [ i ]≔ x) [ j ]≔ y ≡ (xs [ j ]≔ y) [ i ]≔ x
[]≔-commutes xs i j i≢j = updateAt-commutes j i (i≢j ∘ sym) xs

[]≔-updates : ∀ (xs : Vec A n) (i : Fin n) → (xs [ i ]≔ x) [ i ]= x
[]≔-updates xs i = updateAt-updates i xs (lookup⇒[]= i xs refl)

[]≔-minimal : ∀ (xs : Vec A n) (i j : Fin n) → i ≢ j →
              xs [ i ]= x → (xs [ j ]≔ y) [ i ]= x
[]≔-minimal xs i j i≢j loc = updateAt-minimal i j xs i≢j loc

[]≔-lookup : ∀ (xs : Vec A n) (i : Fin n) → xs [ i ]≔ lookup xs i ≡ xs
[]≔-lookup xs i = updateAt-id-local i xs refl

[]≔-++-↑ˡ : ∀ (xs : Vec A m) (ys : Vec A n) i →
            (xs ++ ys) [ i ↑ˡ n ]≔ x ≡ (xs [ i ]≔ x) ++ ys
[]≔-++-↑ˡ (x ∷ xs) ys zero    = refl
[]≔-++-↑ˡ (x ∷ xs) ys (suc i) =
  cong (x ∷_) $ []≔-++-↑ˡ xs ys i

[]≔-++-↑ʳ : ∀ (xs : Vec A m) (ys : Vec A n) i →
            (xs ++ ys) [ m ↑ʳ i ]≔ y ≡ xs ++ (ys [ i ]≔ y)
[]≔-++-↑ʳ {m = zero}     []    (y ∷ ys) i = refl
[]≔-++-↑ʳ {m = suc n} (x ∷ xs) (y ∷ ys) i = cong (x ∷_) $ []≔-++-↑ʳ xs (y ∷ ys) i

lookup∘update : ∀ (i : Fin n) (xs : Vec A n) x →
                lookup (xs [ i ]≔ x) i ≡ x
lookup∘update i xs x = lookup∘updateAt i xs

lookup∘update′ : ∀ {i j} → i ≢ j → ∀ (xs : Vec A n) y →
                 lookup (xs [ j ]≔ y) i ≡ lookup xs i
lookup∘update′ {i = i} {j} i≢j xs y = lookup∘updateAt′ i j i≢j xs

------------------------------------------------------------------------
-- cast

toList-cast : ∀ .(eq : m ≡ n) (xs : Vec A m) → toList (cast eq xs) ≡ toList xs
toList-cast {n = zero}  eq []       = refl
toList-cast {n = suc _} eq (x ∷ xs) =
  cong (x List.∷_) (toList-cast (cong pred eq) xs)

cast-is-id : .(eq : m ≡ m) (xs : Vec A m) → cast eq xs ≡ xs
cast-is-id eq []       = refl
cast-is-id eq (x ∷ xs) = cong (x ∷_) (cast-is-id (suc-injective eq) xs)

subst-is-cast : (eq : m ≡ n) (xs : Vec A m) → subst (Vec A) eq xs ≡ cast eq xs
subst-is-cast refl xs = sym (cast-is-id refl xs)

cast-trans : .(eq₁ : m ≡ n) (eq₂ : n ≡ o) (xs : Vec A m) →
             cast eq₂ (cast eq₁ xs) ≡ cast (trans eq₁ eq₂) xs
cast-trans {m = zero}  {n = zero}  {o = zero}  eq₁ eq₂ [] = refl
cast-trans {m = suc _} {n = suc _} {o = suc _} eq₁ eq₂ (x ∷ xs) =
  cong (x ∷_) (cast-trans (suc-injective eq₁) (suc-injective eq₂) xs)

------------------------------------------------------------------------
-- map

map-id : map id ≗ id {A = Vec A n}
map-id []       = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

map-const : ∀ (xs : Vec A n) (y : B) → map (const y) xs ≡ replicate y
map-const []       _ = refl
map-const (_ ∷ xs) y = cong (y ∷_) (map-const xs y)

map-cast : (f : A → B) .(eq : m ≡ n) (xs : Vec A m) →
           map f (cast eq xs) ≡ cast eq (map f xs)
map-cast {n = zero}  f eq []       = refl
map-cast {n = suc _} f eq (x ∷ xs)
  = cong (f x ∷_) (map-cast f (suc-injective eq) xs)

map-++ : ∀ (f : A → B) (xs : Vec A m) (ys : Vec A n) →
         map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

map-cong : ∀ {f g : A → B} → f ≗ g → map {n = n} f ≗ map g
map-cong f≗g []       = refl
map-cong f≗g (x ∷ xs) = cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

map-∘ : ∀ (f : B → C) (g : A → B) →
        map {n = n} (f ∘ g) ≗ map f ∘ map g
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) = cong (f (g x) ∷_) (map-∘ f g xs)

lookup-map : ∀ (i : Fin n) (f : A → B) (xs : Vec A n) →
             lookup (map f xs) i ≡ f (lookup xs i)
lookup-map zero    f (x ∷ xs) = refl
lookup-map (suc i) f (x ∷ xs) = lookup-map i f xs

map-updateAt : ∀ {f : A → B} {g : A → A} {h : B → B}
               (xs : Vec A n) (i : Fin n) →
               f (g (lookup xs i)) ≡ h (f (lookup xs i)) →
               map f (updateAt i g xs) ≡ updateAt i h (map f xs)
map-updateAt (x ∷ xs) zero    eq = cong (_∷ _) eq
map-updateAt (x ∷ xs) (suc i) eq = cong (_ ∷_) (map-updateAt xs i eq)

map-[]≔ : ∀ (f : A → B) (xs : Vec A n) (i : Fin n) →
          map f (xs [ i ]≔ x) ≡ map f xs [ i ]≔ f x
map-[]≔ f xs i = map-updateAt xs i refl

map-⊛ : ∀ (f : A → B → C) (g : A → B) (xs : Vec A n) →
        (map f xs ⊛ map g xs) ≡ map (f ˢ g) xs
map-⊛ f g []       = refl
map-⊛ f g (x ∷ xs) = cong (f x (g x) ∷_) (map-⊛ f g xs)

------------------------------------------------------------------------
-- _++_

-- See also Data.Vec.Properties.WithK.++-assoc.

++-injectiveˡ : ∀ {n} (ws xs : Vec A n) → ws ++ ys ≡ xs ++ zs → ws ≡ xs
++-injectiveˡ []       []         _  = refl
++-injectiveˡ (_ ∷ ws) (_ ∷ xs) eq =
  cong₂ _∷_ (∷-injectiveˡ eq) (++-injectiveˡ _ _ (∷-injectiveʳ eq))

++-injectiveʳ : ∀ {n} (ws xs : Vec A n) → ws ++ ys ≡ xs ++ zs → ys ≡ zs
++-injectiveʳ []       []         eq = eq
++-injectiveʳ (x ∷ ws) (x′ ∷ xs) eq =
  ++-injectiveʳ ws xs (∷-injectiveʳ eq)

++-injective  : ∀ (ws xs : Vec A n) →
                ws ++ ys ≡ xs ++ zs → ws ≡ xs × ys ≡ zs
++-injective ws xs eq =
  (++-injectiveˡ ws xs eq , ++-injectiveʳ ws xs eq)

lookup-++-< : ∀ (xs : Vec A m) (ys : Vec A n) →
              ∀ i (i<m : toℕ i < m) →
              lookup (xs ++ ys) i  ≡ lookup xs (Fin.fromℕ< i<m)
lookup-++-< (x ∷ xs) ys zero    z<s       = refl
lookup-++-< (x ∷ xs) ys (suc i) (s<s i<m) = lookup-++-< xs ys i i<m

lookup-++-≥ : ∀ (xs : Vec A m) (ys : Vec A n) →
              ∀ i (i≥m : toℕ i ≥ m) →
              lookup (xs ++ ys) i ≡ lookup ys (Fin.reduce≥ i i≥m)
lookup-++-≥ []       ys i       i≥m       = refl
lookup-++-≥ (x ∷ xs) ys (suc i) (s≤s i≥m) = lookup-++-≥ xs ys i i≥m

lookup-++ˡ : ∀ (xs : Vec A m) (ys : Vec A n) i →
             lookup (xs ++ ys) (i ↑ˡ n) ≡ lookup xs i
lookup-++ˡ (x ∷ xs) ys zero    = refl
lookup-++ˡ (x ∷ xs) ys (suc i) = lookup-++ˡ xs ys i

lookup-++ʳ : ∀ (xs : Vec A m) (ys : Vec A n) i →
             lookup (xs ++ ys) (m ↑ʳ i) ≡ lookup ys i
lookup-++ʳ []       ys       zero    = refl
lookup-++ʳ []       (y ∷ xs) (suc i) = lookup-++ʳ [] xs i
lookup-++ʳ (x ∷ xs) ys       i       = lookup-++ʳ xs ys i

lookup-splitAt : ∀ m (xs : Vec A m) (ys : Vec A n) i →
                lookup (xs ++ ys) i ≡ [ lookup xs , lookup ys ]′
                (Fin.splitAt m i)
lookup-splitAt zero    []       ys i       = refl
lookup-splitAt (suc m) (x ∷ xs) ys zero    = refl
lookup-splitAt (suc m) (x ∷ xs) ys (suc i) = trans
  (lookup-splitAt m xs ys i)
  (sym ([,]-map (Fin.splitAt m i)))

------------------------------------------------------------------------
-- concat

lookup-cast : .(eq : m ≡ n) (xs : Vec A m) (i : Fin m) →
              lookup (cast eq xs) (Fin.cast eq i) ≡ lookup xs i
lookup-cast {n = suc _} eq (x ∷ _)  zero    = refl
lookup-cast {n = suc _} eq (_ ∷ xs) (suc i) =
  lookup-cast (suc-injective eq) xs i

lookup-cast₁ : .(eq : m ≡ n) (xs : Vec A m) (i : Fin n) →
               lookup (cast eq xs) i ≡ lookup xs (Fin.cast (sym eq) i)
lookup-cast₁ eq (x ∷ _)  zero    = refl
lookup-cast₁ eq (_ ∷ xs) (suc i) =
  lookup-cast₁ (suc-injective eq) xs i

lookup-cast₂ : .(eq : m ≡ n) (xs : Vec A n) (i : Fin m) →
               lookup xs (Fin.cast eq i) ≡ lookup (cast (sym eq) xs) i
lookup-cast₂ eq (x ∷ _)  zero    = refl
lookup-cast₂ eq (_ ∷ xs) (suc i) =
  lookup-cast₂ (suc-injective eq) xs i

lookup-concat : ∀ (xss : Vec (Vec A m) n) i j →
                lookup (concat xss) (Fin.combine i j) ≡ lookup (lookup xss i) j
lookup-concat (xs ∷ xss) zero j = lookup-++ˡ xs (concat xss) j
lookup-concat (xs ∷ xss) (suc i) j = begin
  lookup (concat (xs ∷ xss)) (Fin.combine (suc i) j)
    ≡⟨ lookup-++ʳ xs (concat xss) (Fin.combine i j) ⟩
  lookup (concat xss) (Fin.combine i j)
    ≡⟨ lookup-concat xss i j ⟩
  lookup (lookup (xs ∷ xss) (suc i)) j
    ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- zipWith

module _ {f : A → A → A} where

  zipWith-assoc : Associative _≡_ f →
                  Associative _≡_ (zipWith {n = n} f)
  zipWith-assoc assoc []       []       []       = refl
  zipWith-assoc assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    cong₂ _∷_ (assoc x y z) (zipWith-assoc assoc xs ys zs)

  zipWith-idem : Idempotent _≡_ f →
                 Idempotent _≡_ (zipWith {n = n} f)
  zipWith-idem idem []       = refl
  zipWith-idem idem (x ∷ xs) =
    cong₂ _∷_ (idem x) (zipWith-idem idem xs)

module _ {f : A → A → A} {e : A} where

  zipWith-identityˡ : LeftIdentity _≡_ e f →
                      LeftIdentity _≡_ (replicate e) (zipWith {n = n} f)
  zipWith-identityˡ idˡ []       = refl
  zipWith-identityˡ idˡ (x ∷ xs) =
    cong₂ _∷_ (idˡ x) (zipWith-identityˡ idˡ xs)

  zipWith-identityʳ : RightIdentity _≡_ e f →
                      RightIdentity _≡_ (replicate e) (zipWith {n = n} f)
  zipWith-identityʳ idʳ []       = refl
  zipWith-identityʳ idʳ (x ∷ xs) =
    cong₂ _∷_ (idʳ x) (zipWith-identityʳ idʳ xs)

  zipWith-zeroˡ : LeftZero _≡_ e f →
                  LeftZero _≡_ (replicate e) (zipWith {n = n} f)
  zipWith-zeroˡ zeˡ []       = refl
  zipWith-zeroˡ zeˡ (x ∷ xs) =
    cong₂ _∷_ (zeˡ x) (zipWith-zeroˡ zeˡ xs)

  zipWith-zeroʳ : RightZero _≡_ e f →
                  RightZero _≡_ (replicate e) (zipWith {n = n} f)
  zipWith-zeroʳ zeʳ []       = refl
  zipWith-zeroʳ zeʳ (x ∷ xs) =
    cong₂ _∷_ (zeʳ x) (zipWith-zeroʳ zeʳ xs)

module _ {f : A → A → A} {e : A} {⁻¹ : A → A} where

  zipWith-inverseˡ : LeftInverse _≡_ e ⁻¹ f →
                     LeftInverse _≡_ (replicate {n = n} e) (map ⁻¹) (zipWith f)
  zipWith-inverseˡ invˡ []       = refl
  zipWith-inverseˡ invˡ (x ∷ xs) =
    cong₂ _∷_ (invˡ x) (zipWith-inverseˡ invˡ xs)

  zipWith-inverseʳ : RightInverse _≡_ e ⁻¹ f →
                     RightInverse _≡_ (replicate {n = n} e) (map ⁻¹) (zipWith f)
  zipWith-inverseʳ invʳ []       = refl
  zipWith-inverseʳ invʳ (x ∷ xs) =
    cong₂ _∷_ (invʳ x) (zipWith-inverseʳ invʳ xs)

module _ {f g : A → A → A} where

  zipWith-distribˡ : _DistributesOverˡ_ _≡_ f g →
                     _DistributesOverˡ_ _≡_ (zipWith {n = n} f) (zipWith g)
  zipWith-distribˡ distribˡ []        []      []       = refl
  zipWith-distribˡ distribˡ (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    cong₂ _∷_ (distribˡ x y z) (zipWith-distribˡ distribˡ xs ys zs)

  zipWith-distribʳ : _DistributesOverʳ_ _≡_ f g →
                     _DistributesOverʳ_ _≡_ (zipWith {n = n} f) (zipWith g)
  zipWith-distribʳ distribʳ []        []      []       = refl
  zipWith-distribʳ distribʳ (x ∷ xs) (y ∷ ys) (z ∷ zs) =
    cong₂ _∷_ (distribʳ x y z) (zipWith-distribʳ distribʳ xs ys zs)

  zipWith-absorbs : _Absorbs_ _≡_ f g →
                   _Absorbs_ _≡_ (zipWith {n = n} f) (zipWith g)
  zipWith-absorbs abs []       []       = refl
  zipWith-absorbs abs (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ (abs x y) (zipWith-absorbs abs xs ys)

module _ {f : A → B → C} {g : B → A → C} where

  zipWith-comm : ∀ (comm : ∀ x y → f x y ≡ g y x) (xs : Vec A n) ys →
                 zipWith f xs ys ≡ zipWith g ys xs
  zipWith-comm comm []       []       = refl
  zipWith-comm comm (x ∷ xs) (y ∷ ys) =
    cong₂ _∷_ (comm x y) (zipWith-comm comm xs ys)

zipWith-map₁ : ∀ (_⊕_ : B → C → D) (f : A → B)
               (xs : Vec A n) (ys : Vec C n) →
               zipWith _⊕_ (map f xs) ys ≡ zipWith (λ x y → f x ⊕ y) xs ys
zipWith-map₁ _⊕_ f []       []       = refl
zipWith-map₁ _⊕_ f (x ∷ xs) (y ∷ ys) =
  cong (f x ⊕ y ∷_) (zipWith-map₁ _⊕_ f xs ys)

zipWith-map₂ : ∀ (_⊕_ : A → C → D) (f : B → C)
               (xs : Vec A n) (ys : Vec B n) →
               zipWith _⊕_ xs (map f ys) ≡ zipWith (λ x y → x ⊕ f y) xs ys
zipWith-map₂ _⊕_ f []       []       = refl
zipWith-map₂ _⊕_ f (x ∷ xs) (y ∷ ys) =
  cong (x ⊕ f y ∷_) (zipWith-map₂ _⊕_ f xs ys)

lookup-zipWith : ∀ (f : A → B → C) (i : Fin n) xs ys →
                 lookup (zipWith f xs ys) i ≡ f (lookup xs i) (lookup ys i)
lookup-zipWith _ zero    (x ∷ _)  (y ∷ _)   = refl
lookup-zipWith _ (suc i) (_ ∷ xs) (_ ∷ ys)  = lookup-zipWith _ i xs ys

------------------------------------------------------------------------
-- zip

lookup-zip : ∀ (i : Fin n) (xs : Vec A n) (ys : Vec B n) →
             lookup (zip xs ys) i ≡ (lookup xs i , lookup ys i)
lookup-zip = lookup-zipWith _,_

-- map lifts projections to vectors of products.

map-proj₁-zip : ∀ (xs : Vec A n) (ys : Vec B n) →
                map proj₁ (zip xs ys) ≡ xs
map-proj₁-zip []       []       = refl
map-proj₁-zip (x ∷ xs) (y ∷ ys) = cong (x ∷_) (map-proj₁-zip xs ys)

map-proj₂-zip : ∀ (xs : Vec A n) (ys : Vec B n) →
                map proj₂ (zip xs ys) ≡ ys
map-proj₂-zip []       []       = refl
map-proj₂-zip (x ∷ xs) (y ∷ ys) = cong (y ∷_) (map-proj₂-zip xs ys)

-- map lifts pairing to vectors of products.

map-<,>-zip : ∀ (f : A → B) (g : A → C) (xs : Vec A n) →
              map < f , g > xs ≡ zip (map f xs) (map g xs)
map-<,>-zip f g []       = refl
map-<,>-zip f g (x ∷ xs) = cong (_ ∷_) (map-<,>-zip f g xs)

map-zip : ∀ (f : A → B) (g : C → D) (xs : Vec A n) (ys : Vec C n) →
          map (Prod.map f g) (zip xs ys) ≡ zip (map f xs) (map g ys)
map-zip f g []       []       = refl
map-zip f g (x ∷ xs) (y ∷ ys) = cong (_ ∷_) (map-zip f g xs ys)

------------------------------------------------------------------------
-- unzip

lookup-unzip : ∀ (i : Fin n) (xys : Vec (A × B) n) →
               let xs , ys = unzip xys
               in (lookup xs i , lookup ys i) ≡ lookup xys i
lookup-unzip ()      []
lookup-unzip zero    ((x , y) ∷ xys) = refl
lookup-unzip (suc i) ((x , y) ∷ xys) = lookup-unzip i xys

map-unzip : ∀ (f : A → B) (g : C → D) (xys : Vec (A × C) n) →
            let xs , ys = unzip xys
            in (map f xs , map g ys) ≡ unzip (map (Prod.map f g) xys)
map-unzip f g []              = refl
map-unzip f g ((x , y) ∷ xys) =
  cong (Prod.map (f x ∷_) (g y ∷_)) (map-unzip f g xys)

-- Products of vectors are isomorphic to vectors of products.

unzip∘zip : ∀ (xs : Vec A n) (ys : Vec B n) →
            unzip (zip xs ys) ≡ (xs , ys)
unzip∘zip [] []             = refl
unzip∘zip (x ∷ xs) (y ∷ ys) =
  cong (Prod.map (x ∷_) (y ∷_)) (unzip∘zip xs ys)

zip∘unzip : ∀ (xys : Vec (A × B) n) → uncurry zip (unzip xys) ≡ xys
zip∘unzip []         = refl
zip∘unzip (xy ∷ xys) = cong (xy ∷_) (zip∘unzip xys)

×v↔v× : (Vec A n × Vec B n) ↔ Vec (A × B) n
×v↔v× = inverse (uncurry zip) unzip (uncurry unzip∘zip) zip∘unzip

------------------------------------------------------------------------
-- _⊛_

lookup-⊛ : ∀ i (fs : Vec (A → B) n) (xs : Vec A n) →
           lookup (fs ⊛ xs) i ≡ (lookup fs i $ lookup xs i)
lookup-⊛ zero    (f ∷ fs) (x ∷ xs) = refl
lookup-⊛ (suc i) (f ∷ fs) (x ∷ xs) = lookup-⊛ i fs xs

map-is-⊛ : ∀ (f : A → B) (xs : Vec A n) →
           map f xs ≡ (replicate f ⊛ xs)
map-is-⊛ f []       = refl
map-is-⊛ f (x ∷ xs) = cong (_ ∷_) (map-is-⊛ f xs)

⊛-is-zipWith : ∀ (fs : Vec (A → B) n) (xs : Vec A n) →
               (fs ⊛ xs) ≡ zipWith _$_ fs xs
⊛-is-zipWith []       []       = refl
⊛-is-zipWith (f ∷ fs) (x ∷ xs) = cong (f x ∷_) (⊛-is-zipWith fs xs)

zipWith-is-⊛ : ∀ (f : A → B → C) (xs : Vec A n) (ys : Vec B n) →
               zipWith f xs ys ≡ (replicate f ⊛ xs ⊛ ys)
zipWith-is-⊛ f []       []       = refl
zipWith-is-⊛ f (x ∷ xs) (y ∷ ys) = cong (_ ∷_) (zipWith-is-⊛ f xs ys)

⊛-is->>= : ∀ (fs : Vec (A → B) n) (xs : Vec A n) →
           (fs ⊛ xs) ≡ (fs DiagonalBind.>>= flip map xs)
⊛-is->>= []       []       = refl
⊛-is->>= (f ∷ fs) (x ∷ xs) = cong (f x ∷_) $ begin
  fs ⊛ xs                                          ≡⟨ ⊛-is->>= fs xs ⟩
  diagonal (map (flip map xs) fs)                  ≡⟨⟩
  diagonal (map (tail ∘ flip map (x ∷ xs)) fs)     ≡⟨ cong diagonal (map-∘ _ _ _) ⟩
  diagonal (map tail (map (flip map (x ∷ xs)) fs)) ∎

------------------------------------------------------------------------
-- _⊛*_

lookup-⊛* : ∀ (fs : Vec (A → B) m) (xs : Vec A n) i j →
            lookup (fs ⊛* xs) (Fin.combine i j) ≡ (lookup fs i $ lookup xs j)
lookup-⊛* (f ∷ fs) xs zero j = trans (lookup-++ˡ (map f xs) _ j) (lookup-map j f xs)
lookup-⊛* (f ∷ fs) xs (suc i) j = trans (lookup-++ʳ (map f xs) _ (Fin.combine i j)) (lookup-⊛* fs xs i j)

------------------------------------------------------------------------
-- foldl

-- The (uniqueness part of the) universality property for foldl.

foldl-universal : ∀ (B : ℕ → Set b) (f : FoldlOp A B) e
                  (h : ∀ {c} (C : ℕ → Set c) (g : FoldlOp A C) (e : C zero) →
                       ∀ {n} → Vec A n → C n) →
                  (∀ {c} {C} {g : FoldlOp A C} e → h {c} C g e [] ≡ e) →
                  (∀ {c} {C} {g : FoldlOp A C} e {n} x →
                   (h {c} C g e {suc n}) ∘ (x ∷_) ≗ h (C ∘ suc) g (g e x)) →
                  h B f e ≗ foldl {n = n} B f e
foldl-universal B f e h base step []       = base e
foldl-universal B f e h base step (x ∷ xs) = begin
  h B f e (x ∷ xs)             ≡⟨ step e x xs ⟩
  h (B ∘ suc) f (f e x) xs     ≡⟨ foldl-universal _ f (f e x) h base step xs ⟩
  foldl (B ∘ suc) f (f e x) xs ≡⟨⟩
  foldl B f e (x ∷ xs)         ∎

foldl-fusion : ∀ {B : ℕ → Set b} {C : ℕ → Set c}
               (h : ∀ {n} → B n → C n) →
               {f : FoldlOp A B} {d : B zero} →
               {g : FoldlOp A C} {e : C zero} →
               (h d ≡ e) →
               (∀ {n} b x → h (f {n} b x) ≡ g (h b) x) →
               h ∘ foldl {n = n} B f d ≗ foldl C g e
foldl-fusion h {f} {d} {g} {e} base fuse []       = base
foldl-fusion h {f} {d} {g} {e} base fuse (x ∷ xs) =
  foldl-fusion h eq fuse xs
  where
    eq : h (f d x) ≡ g e x
    eq = begin
      h (f d x) ≡⟨ fuse d x ⟩
      g (h d) x ≡⟨ cong (λ e → g e x) base ⟩
      g e x     ∎

foldl-[] : ∀ (B : ℕ → Set b) (f : FoldlOp A B) {e} → foldl B f e [] ≡ e
foldl-[] _ _ = refl

------------------------------------------------------------------------
-- foldr

-- See also Data.Vec.Properties.WithK.foldr-cong.

-- The (uniqueness part of the) universality property for foldr.

module _ (B : ℕ → Set b) (f : FoldrOp A B) {e : B zero} where

  foldr-universal : (h : ∀ {n} → Vec A n → B n) →
                    h [] ≡ e →
                    (∀ {n} x → h ∘ (x ∷_) ≗ f {n} x ∘ h) →
                    h ≗ foldr {n = n} B f e
  foldr-universal h base step []       = base
  foldr-universal h base step (x ∷ xs) = begin
    h (x ∷ xs)           ≡⟨ step x xs ⟩
    f x (h xs)           ≡⟨ cong (f x) (foldr-universal h base step xs) ⟩
    f x (foldr B f e xs) ∎

  foldr-[] : foldr B f e [] ≡ e
  foldr-[] = refl

  foldr-++ : ∀ (xs : Vec A m) →
             foldr B f e (xs ++ ys) ≡ foldr (B ∘ (_+ n)) f (foldr B f e ys) xs
  foldr-++ []       = refl
  foldr-++ (x ∷ xs) = cong (f x) (foldr-++ xs)

-- fusion and identity as consequences of universality

foldr-fusion : ∀ {B : ℕ → Set b} {f : FoldrOp A B} e
                 {C : ℕ → Set c} {g : FoldrOp A C}
               (h : ∀ {n} → B n → C n) →
               (∀ {n} x → h ∘ f {n} x ≗ g x ∘ h) →
               h ∘ foldr {n = n} B f e ≗ foldr C g (h e)
foldr-fusion {B = B} {f} e {C} h fuse =
  foldr-universal C _ _ refl (λ x xs → fuse x (foldr B f e xs))

id-is-foldr : id ≗ foldr {n = n} (Vec A) _∷_ []
id-is-foldr = foldr-universal _ _ id refl (λ _ _ → refl)

map-is-foldr : ∀ (f : A → B) →
               map {n = n} f ≗ foldr (Vec B) (λ x ys → f x ∷ ys) []
map-is-foldr f = foldr-universal (Vec _) (λ x ys → f x ∷ ys) (map f) refl (λ _ _ → refl)

++-is-foldr : ∀ (xs : Vec A m) →
              xs ++ ys ≡ foldr (Vec A ∘ (_+ n)) _∷_ ys xs
++-is-foldr {A = A} {n = n} {ys} xs =
  foldr-universal (Vec A ∘ (_+ n)) _∷_ (_++ ys) refl (λ _ _ → refl) xs

------------------------------------------------------------------------
-- _∷ʳ_

∷ʳ-injective : ∀ (xs ys : Vec A n) → xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys × x ≡ y
∷ʳ-injective []       []        refl = (refl , refl)
∷ʳ-injective (x ∷ xs) (y  ∷ ys) eq   with ∷-injective eq
... | refl , eq′ = Prod.map₁ (cong (x ∷_)) (∷ʳ-injective xs ys eq′)

∷ʳ-injectiveˡ : ∀ (xs ys : Vec A n) → xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys
∷ʳ-injectiveˡ xs ys eq = proj₁ (∷ʳ-injective xs ys eq)

∷ʳ-injectiveʳ : ∀ (xs ys : Vec A n) → xs ∷ʳ x ≡ ys ∷ʳ y → x ≡ y
∷ʳ-injectiveʳ xs ys eq = proj₂ (∷ʳ-injective xs ys eq)

foldl-∷ʳ : ∀ (B : ℕ → Set b) (f : FoldlOp A B) e y (ys : Vec A n) →
           foldl B f e (ys ∷ʳ y) ≡ f (foldl B f e ys) y
foldl-∷ʳ B f e y []       = refl
foldl-∷ʳ B f e y (x ∷ xs) = foldl-∷ʳ (B ∘ suc) f (f e x) y xs

foldr-∷ʳ : ∀ (B : ℕ → Set b) (f : FoldrOp A B) {e} y (ys : Vec A n) →
           foldr B f e (ys ∷ʳ y) ≡ foldr (B ∘ suc) f (f y e) ys
foldr-∷ʳ B f y []       = refl
foldr-∷ʳ B f y (x ∷ xs) = cong (f x) (foldr-∷ʳ B f y xs)

-- map and _∷ʳ_

map-∷ʳ : ∀ (f : A → B) x (xs : Vec A n) → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
map-∷ʳ f x []       = refl
map-∷ʳ f x (y ∷ xs) = cong (f y ∷_) (map-∷ʳ f x xs)

------------------------------------------------------------------------
-- reverse

-- reverse of cons is snoc of reverse.

reverse-∷ : ∀ x (xs : Vec A n) → reverse (x ∷ xs) ≡ reverse xs ∷ʳ x
reverse-∷ x xs = sym (foldl-fusion (_∷ʳ x) refl (λ b x → refl) xs)

-- foldl after a reverse is a foldr

foldl-reverse : ∀ (B : ℕ → Set b) (f : FoldlOp A B) {e} →
                foldl {n = n} B f e ∘ reverse ≗ foldr B (flip f) e
foldl-reverse _ _ {e} []       = refl
foldl-reverse B f {e} (x ∷ xs) = begin
  foldl B f e (reverse (x ∷ xs)) ≡⟨ cong (foldl B f e) (reverse-∷ x xs) ⟩
  foldl B f e (reverse xs ∷ʳ x)  ≡⟨ foldl-∷ʳ B f e x (reverse xs) ⟩
  f (foldl B f e (reverse xs)) x ≡⟨ cong (flip f x) (foldl-reverse B f xs) ⟩
  f (foldr B (flip f) e xs) x    ≡⟨⟩
  foldr B (flip f) e (x ∷ xs)    ∎

-- foldr after a reverse is a foldl

foldr-reverse : ∀ (B : ℕ → Set b) (f : FoldrOp A B) {e} →
                foldr {n = n} B f e ∘ reverse ≗ foldl B (flip f) e
foldr-reverse B f {e} xs = foldl-fusion (foldr B f e) refl (λ _ _ → refl) xs

-- reverse is involutive.

reverse-involutive : Involutive {A = Vec A n} _≡_ reverse
reverse-involutive xs = begin
  reverse (reverse xs)    ≡⟨  foldl-reverse (Vec _) (flip _∷_) xs ⟩
  foldr (Vec _) _∷_ [] xs ≡˘⟨ id-is-foldr xs ⟩
  xs                      ∎

reverse-reverse : reverse xs ≡ ys → reverse ys ≡ xs
reverse-reverse {xs = xs} {ys} eq =  begin
  reverse ys           ≡˘⟨ cong reverse eq ⟩
  reverse (reverse xs) ≡⟨  reverse-involutive xs ⟩
  xs                   ∎

-- reverse is injective.

reverse-injective : reverse xs ≡ reverse ys → xs ≡ ys
reverse-injective {xs = xs} {ys} eq = begin
  xs                   ≡˘⟨ reverse-reverse eq ⟩
  reverse (reverse ys) ≡⟨  reverse-involutive ys ⟩
  ys                   ∎

-- map and reverse

map-reverse : ∀ (f : A → B) (xs : Vec A n) →
              map f (reverse xs) ≡ reverse (map f xs)
map-reverse f []       = refl
map-reverse f (x ∷ xs) = begin
  map f (reverse (x ∷ xs))  ≡⟨  cong (map f) (reverse-∷ x xs) ⟩
  map f (reverse xs ∷ʳ x)   ≡⟨  map-∷ʳ f x (reverse xs) ⟩
  map f (reverse xs) ∷ʳ f x ≡⟨  cong (_∷ʳ f x) (map-reverse f xs ) ⟩
  reverse (map f xs) ∷ʳ f x ≡˘⟨ reverse-∷ (f x) (map f xs) ⟩
  reverse (f x ∷ map f xs)  ≡⟨⟩
  reverse (map f (x ∷ xs))  ∎

------------------------------------------------------------------------
-- _ʳ++_

-- reverse-append is append of reverse.

unfold-ʳ++ : ∀ (xs : Vec A m) (ys : Vec A n) → xs ʳ++ ys ≡ reverse xs ++ ys
unfold-ʳ++ xs ys = sym (foldl-fusion (_++ ys) refl (λ b x → refl) xs)

-- foldr after a reverse-append is a foldl

foldr-ʳ++ : ∀ (B : ℕ → Set b) (f : FoldrOp A B) {e}
            (xs : Vec A m) {ys : Vec A n} →
            foldr B f e (xs ʳ++ ys) ≡
            foldl (B ∘ (_+ n)) (flip f) (foldr B f e ys) xs
foldr-ʳ++ B f {e} xs = foldl-fusion (foldr B f e) refl (λ _ _ → refl) xs

-- map and _ʳ++_

map-ʳ++ : ∀ (f : A → B) (xs : Vec A m) →
          map f (xs ʳ++ ys) ≡ map f xs ʳ++ map f ys
map-ʳ++ {ys = ys} f xs = begin
  map f (xs ʳ++ ys)              ≡⟨  cong (map f) (unfold-ʳ++ xs ys) ⟩
  map f (reverse xs ++ ys)       ≡⟨  map-++ f (reverse xs) ys ⟩
  map f (reverse xs) ++ map f ys ≡⟨  cong (_++ map f ys) (map-reverse f xs) ⟩
  reverse (map f xs) ++ map f ys ≡˘⟨ unfold-ʳ++ (map f xs) (map f ys) ⟩
  map f xs ʳ++ map f ys          ∎

------------------------------------------------------------------------
-- sum

sum-++ : ∀ (xs : Vec ℕ m) → sum (xs ++ ys) ≡ sum xs + sum ys
sum-++ {_}       []       = refl
sum-++ {ys = ys} (x ∷ xs) = begin
  x + sum (xs ++ ys)     ≡⟨  cong (x +_) (sum-++ xs) ⟩
  x + (sum xs + sum ys)  ≡˘⟨ +-assoc x (sum xs) (sum ys) ⟩
  sum (x ∷ xs) + sum ys  ∎

------------------------------------------------------------------------
-- replicate

lookup-replicate : ∀ (i : Fin n) (x : A) → lookup (replicate x) i ≡ x
lookup-replicate zero    x = refl
lookup-replicate (suc i) x = lookup-replicate i x

map-replicate :  ∀ (f : A → B) (x : A) n →
                 map f (replicate x) ≡ replicate {n = n} (f x)
map-replicate f x zero = refl
map-replicate f x (suc n) = cong (f x ∷_) (map-replicate f x n)

transpose-replicate : ∀ (xs : Vec A m) →
                      transpose (replicate {n = n} xs) ≡ map replicate xs
transpose-replicate {n = zero}  _  = sym (map-const _ [])
transpose-replicate {n = suc n} xs = begin
  transpose (replicate xs)                        ≡⟨⟩
  (replicate _∷_ ⊛ xs ⊛ transpose (replicate xs)) ≡⟨ cong₂ _⊛_ (sym (map-is-⊛ _∷_ xs)) (transpose-replicate xs) ⟩
  (map _∷_ xs ⊛ map replicate xs)                 ≡⟨ map-⊛ _∷_ replicate xs ⟩
  map replicate xs                                ∎

zipWith-replicate : ∀ (_⊕_ : A → B → C) (x : A) (y : B) →
                    zipWith {n = n} _⊕_ (replicate x) (replicate y) ≡ replicate (x ⊕ y)
zipWith-replicate {n = zero}  _⊕_ x y = refl
zipWith-replicate {n = suc n} _⊕_ x y = cong (x ⊕ y ∷_) (zipWith-replicate _⊕_ x y)

zipWith-replicate₁ : ∀ (_⊕_ : A → B → C) (x : A) (ys : Vec B n) →
                     zipWith _⊕_ (replicate x) ys ≡ map (x ⊕_) ys
zipWith-replicate₁ _⊕_ x []       = refl
zipWith-replicate₁ _⊕_ x (y ∷ ys) =
  cong (x ⊕ y ∷_) (zipWith-replicate₁ _⊕_ x ys)

zipWith-replicate₂ : ∀ (_⊕_ : A → B → C) (xs : Vec A n) (y : B) →
                     zipWith _⊕_ xs (replicate y) ≡ map (_⊕ y) xs
zipWith-replicate₂ _⊕_ []       y = refl
zipWith-replicate₂ _⊕_ (x ∷ xs) y =
  cong (x ⊕ y ∷_) (zipWith-replicate₂ _⊕_ xs y)

------------------------------------------------------------------------
-- tabulate

lookup∘tabulate : ∀ (f : Fin n → A) (i : Fin n) →
                  lookup (tabulate f) i ≡ f i
lookup∘tabulate f zero    = refl
lookup∘tabulate f (suc i) = lookup∘tabulate (f ∘ suc) i

tabulate∘lookup : ∀ (xs : Vec A n) → tabulate (lookup xs) ≡ xs
tabulate∘lookup []       = refl
tabulate∘lookup (x ∷ xs) = cong (x ∷_) (tabulate∘lookup xs)

tabulate-∘ : ∀ (f : A → B) (g : Fin n → A) →
             tabulate (f ∘ g) ≡ map f (tabulate g)
tabulate-∘ {n = zero}  f g = refl
tabulate-∘ {n = suc n} f g = cong (f (g zero) ∷_) (tabulate-∘ f (g ∘ suc))

tabulate-cong : ∀ {f g : Fin n → A} → f ≗ g → tabulate f ≡ tabulate g
tabulate-cong {n = zero}  p = refl
tabulate-cong {n = suc n} p = cong₂ _∷_ (p zero) (tabulate-cong (p ∘ suc))

------------------------------------------------------------------------
-- allFin

lookup-allFin : ∀ (i : Fin n) → lookup (allFin n) i ≡ i
lookup-allFin = lookup∘tabulate id

allFin-map : ∀ n → allFin (suc n) ≡ zero ∷ map suc (allFin n)
allFin-map n = cong (zero ∷_) $ tabulate-∘ suc id

tabulate-allFin : ∀ (f : Fin n → A) → tabulate f ≡ map f (allFin n)
tabulate-allFin f = tabulate-∘ f id

-- If you look up every possible index, in increasing order, then you
-- get back the vector you started with.

map-lookup-allFin : ∀ (xs : Vec A n) → map (lookup xs) (allFin n) ≡ xs
map-lookup-allFin {n = n} xs = begin
  map (lookup xs) (allFin n) ≡˘⟨ tabulate-∘ (lookup xs) id ⟩
  tabulate (lookup xs)       ≡⟨ tabulate∘lookup xs ⟩
  xs                         ∎

------------------------------------------------------------------------
-- count

module _ {P : Pred A p} (P? : Decidable P) where

  count≤n : ∀ (xs : Vec A n) → count P? xs ≤ n
  count≤n []       = z≤n
  count≤n (x ∷ xs) with does (P? x)
  ... | true  = s≤s (count≤n xs)
  ... | false = m≤n⇒m≤1+n (count≤n xs)

------------------------------------------------------------------------
-- insert

insert-lookup : ∀ (xs : Vec A n) (i : Fin (suc n)) (v : A) →
                lookup (insert xs i v) i ≡ v
insert-lookup xs       zero     v = refl
insert-lookup (x ∷ xs) (suc i)  v = insert-lookup xs i v

insert-punchIn : ∀ (xs : Vec A n) (i : Fin (suc n)) (v : A) (j : Fin n) →
                 lookup (insert xs i v) (Fin.punchIn i j) ≡ lookup xs j
insert-punchIn xs       zero     v j       = refl
insert-punchIn (x ∷ xs) (suc i)  v zero    = refl
insert-punchIn (x ∷ xs) (suc i)  v (suc j) = insert-punchIn xs i v j

remove-punchOut : ∀ (xs : Vec A (suc n)) {i} {j} (i≢j : i ≢ j) →
                  lookup (remove xs i) (Fin.punchOut i≢j) ≡ lookup xs j
remove-punchOut (x ∷ xs)     {zero}  {zero}  i≢j = contradiction refl i≢j
remove-punchOut (x ∷ xs)     {zero}  {suc j} i≢j = refl
remove-punchOut (x ∷ y ∷ xs) {suc i} {zero}  i≢j = refl
remove-punchOut (x ∷ y ∷ xs) {suc i} {suc j} i≢j =
  remove-punchOut (y ∷ xs) (i≢j ∘ cong suc)

------------------------------------------------------------------------
-- remove

remove-insert : ∀ (xs : Vec A n) (i : Fin (suc n)) (v : A) →
                remove (insert xs i v) i ≡ xs
remove-insert xs           zero           v = refl
remove-insert (x ∷ xs)     (suc zero)     v = refl
remove-insert (x ∷ y ∷ xs) (suc (suc i))  v =
  cong (x ∷_) (remove-insert (y ∷ xs) (suc i) v)

insert-remove : ∀ (xs : Vec A (suc n)) (i : Fin (suc n)) →
                insert (remove xs i) i (lookup xs i) ≡ xs
insert-remove (x ∷ xs)     zero     = refl
insert-remove (x ∷ y ∷ xs) (suc i)  =
  cong (x ∷_) (insert-remove (y ∷ xs) i)

------------------------------------------------------------------------
-- Conversion function

toList∘fromList : (xs : List A) → toList (fromList xs) ≡ xs
toList∘fromList List.[]       = refl
toList∘fromList (x List.∷ xs) = cong (x List.∷_) (toList∘fromList xs)


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

[]%=-compose = []%=-∘
{-# WARNING_ON_USAGE []%=-compose
"Warning: []%=-compose was deprecated in v2.0.
Please use []%=-∘ instead."
#-}

[]≔-++-inject+ : ∀ {m n x} (xs : Vec A m) (ys : Vec A n) i →
                 (xs ++ ys) [ i ↑ˡ n ]≔ x ≡ (xs [ i ]≔ x) ++ ys
[]≔-++-inject+ = []≔-++-↑ˡ
{-# WARNING_ON_USAGE []≔-++-inject+
"Warning: []≔-++-inject+ was deprecated in v2.0.
Please use []≔-++-↑ˡ instead."
#-}
idIsFold = id-is-foldr
{-# WARNING_ON_USAGE idIsFold
"Warning: idIsFold was deprecated in v2.0.
Please use id-is-foldr instead."
#-}
sum-++-commute = sum-++
{-# WARNING_ON_USAGE sum-++-commute
"Warning: sum-++-commute was deprecated in v2.0.
Please use sum-++ instead."
#-}
