------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vec-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Properties where

open import Algebra.Definitions
open import Data.Bool.Base using (true; false)
open import Data.Fin.Base as Fin
  using (Fin; zero; suc; toℕ; fromℕ<; _↑ˡ_; _↑ʳ_; inject≤)
open import Data.List.Base as List using (List)
import Data.List.Properties as List
open import Data.Nat.Base
  using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; pred; s<s⁻¹; _≥_; s≤s⁻¹; z≤n; _∸_)
open import Data.Nat.Properties
  using (suc-injective; +-assoc;  +-comm; +-suc; +-identityʳ
        ; m≤n⇒m≤1+n; m≤m+n; suc[m]≤n⇒m≤pred[n]
        ; ≤-refl; ≤-trans; ≤-irrelevant; ≤⇒≤″; m≤n⇒∃[o]m+o≡n
        )
open import Data.Product.Base as Product
  using (_×_; _,_; proj₁; proj₂; <_,_>; uncurry)
open import Data.Sum.Base using ([_,_]′)
open import Data.Sum.Properties using ([,]-map)
open import Data.Vec.Base
open import Data.Vec.Relation.Binary.Equality.Cast as VecCast
  using (_≈[_]_; ≈-sym; ≈-cong′; module CastReasoning)
open import Function.Base using (_∘_; id; _$_; const; _ˢ_; flip)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Level using (Level)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; _≗_; refl; sym; trans; cong; cong₂; subst; ¬[x≢x])
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Decidable.Core
  using (Dec; does; yes; _×?_; map′)
import Data.Nat.GeneralisedArithmetic as ℕ

private
  m+n+o≡n+[m+o] : ∀ m n o → m + n + o ≡ n + (m + o)
  m+n+o≡n+[m+o] m n o = trans (cong (_+ o) (+-comm m n)) (+-assoc n m o)

private
  variable
    a b c d p : Level
    A B C D : Set a
    w x y z : A
    m n o : ℕ
    ws xs ys zs : Vec A n

------------------------------------------------------------------------
-- Properties of toList

toList-injective : .(m≡n : m ≡ n) → (xs : Vec A m) (ys : Vec A n) →
                  toList xs ≡ toList ys → xs ≈[ m≡n ] ys
toList-injective m≡n [] [] xs=ys = refl
toList-injective m≡n (x ∷ xs) (y ∷ ys) xs=ys =
  cong₂ _∷_ (List.∷-injectiveˡ xs=ys) (toList-injective (cong pred m≡n) xs ys (List.∷-injectiveʳ xs=ys))

------------------------------------------------------------------------
-- Properties of propositional equality over vectors

∷-injectiveˡ : x ∷ xs ≡ y ∷ ys → x ≡ y
∷-injectiveˡ refl = refl

∷-injectiveʳ : x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-injectiveʳ refl = refl

∷-injective : x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

≡-dec : DecidableEquality A → DecidableEquality (Vec A n)
≡-dec _≟_ []       []       = yes refl
≡-dec _≟_ (x ∷ xs) (y ∷ ys) = map′ (uncurry (cong₂ _∷_))
  ∷-injective (x ≟ y ×? ≡-dec _≟_ xs ys)

------------------------------------------------------------------------
-- _[_]=_

[]=-injective : ∀ {i} → xs [ i ]= x → xs [ i ]= y → x ≡ y
[]=-injective here          here          = refl
[]=-injective (there xsᵢ≡x) (there xsᵢ≡y) = []=-injective xsᵢ≡x xsᵢ≡y

-- See also Data.Vec.Properties.WithK.[]=-irrelevant.

------------------------------------------------------------------------
-- take

unfold-take : ∀ n x (xs : Vec A (n + m)) → take (suc n) (x ∷ xs) ≡ x ∷ take n xs
unfold-take n x xs = refl

take-zipWith : ∀ (f : A → B → C) →
               (xs : Vec A (m + n)) (ys : Vec B (m + n)) →
               take m (zipWith f xs ys) ≡ zipWith f (take m xs) (take m ys)
take-zipWith {m = zero}  f xs       ys       = refl
take-zipWith {m = suc m} f (x ∷ xs) (y ∷ ys) = cong (f x y ∷_) (take-zipWith f xs ys)

take-map : ∀ (f : A → B) (m : ℕ) (xs : Vec A (m + n)) →
           take m (map f xs) ≡ map f (take m xs)
take-map f zero    xs       = refl
take-map f (suc m) (x ∷ xs) = cong (f x ∷_) (take-map f m xs)

updateAt-take : (xs : Vec A (m + n)) (i : Fin m) (f : A → A) →
                updateAt (take m xs) i f ≡ take m (updateAt xs (inject≤ i (m≤m+n m n)) f)
updateAt-take (_ ∷ _ ) zero    f = refl
updateAt-take (x ∷ xs) (suc i) f = cong (x ∷_) (updateAt-take xs i f)

------------------------------------------------------------------------
-- drop

unfold-drop : ∀ n x (xs : Vec A (n + m)) →
              drop (suc n) (x ∷ xs) ≡ drop n xs
unfold-drop n x xs = refl

drop-zipWith : (f : A → B → C) →
               (xs : Vec A (m + n)) (ys : Vec B (m + n)) →
               drop m (zipWith f xs ys) ≡ zipWith f (drop m xs) (drop m ys)
drop-zipWith {m = zero}  f   xs       ys     = refl
drop-zipWith {m = suc m} f (x ∷ xs) (y ∷ ys) = drop-zipWith f xs ys

drop-map : ∀ (f : A → B) (m : ℕ) (xs : Vec A (m + n)) →
           drop m (map f xs) ≡ map f (drop m xs)
drop-map f zero    xs       = refl
drop-map f (suc m) (x ∷ xs) = drop-map f m xs

------------------------------------------------------------------------
-- take and drop together

take++drop≡id : ∀ (m : ℕ) (xs : Vec A (m + n)) → take m xs ++ drop m xs ≡ xs
take++drop≡id zero    xs       = refl
take++drop≡id (suc m) (x ∷ xs) = cong (x ∷_) (take++drop≡id m xs)

------------------------------------------------------------------------
-- truncate

truncate-refl : (xs : Vec A n) → truncate ≤-refl xs ≡ xs
truncate-refl []       = refl
truncate-refl (x ∷ xs) = cong (x ∷_) (truncate-refl xs)

truncate-trans : ∀ .(m≤n : m ≤ n) .(n≤o : n ≤ o) (xs : Vec A o) →
                 truncate (≤-trans m≤n n≤o) xs ≡ truncate m≤n (truncate n≤o xs)
truncate-trans {m = zero}              _   _   _        = refl
truncate-trans {m = suc _} {n = suc _} m≤n n≤o (x ∷ xs) =
  cong (x ∷_) (truncate-trans (s≤s⁻¹ m≤n) (s≤s⁻¹ n≤o) xs)

truncate≡take : .(m≤n : m ≤ n) (xs : Vec A n) .(eq : n ≡ m + o) →
                truncate m≤n xs ≡ take m (cast eq xs)
truncate≡take {m = zero}  _   _        _  = refl
truncate≡take {m = suc _} m≤n (x ∷ xs) eq =
  cong (x ∷_) (truncate≡take (s≤s⁻¹ m≤n) xs (suc-injective eq))

take≡truncate : ∀ m (xs : Vec A (m + n)) →
                take m xs ≡ truncate (m≤m+n m n) xs
take≡truncate zero    _        = refl
take≡truncate (suc m) (x ∷ xs) = cong (x ∷_) (take≡truncate m xs)

truncate-zipWith : (f : A → B → C) .(m≤n : m ≤ n) (xs : Vec A n) (ys : Vec B n) →
  truncate m≤n (zipWith f xs ys) ≡ zipWith f (truncate m≤n xs) (truncate m≤n ys)
truncate-zipWith {m = zero}  f m≤n  _       _        = refl
truncate-zipWith {m = suc _} f m≤n (x ∷ xs) (y ∷ ys) =
  cong (f x y ∷_) (truncate-zipWith f (s≤s⁻¹ m≤n) xs ys)

truncate-zipWith-truncate : ∀ (f : A → B → C) .(m≤n : m ≤ n) .(n≤o : n ≤ o)
  (xs : Vec A o) (ys : Vec B n) →
  truncate m≤n (zipWith f (truncate n≤o xs) ys) ≡
  zipWith f (truncate (≤-trans m≤n n≤o) xs) (truncate m≤n ys)
truncate-zipWith-truncate f m≤n n≤o xs ys =
  trans (truncate-zipWith f m≤n (truncate n≤o xs) ys)
  (cong (λ zs → zipWith f zs (truncate m≤n ys)) ((sym (truncate-trans m≤n n≤o xs))))

truncate-updateAt : (m≤n : m ≤ n) (xs : Vec A n) (i : Fin m) (f : A → A) →
                    updateAt (truncate m≤n xs) i f ≡ truncate m≤n (updateAt xs (inject≤ i m≤n) f)
truncate-updateAt m≤n (_ ∷ _ ) zero f = refl
truncate-updateAt m≤n (x ∷ xs) (suc i) f = cong (x ∷_) (truncate-updateAt (s≤s⁻¹ m≤n) xs i f)

module _ (xs : Vec A (m + n)) (i : Fin m) (f : A → A) where
  private
    i′ = inject≤ i (m≤m+n m n)

  updateAt-truncate : updateAt (truncate (m≤m+n m n) xs) i f ≡ truncate (m≤m+n m n) (updateAt xs i′ f)
  updateAt-truncate = begin
    updateAt (truncate (m≤m+n m n) xs) i f ≡⟨ cong (λ l → updateAt l i f) (take≡truncate m xs) ⟨
    updateAt (take m xs) i f         ≡⟨ updateAt-take xs i f ⟩
    take m (updateAt xs i′ f)        ≡⟨ take≡truncate m (updateAt xs i′ f) ⟩
    truncate (m≤m+n m n) (updateAt xs i′ f) ∎
    where open ≡-Reasoning

------------------------------------------------------------------------
-- truncate and padRight together

truncate-padRight : .(m≤n : m ≤ n) (a : A) (xs : Vec A m) →
                    truncate m≤n (padRight m≤n a xs) ≡ xs
truncate-padRight             _   a []       = refl
truncate-padRight {n = suc _} m≤n a (x ∷ xs) =
  cong (x ∷_) (truncate-padRight (s≤s⁻¹ m≤n) a xs)

------------------------------------------------------------------------
-- lookup

[]=⇒lookup : ∀ {i} → xs [ i ]= x → lookup xs i ≡ x
[]=⇒lookup here            = refl
[]=⇒lookup (there xs[i]=x) = []=⇒lookup xs[i]=x

lookup⇒[]= : ∀ (i : Fin n) xs → lookup xs i ≡ x → xs [ i ]= x
lookup⇒[]= zero    (_ ∷ _)  refl = here
lookup⇒[]= (suc i) (_ ∷ xs) p    = there (lookup⇒[]= i xs p)

[]=↔lookup : ∀ {i} → xs [ i ]= x ↔ lookup xs i ≡ x
[]=↔lookup {xs = ys} {i = i} =
  mk↔ₛ′ []=⇒lookup (lookup⇒[]= i ys) ([]=⇒lookup∘lookup⇒[]= _ i) lookup⇒[]=∘[]=⇒lookup
  where
  lookup⇒[]=∘[]=⇒lookup : ∀ {i} (p : xs [ i ]= x) →
                          lookup⇒[]= i xs ([]=⇒lookup p) ≡ p
  lookup⇒[]=∘[]=⇒lookup here      = refl
  lookup⇒[]=∘[]=⇒lookup (there p) = cong there (lookup⇒[]=∘[]=⇒lookup p)

  []=⇒lookup∘lookup⇒[]= : ∀ xs (i : Fin n) (p : lookup xs i ≡ x) →
                          []=⇒lookup (lookup⇒[]= i xs p) ≡ p
  []=⇒lookup∘lookup⇒[]= (x ∷ xs) zero    refl = refl
  []=⇒lookup∘lookup⇒[]= (x ∷ xs) (suc i) p    = []=⇒lookup∘lookup⇒[]= xs i p

lookup-truncate : .(m≤n : m ≤ n) (xs : Vec A n) (i : Fin m) →
                  lookup (truncate m≤n xs) i ≡ lookup xs (Fin.inject≤ i m≤n)
lookup-truncate _   (_ ∷ _)  zero    = refl
lookup-truncate m≤n (_ ∷ xs) (suc i) = lookup-truncate (suc[m]≤n⇒m≤pred[n] m≤n) xs i

lookup-take-inject≤ : (xs : Vec A (m + n)) (i : Fin m) →
                      lookup (take m xs) i ≡ lookup xs (Fin.inject≤ i (m≤m+n m n))
lookup-take-inject≤ {m = m} {n = n} xs i = begin
  lookup (take _ xs) i
    ≡⟨ cong (λ ys → lookup ys i) (take≡truncate m xs) ⟩
  lookup (truncate _ xs) i
    ≡⟨ lookup-truncate (m≤m+n m n) xs i ⟩
  lookup xs (Fin.inject≤ i (m≤m+n m n))
    ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- updateAt (_[_]%=_)

-- (+) updateAt i actually updates the element at index i.

updateAt-updates : ∀ (i : Fin n) {f : A → A} (xs : Vec A n) →
                   xs [ i ]= x → (updateAt xs i f) [ i ]= f x
updateAt-updates zero    (x ∷ xs) here        = here
updateAt-updates (suc i) (x ∷ xs) (there loc) = there (updateAt-updates i xs loc)

-- (-) updateAt i does not touch the elements at other indices.

updateAt-minimal : ∀ (i j : Fin n) {f : A → A} (xs : Vec A n) →
                   i ≢ j → xs [ i ]= x → (updateAt xs j f) [ i ]= x
updateAt-minimal zero    zero    (x ∷ xs) 0≢0 here        = ¬[x≢x] 0≢0
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
                    updateAt xs i f ≡ xs
updateAt-id-local zero    (x ∷ xs) eq = cong (_∷ xs) eq
updateAt-id-local (suc i) (x ∷ xs) eq = cong (x ∷_) (updateAt-id-local i xs eq)

-- 1b. identity:  updateAt i id ≗ id

updateAt-id : ∀ (i : Fin n) (xs : Vec A n) → updateAt xs i id ≡ xs
updateAt-id i xs = updateAt-id-local i xs refl

-- 2a. local composition:  f ∘ g = h ↾ (lookup xs i)
--                implies  updateAt i f ∘ updateAt i g = updateAt i h ↾ xs

updateAt-updateAt-local : ∀ (i : Fin n) {f g h : A → A} (xs : Vec A n) →
                          f (g (lookup xs i)) ≡ h (lookup xs i) →
                          updateAt (updateAt xs i g) i f ≡ updateAt xs i h
updateAt-updateAt-local zero    (x ∷ xs) fg=h = cong (_∷ xs) fg=h
updateAt-updateAt-local (suc i) (x ∷ xs) fg=h = cong (x ∷_) (updateAt-updateAt-local i xs fg=h)

-- 2b. composition:  updateAt i f ∘ updateAt i g ≗ updateAt i (f ∘ g)

updateAt-updateAt : ∀ (i : Fin n) {f g : A → A} (xs : Vec A n) →
                    updateAt (updateAt xs i g) i f ≡ updateAt xs i (f ∘ g)
updateAt-updateAt i xs = updateAt-updateAt-local i xs refl

-- 3. congruence:  updateAt i  is a congruence wrt. extensional equality.

-- 3a.  If    f = g ↾ (lookup xs i)
--      then  updateAt i f = updateAt i g ↾ xs

updateAt-cong-local : ∀ (i : Fin n) {f g : A → A} (xs : Vec A n) →
                      f (lookup xs i) ≡ g (lookup xs i) →
                      updateAt xs i f ≡ updateAt xs i g
updateAt-cong-local zero    (x ∷ xs) f=g = cong (_∷ xs) f=g
updateAt-cong-local (suc i) (x ∷ xs) f=g = cong (x ∷_) (updateAt-cong-local i xs f=g)

-- 3b. congruence:  f ≗ g → updateAt i f ≗ updateAt i g

updateAt-cong : ∀ (i : Fin n) {f g : A → A} → f ≗ g → (xs : Vec A n) →
                updateAt xs i f ≡ updateAt xs i g
updateAt-cong i f≗g xs = updateAt-cong-local i xs (f≗g (lookup xs i))

-- The order of updates at different indices i ≢ j does not matter.

-- This a consequence of updateAt-updates and updateAt-minimal
-- but easier to prove inductively.

updateAt-commutes : ∀ (i j : Fin n) {f g : A → A} → i ≢ j → (xs : Vec A n) →
                    updateAt (updateAt xs j g) i f ≡ updateAt (updateAt xs i f) j g
updateAt-commutes zero    zero    0≢0 (x ∷ xs) = ¬[x≢x] 0≢0
updateAt-commutes zero    (suc j) i≢j (x ∷ xs) = refl
updateAt-commutes (suc i) zero    i≢j (x ∷ xs) = refl
updateAt-commutes (suc i) (suc j) i≢j (x ∷ xs) =
   cong (x ∷_) (updateAt-commutes i j (i≢j ∘ cong suc) xs)

-- lookup after updateAt reduces.

-- For same index this is an easy consequence of updateAt-updates
-- using []=↔lookup.

lookup∘updateAt : ∀ (i : Fin n) {f : A → A} xs →
                  lookup (updateAt xs i f) i ≡ f (lookup xs i)
lookup∘updateAt i xs =
  []=⇒lookup (updateAt-updates i xs (lookup⇒[]= i _ refl))

-- For different indices it easily follows from updateAt-minimal.

lookup∘updateAt′ : ∀ (i j : Fin n) {f : A → A} → i ≢ j → ∀ xs →
                   lookup (updateAt xs j f) i ≡ lookup xs i
lookup∘updateAt′ i j xs i≢j =
  []=⇒lookup (updateAt-minimal i j i≢j xs (lookup⇒[]= i _ refl))

-- Aliases for notation _[_]%=_

[]%=-id : ∀ (xs : Vec A n) (i : Fin n) → xs [ i ]%= id ≡ xs
[]%=-id xs i = updateAt-id i xs

[]%=-∘ : ∀ (xs : Vec A n) (i : Fin n) {f g : A → A} →
      xs [ i ]%= f
         [ i ]%= g
    ≡ xs [ i ]%= g ∘ f
[]%=-∘ xs i = updateAt-updateAt i xs


------------------------------------------------------------------------
-- _[_]≔_ (update)
--
-- _[_]≔_ is defined in terms of updateAt, and all of its properties
-- are special cases of the ones for updateAt.

[]≔-idempotent : ∀ (xs : Vec A n) (i : Fin n) →
                  (xs [ i ]≔ x) [ i ]≔ y ≡ xs [ i ]≔ y
[]≔-idempotent xs i = updateAt-updateAt i xs

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

open VecCast public
  using (cast-is-id; cast-trans)

subst-is-cast : (eq : m ≡ n) (xs : Vec A m) → subst (Vec A) eq xs ≡ cast eq xs
subst-is-cast refl xs = sym (cast-is-id refl xs)

cast-sym : .(eq : m ≡ n) {xs : Vec A m} {ys : Vec A n} →
           cast eq xs ≡ ys → cast (sym eq) ys ≡ xs
cast-sym eq {xs = []}     {ys = []}     _ = refl
cast-sym eq {xs = x ∷ xs} {ys = y ∷ ys} xxs[eq]≡yys =
  let x≡y , xs[eq]≡ys = ∷-injective xxs[eq]≡yys
  in cong₂ _∷_ (sym x≡y) (cast-sym (suc-injective eq) xs[eq]≡ys)

------------------------------------------------------------------------
-- map

map-id : map id ≗ id {A = Vec A n}
map-id []       = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

map-const : ∀ (xs : Vec A n) (y : B) → map (const y) xs ≡ replicate n y
map-const []       _ = refl
map-const (_ ∷ xs) y = cong (y ∷_) (map-const xs y)

map-cast : (f : A → B) .(eq : m ≡ n) (xs : Vec A m) →
           map f (cast eq xs) ≡ cast eq (map f xs)
map-cast f _ _ = sym (≈-cong′ (map f) refl)

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
               map f (updateAt xs i g) ≡ updateAt (map f xs) i h
map-updateAt (x ∷ xs) zero    eq = cong (_∷ _) eq
map-updateAt (x ∷ xs) (suc i) eq = cong (_ ∷_) (map-updateAt xs i eq)

map-insertAt : ∀ (f : A → B) (x : A) (xs : Vec A n) (i : Fin (suc n)) →
             map f (insertAt xs i x) ≡ insertAt (map f xs) i (f x)
map-insertAt f _ []        Fin.zero = refl
map-insertAt f _ (x' ∷ xs) Fin.zero = refl
map-insertAt f x (x' ∷ xs) (Fin.suc i) = cong (_ ∷_) (map-insertAt f x xs i)

map-removeAt : ∀ (f : A → B) (xs : Vec A (suc n)) (i : Fin (suc n)) →
               map f (removeAt xs i) ≡ removeAt (map f xs) i
map-removeAt f (x ∷ xs) zero = refl
map-removeAt f (x ∷ xs@(_ ∷ _)) (suc i) = cong (f x ∷_) (map-removeAt f xs i)

map-[]≔ : ∀ (f : A → B) (xs : Vec A n) (i : Fin n) →
          map f (xs [ i ]≔ x) ≡ map f xs [ i ]≔ f x
map-[]≔ f xs i = map-updateAt xs i refl

map-⊛ : ∀ (f : A → B → C) (g : A → B) (xs : Vec A n) →
        (map f xs ⊛ map g xs) ≡ map (f ˢ g) xs
map-⊛ f g []       = refl
map-⊛ f g (x ∷ xs) = cong (f x (g x) ∷_) (map-⊛ f g xs)

map-concat : (f : A → B) (xss : Vec (Vec A m) n) →
             map f (concat xss) ≡ concat (map (map f) xss)
map-concat f [] = refl
map-concat f (xs ∷ xss) = begin
  map f (concat (xs ∷ xss))
    ≡⟨⟩
  map f (xs ++ concat xss)
    ≡⟨ map-++ f xs (concat xss) ⟩
  map f xs ++ map f (concat xss)
    ≡⟨ cong (map f xs ++_) (map-concat f xss) ⟩
  map f xs ++ concat (map (map f) xss)
    ≡⟨⟩
  concat (map (map f) (xs ∷ xss))
    ∎ where open ≡-Reasoning

toList-map : ∀ (f : A → B) (xs : Vec A n) →
             toList (map f xs) ≡ List.map f (toList xs)
toList-map f [] = refl
toList-map f (x ∷ xs) = cong (f x List.∷_) (toList-map f xs)

map-truncate : (f : A → B) (m≤n : m ≤ n) (xs : Vec A n) →
  map f (truncate m≤n xs) ≡ truncate m≤n (map f xs)
map-truncate {m = m} {n = n} f m≤n xs =
  let _ , n≡m+o = m≤n⇒∃[o]m+o≡n m≤n
  in let m+o≡n = sym n≡m+o
  in begin
    map f (truncate m≤n xs)              ≡⟨ cong (map f) (truncate≡take m≤n xs m+o≡n) ⟩
    map f (take m (cast m+o≡n xs)) ≡⟨ take-map f m _ ⟨
    take m (map f (cast m+o≡n xs)) ≡⟨ cong (take m) (map-cast f m+o≡n xs) ⟩
    take m (cast m+o≡n (map f xs)) ≡⟨ truncate≡take m≤n (map f xs) m+o≡n ⟨
    truncate m≤n (map f xs)              ∎
  where open ≡-Reasoning

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

++-assoc-eqFree : ∀ (xs : Vec A m) (ys : Vec A n) (zs : Vec A o) → let eq = +-assoc m n o in
                  cast eq ((xs ++ ys) ++ zs) ≡ xs ++ (ys ++ zs)
++-assoc-eqFree []       ys zs = cast-is-id refl (ys ++ zs)
++-assoc-eqFree (x ∷ xs) ys zs = cong (x ∷_) (++-assoc-eqFree xs ys zs)

++-identityʳ-eqFree : ∀ (xs : Vec A n) → cast (+-identityʳ n) (xs ++ []) ≡ xs
++-identityʳ-eqFree []       = refl
++-identityʳ-eqFree (x ∷ xs) = cong (x ∷_) (++-identityʳ-eqFree xs)

cast-++ˡ : ∀ .(eq : m ≡ o) (xs : Vec A m) {ys : Vec A n} →
           cast (cong (_+ n) eq) (xs ++ ys) ≡ cast eq xs ++ ys
cast-++ˡ _ _ {ys} = ≈-cong′ (_++ ys) refl

cast-++ʳ : ∀ .(eq : n ≡ o) (xs : Vec A m) {ys : Vec A n} →
           cast (cong (m +_) eq) (xs ++ ys) ≡ xs ++ cast eq ys
cast-++ʳ _ xs = ≈-cong′ (xs ++_) refl

lookup-++-< : ∀ (xs : Vec A m) (ys : Vec A n) →
              ∀ i (i<m : toℕ i < m) →
              lookup (xs ++ ys) i  ≡ lookup xs (Fin.fromℕ< i<m)
lookup-++-< (x ∷ xs) ys zero    _     = refl
lookup-++-< (x ∷ xs) ys (suc i) si<sm = lookup-++-< xs ys i (s<s⁻¹ si<sm)

lookup-++-≥ : ∀ (xs : Vec A m) (ys : Vec A n) →
              ∀ i (i≥m : toℕ i ≥ m) →
              lookup (xs ++ ys) i ≡ lookup ys (Fin.reduce≥ i i≥m)
lookup-++-≥ []       ys i       _     = refl
lookup-++-≥ (x ∷ xs) ys (suc i) si≥sm = lookup-++-≥ xs ys i (s≤s⁻¹ si≥sm)

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

toList-++ : (xs : Vec A n) (ys : Vec A m) →
            toList (xs ++ ys) ≡ toList xs List.++ toList ys
toList-++ []       ys = refl
toList-++ (x ∷ xs) ys = cong (x List.∷_) (toList-++ xs ys)

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
                      LeftIdentity _≡_ (replicate n e) (zipWith f)
  zipWith-identityˡ idˡ []       = refl
  zipWith-identityˡ idˡ (x ∷ xs) =
    cong₂ _∷_ (idˡ x) (zipWith-identityˡ idˡ xs)

  zipWith-identityʳ : RightIdentity _≡_ e f →
                      RightIdentity _≡_ (replicate n e) (zipWith f)
  zipWith-identityʳ idʳ []       = refl
  zipWith-identityʳ idʳ (x ∷ xs) =
    cong₂ _∷_ (idʳ x) (zipWith-identityʳ idʳ xs)

  zipWith-zeroˡ : LeftZero _≡_ e f →
                  LeftZero _≡_ (replicate n e) (zipWith f)
  zipWith-zeroˡ zeˡ []       = refl
  zipWith-zeroˡ zeˡ (x ∷ xs) =
    cong₂ _∷_ (zeˡ x) (zipWith-zeroˡ zeˡ xs)

  zipWith-zeroʳ : RightZero _≡_ e f →
                  RightZero _≡_ (replicate n e) (zipWith f)
  zipWith-zeroʳ zeʳ []       = refl
  zipWith-zeroʳ zeʳ (x ∷ xs) =
    cong₂ _∷_ (zeʳ x) (zipWith-zeroʳ zeʳ xs)

module _ {f : A → A → A} {e : A} {⁻¹ : A → A} where

  zipWith-inverseˡ : LeftInverse _≡_ e ⁻¹ f →
                     LeftInverse _≡_ (replicate n e) (map ⁻¹) (zipWith f)
  zipWith-inverseˡ invˡ []       = refl
  zipWith-inverseˡ invˡ (x ∷ xs) =
    cong₂ _∷_ (invˡ x) (zipWith-inverseˡ invˡ xs)

  zipWith-inverseʳ : RightInverse _≡_ e ⁻¹ f →
                     RightInverse _≡_ (replicate n e) (map ⁻¹) (zipWith f)
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

zipWith-++ : ∀ (f : A → B → C)
             (xs : Vec A n) (ys : Vec A m)
             (xs' : Vec B n) (ys' : Vec B m) →
             zipWith f (xs ++ ys) (xs' ++ ys') ≡
             zipWith f xs xs' ++ zipWith f ys ys'
zipWith-++ f []       ys []         ys' = refl
zipWith-++ f (x ∷ xs) ys (x' ∷ xs') ys' =
  cong (_ ∷_) (zipWith-++ f xs ys xs' ys')

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
          map (Product.map f g) (zip xs ys) ≡ zip (map f xs) (map g ys)
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
            in (map f xs , map g ys) ≡ unzip (map (Product.map f g) xys)
map-unzip f g []              = refl
map-unzip f g ((x , y) ∷ xys) =
  cong (Product.map (f x ∷_) (g y ∷_)) (map-unzip f g xys)

-- Products of vectors are isomorphic to vectors of products.

unzip∘zip : ∀ (xs : Vec A n) (ys : Vec B n) →
            unzip (zip xs ys) ≡ (xs , ys)
unzip∘zip [] []             = refl
unzip∘zip (x ∷ xs) (y ∷ ys) =
  cong (Product.map (x ∷_) (y ∷_)) (unzip∘zip xs ys)

zip∘unzip : ∀ (xys : Vec (A × B) n) → uncurry zip (unzip xys) ≡ xys
zip∘unzip []         = refl
zip∘unzip (xy ∷ xys) = cong (xy ∷_) (zip∘unzip xys)

×v↔v× : (Vec A n × Vec B n) ↔ Vec (A × B) n
×v↔v× = mk↔ₛ′ (uncurry zip) unzip zip∘unzip (uncurry unzip∘zip)

------------------------------------------------------------------------
-- _⊛_

lookup-⊛ : ∀ i (fs : Vec (A → B) n) (xs : Vec A n) →
           lookup (fs ⊛ xs) i ≡ (lookup fs i $ lookup xs i)
lookup-⊛ zero    (f ∷ fs) (x ∷ xs) = refl
lookup-⊛ (suc i) (f ∷ fs) (x ∷ xs) = lookup-⊛ i fs xs

map-is-⊛ : ∀ (f : A → B) (xs : Vec A n) →
           map f xs ≡ (replicate n f ⊛ xs)
map-is-⊛ f []       = refl
map-is-⊛ f (x ∷ xs) = cong (_ ∷_) (map-is-⊛ f xs)

⊛-is-zipWith : ∀ (fs : Vec (A → B) n) (xs : Vec A n) →
               (fs ⊛ xs) ≡ zipWith _$_ fs xs
⊛-is-zipWith []       []       = refl
⊛-is-zipWith (f ∷ fs) (x ∷ xs) = cong (f x ∷_) (⊛-is-zipWith fs xs)

zipWith-is-⊛ : ∀ (f : A → B → C) (xs : Vec A n) (ys : Vec B n) →
               zipWith f xs ys ≡ (replicate n f ⊛ xs ⊛ ys)
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
  where open ≡-Reasoning

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
  where open ≡-Reasoning

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
    open ≡-Reasoning
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
    where open ≡-Reasoning

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

-- snoc is snoc

unfold-∷ʳ-eqFree : ∀ x (xs : Vec A n) → cast (+-comm 1 n) (xs ∷ʳ x) ≡ xs ++ [ x ]
unfold-∷ʳ-eqFree x []       = refl
unfold-∷ʳ-eqFree x (y ∷ xs) = cong (y ∷_) (unfold-∷ʳ-eqFree x xs)

∷ʳ-injective : ∀ (xs ys : Vec A n) → xs ∷ʳ x ≡ ys ∷ʳ y → xs ≡ ys × x ≡ y
∷ʳ-injective []       []        refl = (refl , refl)
∷ʳ-injective (x ∷ xs) (y  ∷ ys) eq   with ∷-injective eq
... | refl , eq′ = Product.map₁ (cong (x ∷_)) (∷ʳ-injective xs ys eq′)

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

-- init, last and _∷ʳ_

init-∷ʳ : ∀ x (xs : Vec A n) → init (xs ∷ʳ x) ≡ xs
init-∷ʳ x []       = refl
init-∷ʳ x (y ∷ xs) = cong (y ∷_) (init-∷ʳ x xs)

last-∷ʳ : ∀ x (xs : Vec A n) → last (xs ∷ʳ x) ≡ x
last-∷ʳ x []       = refl
last-∷ʳ x (y ∷ xs) = last-∷ʳ x xs

-- map and _∷ʳ_

map-∷ʳ : ∀ (f : A → B) x (xs : Vec A n) → map f (xs ∷ʳ x) ≡ map f xs ∷ʳ f x
map-∷ʳ f x []       = refl
map-∷ʳ f x (y ∷ xs) = cong (f y ∷_) (map-∷ʳ f x xs)

-- cast and _∷ʳ_

cast-∷ʳ : ∀ .(eq : suc n ≡ suc m) x (xs : Vec A n) →
          cast eq (xs ∷ʳ x) ≡ (cast (cong pred eq) xs) ∷ʳ x
cast-∷ʳ _ x _ = ≈-cong′ (_∷ʳ x) refl

-- _++_ and _∷ʳ_

++-∷ʳ-eqFree : ∀ z (xs : Vec A m) (ys : Vec A n) → let eq = sym (+-suc m n) in
               cast eq ((xs ++ ys) ∷ʳ z) ≡ xs ++ (ys ∷ʳ z)
++-∷ʳ-eqFree {m = zero}  z []       []       = refl
++-∷ʳ-eqFree {m = zero}  z []       (y ∷ ys) = cong (y ∷_) (++-∷ʳ-eqFree z [] ys)
++-∷ʳ-eqFree {m = suc m} z (x ∷ xs) ys       = cong (x ∷_) (++-∷ʳ-eqFree z xs ys)

∷ʳ-++-eqFree : ∀ a (xs : Vec A n) {ys : Vec A m} → let eq = sym (+-suc n m) in
               cast eq ((xs ∷ʳ a) ++ ys) ≡ xs ++ (a ∷ ys)
∷ʳ-++-eqFree a []       {ys} = cong (a ∷_) (cast-is-id refl ys)
∷ʳ-++-eqFree a (x ∷ xs) {ys} = cong (x ∷_) (∷ʳ-++-eqFree a xs)

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
  where open ≡-Reasoning

-- foldr after a reverse is a foldl

foldr-reverse : ∀ (B : ℕ → Set b) (f : FoldrOp A B) {e} →
                foldr {n = n} B f e ∘ reverse ≗ foldl B (flip f) e
foldr-reverse B f {e} xs = foldl-fusion (foldr B f e) refl (λ _ _ → refl) xs

-- reverse is involutive.

reverse-involutive : Involutive {A = Vec A n} _≡_ reverse
reverse-involutive xs = begin
  reverse (reverse xs)    ≡⟨  foldl-reverse (Vec _) (flip _∷_) xs ⟩
  foldr (Vec _) _∷_ [] xs ≡⟨ id-is-foldr xs ⟨
  xs                      ∎
  where open ≡-Reasoning

reverse-reverse : reverse xs ≡ ys → reverse ys ≡ xs
reverse-reverse {xs = xs} {ys} eq =  begin
  reverse ys           ≡⟨ cong reverse eq ⟨
  reverse (reverse xs) ≡⟨  reverse-involutive xs ⟩
  xs                   ∎
  where open ≡-Reasoning

-- reverse is injective.

reverse-injective : reverse xs ≡ reverse ys → xs ≡ ys
reverse-injective {xs = xs} {ys} eq = begin
  xs                   ≡⟨ reverse-reverse eq ⟨
  reverse (reverse ys) ≡⟨  reverse-involutive ys ⟩
  ys                   ∎
  where open ≡-Reasoning

-- init and last of reverse

init-reverse : init ∘ reverse ≗ reverse ∘ tail {A = A} {n = n}
init-reverse (x ∷ xs) = begin
  init (reverse (x ∷ xs))   ≡⟨ cong init (reverse-∷ x xs) ⟩
  init (reverse xs ∷ʳ x)    ≡⟨ init-∷ʳ x (reverse xs) ⟩
  reverse xs                ∎
  where open ≡-Reasoning

last-reverse : last ∘ reverse ≗ head {A = A} {n = n}
last-reverse (x ∷ xs) = begin
  last (reverse (x ∷ xs))   ≡⟨ cong last (reverse-∷ x xs) ⟩
  last (reverse xs ∷ʳ x)    ≡⟨ last-∷ʳ x (reverse xs) ⟩
  x                         ∎
  where open ≡-Reasoning

-- map and reverse

map-reverse : ∀ (f : A → B) (xs : Vec A n) →
              map f (reverse xs) ≡ reverse (map f xs)
map-reverse f []       = refl
map-reverse f (x ∷ xs) = begin
  map f (reverse (x ∷ xs))  ≡⟨ cong (map f) (reverse-∷ x xs) ⟩
  map f (reverse xs ∷ʳ x)   ≡⟨ map-∷ʳ f x (reverse xs) ⟩
  map f (reverse xs) ∷ʳ f x ≡⟨ cong (_∷ʳ f x) (map-reverse f xs ) ⟩
  reverse (map f xs) ∷ʳ f x ≡⟨ reverse-∷ (f x) (map f xs) ⟨
  reverse (f x ∷ map f xs)  ≡⟨⟩
  reverse (map f (x ∷ xs))  ∎
  where open ≡-Reasoning

-- append and reverse
toList-∷ʳ : ∀ x (xs : Vec A n) → toList (xs ∷ʳ x) ≡ toList xs List.++ List.[ x ]
toList-∷ʳ x []       = refl
toList-∷ʳ x (y ∷ xs) = cong (y List.∷_) (toList-∷ʳ x xs)

toList-reverse : ∀ (xs : Vec A n) → toList (reverse xs) ≡ List.reverse (toList xs)
toList-reverse [] = refl
toList-reverse (x ∷ xs) = begin
  toList (reverse (x ∷ xs))                   ≡⟨ cong toList (reverse-∷ x xs) ⟩
  toList (reverse xs ∷ʳ x)                    ≡⟨ toList-∷ʳ x (reverse xs) ⟩
  toList (reverse xs) List.++ List.[ x ]      ≡⟨ cong (List._++ List.[ x ]) (toList-reverse xs) ⟩
  List.reverse (toList xs) List.++ List.[ x ] ≡⟨ List.unfold-reverse x (toList xs) ⟨
  List.reverse (toList (x ∷ xs))              ∎
  where open ≡-Reasoning

reverse-++-eqFree : ∀ (xs : Vec A m) (ys : Vec A n)
                  → reverse (xs ++ ys) ≈[ +-comm m n ] reverse ys ++ reverse xs
reverse-++-eqFree {m = m} {n = n} xs ys =
  toList-injective (+-comm m n) (reverse (xs ++ ys)) (reverse ys ++ reverse xs) $
  begin
    toList (reverse (xs ++ ys))                               ≡⟨ toList-reverse ((xs ++ ys)) ⟩
    List.reverse (toList (xs ++ ys))                          ≡⟨ cong List.reverse (toList-++ xs ys) ⟩
    List.reverse (toList xs List.++ toList ys)                ≡⟨ List.reverse-++ (toList xs) (toList ys) ⟩
    List.reverse (toList ys) List.++ List.reverse (toList xs) ≡⟨ cong₂ List._++_ (toList-reverse ys) (toList-reverse xs) ⟨
    toList (reverse ys) List.++ toList (reverse xs)           ≡⟨ toList-++ (reverse ys) (reverse xs) ⟨
    toList (reverse ys ++ reverse xs)                         ∎
  where open ≡-Reasoning

cast-reverse : ∀ .(eq : m ≡ n) → cast eq ∘ reverse {A = A} {n = m} ≗ reverse ∘ cast eq
cast-reverse _ _ = ≈-cong′ reverse refl

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
  map f (xs ʳ++ ys)              ≡⟨ cong (map f) (unfold-ʳ++ xs ys) ⟩
  map f (reverse xs ++ ys)       ≡⟨ map-++ f (reverse xs) ys ⟩
  map f (reverse xs) ++ map f ys ≡⟨ cong (_++ map f ys) (map-reverse f xs) ⟩
  reverse (map f xs) ++ map f ys ≡⟨ unfold-ʳ++ (map f xs) (map f ys) ⟨
  map f xs ʳ++ map f ys          ∎
  where open ≡-Reasoning

toList-ʳ++ : ∀ (xs : Vec A m) {ys : Vec A n} →
            toList (xs ʳ++ ys) ≡ (toList xs) List.ʳ++ toList ys
toList-ʳ++ xs {ys} = begin
  toList (xs ʳ++ ys)                          ≡⟨ cong toList (unfold-ʳ++ xs ys) ⟩
  toList (reverse xs ++ ys)                   ≡⟨ toList-++ ((reverse xs )) ys ⟩
  toList (reverse xs) List.++ toList ys       ≡⟨ cong (List._++ toList ys) (toList-reverse xs) ⟩
  List.reverse (toList xs) List.++ toList ys  ≡⟨ List.ʳ++-defn (toList xs) ⟨
  toList xs List.ʳ++ toList ys                ∎
  where open ≡-Reasoning


++-ʳ++-eqFree : ∀ (xs : Vec A m) {ys : Vec A n} {zs : Vec A o} → let eq = m+n+o≡n+[m+o] m n o in
                cast eq ((xs ++ ys) ʳ++ zs) ≡ ys ʳ++ (xs ʳ++ zs)
++-ʳ++-eqFree {m = m} {n} {o} xs {ys} {zs} =
  toList-injective (m+n+o≡n+[m+o] m n o) ((xs ++ ys) ʳ++ zs) (ys ʳ++ (xs ʳ++ zs)) $
  begin
    toList ((xs ++ ys) ʳ++ zs)                          ≡⟨ toList-ʳ++ (xs ++ ys) ⟩
    toList (xs ++ ys) List.ʳ++ toList zs                ≡⟨ cong (List._ʳ++ toList zs) (toList-++ xs ys)  ⟩
    ((toList xs) List.++ toList ys ) List.ʳ++ toList zs ≡⟨ List.++-ʳ++ (toList xs) ⟩
    toList ys List.ʳ++ (toList xs List.ʳ++ toList zs)   ≡⟨ cong (toList ys List.ʳ++_) (toList-ʳ++ xs) ⟨
    toList ys List.ʳ++ toList (xs ʳ++ zs)               ≡⟨ toList-ʳ++ ys ⟨
    toList (ys ʳ++ (xs ʳ++ zs))                         ∎
    where open ≡-Reasoning

ʳ++-ʳ++-eqFree : ∀ (xs : Vec A m) {ys : Vec A n} {zs : Vec A o} → let eq = m+n+o≡n+[m+o] m n o in
                 cast eq ((xs ʳ++ ys) ʳ++ zs) ≡ ys ʳ++ (xs ++ zs)
ʳ++-ʳ++-eqFree {m = m} {n} {o} xs {ys} {zs} =
  toList-injective (m+n+o≡n+[m+o] m n o) ((xs ʳ++ ys) ʳ++ zs) (ys ʳ++ (xs ++ zs)) $
  begin
    toList ((xs ʳ++ ys) ʳ++ zs)                       ≡⟨ toList-ʳ++ (xs ʳ++ ys) ⟩
    toList (xs ʳ++ ys) List.ʳ++ toList zs             ≡⟨ cong (List._ʳ++ toList zs) (toList-ʳ++ xs) ⟩
    (toList xs List.ʳ++ toList ys) List.ʳ++ toList zs ≡⟨ List.ʳ++-ʳ++ (toList xs) ⟩
    toList ys List.ʳ++ (toList xs List.++ toList zs)  ≡⟨ cong (toList ys List.ʳ++_) (toList-++ xs zs) ⟨
    toList ys List.ʳ++ (toList (xs ++ zs))            ≡⟨ toList-ʳ++ ys ⟨
    toList (ys ʳ++ (xs ++ zs))                        ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
--sum

sum-++ : ∀ (xs : Vec ℕ m) → sum (xs ++ ys) ≡ sum xs + sum ys
sum-++ {_}       []       = refl
sum-++ {ys = ys} (x ∷ xs) = begin
  x + sum (xs ++ ys)     ≡⟨ cong (x +_) (sum-++ xs) ⟩
  x + (sum xs + sum ys)  ≡⟨ +-assoc x (sum xs) (sum ys) ⟨
  sum (x ∷ xs) + sum ys  ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- replicate

cast-replicate : ∀ .(m≡n : m ≡ n) (x : A) → cast m≡n (replicate m x) ≡ replicate n x
cast-replicate {m = zero}  {n = zero}  _  _ = refl
cast-replicate {m = suc _} {n = suc _} eq x = cong (x ∷_) (cast-replicate (suc-injective eq) x)

lookup-replicate : ∀ (i : Fin n) (x : A) → lookup (replicate n x) i ≡ x
lookup-replicate zero    x = refl
lookup-replicate (suc i) x = lookup-replicate i x

map-replicate :  ∀ (f : A → B) (x : A) n →
                 map f (replicate n x) ≡ replicate n (f x)
map-replicate f x zero = refl
map-replicate f x (suc n) = cong (f x ∷_) (map-replicate f x n)

transpose-replicate : ∀ (xs : Vec A m) →
                      transpose (replicate n xs) ≡ map (replicate n) xs
transpose-replicate {n = zero}  _  = sym (map-const _ [])
transpose-replicate {n = suc n} xs = begin
  transpose (replicate (suc n) xs)                    ≡⟨⟩
  (replicate _ _∷_ ⊛ xs ⊛ transpose (replicate _ xs)) ≡⟨ cong₂ _⊛_ (sym (map-is-⊛ _∷_ xs)) (transpose-replicate xs) ⟩
  (map _∷_ xs ⊛ map (replicate n) xs)                 ≡⟨ map-⊛ _∷_ (replicate n) xs ⟩
  map (replicate (suc n)) xs                          ∎
  where open ≡-Reasoning

zipWith-replicate : ∀ (_⊕_ : A → B → C) (x : A) (y : B) →
                    zipWith _⊕_ (replicate n x) (replicate n y) ≡ replicate n (x ⊕ y)
zipWith-replicate {n = zero}  _⊕_ x y = refl
zipWith-replicate {n = suc n} _⊕_ x y = cong (x ⊕ y ∷_) (zipWith-replicate _⊕_ x y)

zipWith-replicate₁ : ∀ (_⊕_ : A → B → C) (x : A) (ys : Vec B n) →
                     zipWith _⊕_ (replicate n x) ys ≡ map (x ⊕_) ys
zipWith-replicate₁ _⊕_ x []       = refl
zipWith-replicate₁ _⊕_ x (y ∷ ys) =
  cong (x ⊕ y ∷_) (zipWith-replicate₁ _⊕_ x ys)

zipWith-replicate₂ : ∀ (_⊕_ : A → B → C) (xs : Vec A n) (y : B) →
                     zipWith _⊕_ xs (replicate n y) ≡ map (_⊕ y) xs
zipWith-replicate₂ _⊕_ []       y = refl
zipWith-replicate₂ _⊕_ (x ∷ xs) y =
  cong (x ⊕ y ∷_) (zipWith-replicate₂ _⊕_ xs y)

toList-replicate : ∀ (n : ℕ) (x : A) →
                   toList (replicate n x) ≡ List.replicate n x
toList-replicate zero    x = refl
toList-replicate (suc n) x = cong (_ List.∷_) (toList-replicate n x)

------------------------------------------------------------------------
-- pad

padRight-refl : (a : A) (xs : Vec A n) → padRight ≤-refl a xs ≡ xs
padRight-refl a []       = refl
padRight-refl a (x ∷ xs) = cong (x ∷_) (padRight-refl a xs)

padRight-replicate : ∀ .(m≤n : m ≤ n) (a : A) →
                     replicate n a ≡ padRight m≤n a (replicate m a)
padRight-replicate {m = zero}              _   a = refl
padRight-replicate {m = suc _} {n = suc _} m≤n a =
  cong (a ∷_) (padRight-replicate (s≤s⁻¹ m≤n) a)

padRight-trans : ∀ .(m≤n : m ≤ n) .(n≤o : n ≤ o) (a : A) (xs : Vec A m) →
            padRight (≤-trans m≤n n≤o) a xs ≡ padRight n≤o a (padRight m≤n a xs)
padRight-trans                         _   n≤o a []       = padRight-replicate n≤o a
padRight-trans {n = suc _} {o = suc _} m≤n n≤o a (x ∷ xs) =
  cong (x ∷_) (padRight-trans (s≤s⁻¹ m≤n) (s≤s⁻¹ n≤o) a xs)

padRight-lookup : ∀ .(m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin m) →
                  lookup (padRight m≤n a xs) (inject≤ i m≤n) ≡ lookup xs i
padRight-lookup {n = suc _} _   a (x ∷ xs) zero    = refl
padRight-lookup {n = suc _} m≤n a (x ∷ xs) (suc i) = padRight-lookup (s≤s⁻¹ m≤n) a xs i

padRight-map : ∀ (f : A → B) .(m≤n : m ≤ n) (a : A) (xs : Vec A m) →
               map f (padRight m≤n a xs) ≡ padRight m≤n (f a) (map f xs)
padRight-map             f _   a [] = map-replicate f a _
padRight-map {n = suc _} f m≤n a (x ∷ xs) = cong (f x ∷_) (padRight-map f (s≤s⁻¹ m≤n) a xs)

padRight-zipWith : ∀ (f : A → B → C) .(m≤n : m ≤ n) (a : A) (b : B)
                   (xs : Vec A m) (ys : Vec B m) →
                   zipWith f (padRight m≤n a xs) (padRight m≤n b ys) ≡ padRight m≤n (f a b) (zipWith f xs ys)
padRight-zipWith             f _   a b []       []       = zipWith-replicate f a b
padRight-zipWith {n = suc _} f m≤n a b (x ∷ xs) (y ∷ ys) =
  cong (f x y ∷_) (padRight-zipWith f (s≤s⁻¹ m≤n) a b xs ys)

padRight-zipWith₁ : ∀ (f : A → B → C) .(m≤n : m ≤ n) .(n≤o : n ≤ o)
                    (a : A) (b : B) (xs : Vec A n) (ys : Vec B m) →
                    zipWith f (padRight n≤o a xs) (padRight (≤-trans m≤n n≤o) b ys) ≡
                    padRight n≤o (f a b) (zipWith f xs (padRight m≤n b ys))
padRight-zipWith₁ f m≤n n≤o a b xs ys =
  trans (cong (zipWith f (padRight n≤o a xs)) (padRight-trans m≤n n≤o b ys))
        (padRight-zipWith f n≤o a b xs (padRight m≤n b ys))

padRight-drop : ∀ .(m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) →
                drop m (cast n≡m+o (padRight m≤n a xs)) ≡ replicate o a
padRight-drop {m = zero}              _   a []       eq = cast-replicate eq a
padRight-drop {m = suc _} {n = suc _} m≤n a (x ∷ xs) eq = padRight-drop (s≤s⁻¹ m≤n) a xs (suc-injective eq)

padRight-drop′ : ∀ .(m≤n : m ≤ n) (a : A) (xs : Vec A m) →
                 let o , n≡m+o = m≤n⇒∃[o]m+o≡n m≤n
                 in drop m (cast (sym n≡m+o) (padRight m≤n a xs)) ≡ replicate o a
padRight-drop′ m≤n a xs = let o , n≡m+o = m≤n⇒∃[o]m+o≡n m≤n
  in padRight-drop m≤n a xs (sym n≡m+o)

padRight-take : ∀ .(m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) →
                take m (cast n≡m+o (padRight m≤n a xs)) ≡ xs
padRight-take {m = zero}              _   a []       _  = refl
padRight-take {m = suc _} {n = suc _} m≤n a (x ∷ xs) eq = cong (x ∷_) (padRight-take (s≤s⁻¹ m≤n) a xs (suc-injective eq))

padRight-take′ : ∀ .(m≤n : m ≤ n) (a : A) (xs : Vec A m) →
                 let _ , n≡m+o = m≤n⇒∃[o]m+o≡n m≤n
                 in take m (cast (sym n≡m+o) (padRight m≤n a xs)) ≡ xs
padRight-take′ m≤n a xs = let _ , n≡m+o = m≤n⇒∃[o]m+o≡n m≤n
  in padRight-take m≤n a xs (sym n≡m+o)

padRight-updateAt : ∀ .(m≤n : m ≤ n) (xs : Vec A m) (f : A → A) (i : Fin m) (x : A) →
                    updateAt (padRight m≤n x xs) (inject≤ i m≤n) f ≡
                    padRight m≤n x (updateAt xs i f)
padRight-updateAt {n = suc _} m≤n (y ∷ xs) f zero    x = refl
padRight-updateAt {n = suc _} m≤n (y ∷ xs) f (suc i) x = cong (y ∷_) (padRight-updateAt (s≤s⁻¹ m≤n) xs f i x)

--
------------------------------------------------------------------------
-- iterate

iterate-id : ∀ (x : A) n → iterate id x n ≡ replicate n x
iterate-id x zero    = refl
iterate-id x (suc n) = cong (_ ∷_) (iterate-id (id x) n)
take-iterate : ∀ n f (x : A) → take n (iterate f x (n + m)) ≡ iterate f x n
take-iterate zero    f x = refl
take-iterate (suc n) f x = cong (_ ∷_) (take-iterate n f (f x))

drop-iterate : ∀ n f (x : A) → drop n (iterate f x (n + zero)) ≡ []
drop-iterate zero    f x = refl
drop-iterate (suc n) f x = drop-iterate n f (f x)

lookup-iterate :  ∀ f (x : A) (i : Fin n) → lookup (iterate f x n) i ≡ ℕ.iterate f x (toℕ i)
lookup-iterate f x zero    = refl
lookup-iterate f x (suc i) = lookup-iterate f (f x) i

toList-iterate : ∀ f (x : A) n → toList (iterate f x n) ≡ List.iterate f x n
toList-iterate f x zero    = refl
toList-iterate f x (suc n) = cong (_ List.∷_) (toList-iterate f (f x) n)

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
  map (lookup xs) (allFin n) ≡⟨ tabulate-∘ (lookup xs) id ⟨
  tabulate (lookup xs)       ≡⟨ tabulate∘lookup xs ⟩
  xs                         ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- count

module _ {P : Pred A p} (P? : Decidable P) where

  count≤n : ∀ (xs : Vec A n) → count P? xs ≤ n
  count≤n []       = z≤n
  count≤n (x ∷ xs) with does (P? x)
  ... | true  = s≤s (count≤n xs)
  ... | false = m≤n⇒m≤1+n (count≤n xs)

------------------------------------------------------------------------
-- length

length-toList : (xs : Vec A n) → List.length (toList xs) ≡ length xs
length-toList []       = refl
length-toList (x ∷ xs) = cong suc (length-toList xs)

------------------------------------------------------------------------
-- insertAt

insertAt-lookup : ∀ (xs : Vec A n) (i : Fin (suc n)) (v : A) →
                  lookup (insertAt xs i v) i ≡ v
insertAt-lookup xs       zero     v = refl
insertAt-lookup (x ∷ xs) (suc i)  v = insertAt-lookup xs i v

insertAt-punchIn : ∀ (xs : Vec A n) (i : Fin (suc n)) (v : A) (j : Fin n) →
                   lookup (insertAt xs i v) (Fin.punchIn i j) ≡ lookup xs j
insertAt-punchIn xs       zero     v j       = refl
insertAt-punchIn (x ∷ xs) (suc i)  v zero    = refl
insertAt-punchIn (x ∷ xs) (suc i)  v (suc j) = insertAt-punchIn xs i v j

toList-insertAt : ∀ (xs : Vec A n) (i : Fin (suc n)) (v : A) →
                  toList (insertAt xs i v) ≡ List.insertAt (toList xs) (Fin.cast (cong suc (sym (length-toList xs))) i) v
toList-insertAt xs       zero    v = refl
toList-insertAt (x ∷ xs) (suc i) v = cong (_ List.∷_) (toList-insertAt xs i v)

------------------------------------------------------------------------
-- removeAt

removeAt-punchOut : ∀ (xs : Vec A (suc n)) {i} {j} (i≢j : i ≢ j) →
                  lookup (removeAt xs i) (Fin.punchOut i≢j) ≡ lookup xs j
removeAt-punchOut (x ∷ xs)     {zero}  {zero}  i≢j = ¬[x≢x] i≢j
removeAt-punchOut (x ∷ xs)     {zero}  {suc j} i≢j = refl
removeAt-punchOut (x ∷ y ∷ xs) {suc i} {zero}  i≢j = refl
removeAt-punchOut (x ∷ y ∷ xs) {suc i} {suc j} i≢j =
  removeAt-punchOut (y ∷ xs) (i≢j ∘ cong suc)

------------------------------------------------------------------------
-- insertAt and removeAt

removeAt-insertAt : ∀ (xs : Vec A n) (i : Fin (suc n)) (v : A) →
                    removeAt (insertAt xs i v) i ≡ xs
removeAt-insertAt xs               zero           v = refl
removeAt-insertAt (x ∷ xs)         (suc zero)     v = refl
removeAt-insertAt (x ∷ xs@(_ ∷ _)) (suc (suc i))  v =
  cong (x ∷_) (removeAt-insertAt xs (suc i) v)

insertAt-removeAt : ∀ (xs : Vec A (suc n)) (i : Fin (suc n)) →
                    insertAt (removeAt xs i) i (lookup xs i) ≡ xs
insertAt-removeAt (x ∷ xs)         zero     = refl
insertAt-removeAt (x ∷ xs@(_ ∷ _)) (suc i)  =
  cong (x ∷_) (insertAt-removeAt xs i)

------------------------------------------------------------------------
-- Conversion function

toList∘fromList : (xs : List A) → toList (fromList xs) ≡ xs
toList∘fromList List.[]       = refl
toList∘fromList (x List.∷ xs) = cong (x List.∷_) (toList∘fromList xs)

fromList∘toList : ∀  (xs : Vec A n) → fromList (toList xs) ≈[ length-toList xs ] xs
fromList∘toList [] = refl
fromList∘toList (x ∷ xs) = cong (x ∷_) (fromList∘toList xs)

toList-cast : ∀ .(eq : m ≡ n) (xs : Vec A m) → toList (cast eq xs) ≡ toList xs
toList-cast {n = zero}  eq []       = refl
toList-cast {n = suc _} eq (x ∷ xs) =
  cong (x List.∷_) (toList-cast (cong pred eq) xs)

cast-fromList : ∀ {xs ys : List A} (eq : xs ≡ ys) →
                cast (cong List.length eq) (fromList xs) ≡ fromList ys
cast-fromList {xs = List.[]}     {ys = List.[]}     eq = refl
cast-fromList {xs = x List.∷ xs} {ys = y List.∷ ys} eq =
  let x≡y , xs≡ys = List.∷-injective eq in begin
  x ∷ cast (cong (pred ∘ List.length) eq) (fromList xs) ≡⟨ cong (_ ∷_) (cast-fromList xs≡ys) ⟩
  x ∷ fromList ys                                       ≡⟨ cong (_∷ _) x≡y ⟩
  y ∷ fromList ys                                       ∎
  where open ≡-Reasoning

fromList-map : ∀ (f : A → B) (xs : List A) →
               cast (List.length-map f xs) (fromList (List.map f xs)) ≡ map f (fromList xs)
fromList-map f List.[]       = refl
fromList-map f (x List.∷ xs) = cong (f x ∷_) (fromList-map f xs)

fromList-++ : ∀ (xs : List A) {ys : List A} →
              cast (List.length-++ xs) (fromList (xs List.++ ys)) ≡ fromList xs ++ fromList ys
fromList-++ List.[]       {ys} = cast-is-id refl (fromList ys)
fromList-++ (x List.∷ xs) {ys} = cong (x ∷_) (fromList-++ xs)

fromList-reverse : (xs : List A) →
                  (fromList (List.reverse xs)) ≈[ List.length-reverse xs ] reverse (fromList xs)
fromList-reverse xs =
  toList-injective (List.length-reverse xs) (fromList (List.reverse xs)) (reverse (fromList xs)) $
  begin
    toList (fromList (List.reverse xs)) ≡⟨ toList∘fromList (List.reverse xs) ⟩
    List.reverse xs                     ≡⟨ cong (λ x → List.reverse x) (toList∘fromList xs) ⟨
    List.reverse (toList (fromList xs)) ≡⟨ toList-reverse (fromList xs) ⟨
    toList (reverse (fromList xs))      ∎
    where open ≡-Reasoning


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.3

∷-ʳ++-eqFree : ∀ a (xs : Vec A m) {ys : Vec A n} → let eq = sym (+-suc m n) in
               cast eq ((a ∷ xs) ʳ++ ys) ≡ xs ʳ++ (a ∷ ys)
∷-ʳ++-eqFree a xs {ys} = ʳ++-ʳ++-eqFree (a ∷ []) {ys = xs} {zs = ys}
{-# WARNING_ON_USAGE ∷-ʳ++-eqFree
"Warning: ∷-ʳ++-eqFree was deprecated in v2.3.
Please use ʳ++-ʳ++-eqFree instead, which does not take eq."
#-}

-- Version 2.2

-- TRANSITION TO EQ-FREE LEMMA
--
-- Please use the new proofs, which do not require an `eq` parameter.
-- In v3, `name` will be changed to be the same lemma as `name-eqFree`,
-- and `name-eqFree` will be deprecated.

++-identityʳ : ∀ .(eq : n + zero ≡ n) (xs : Vec A n) → cast eq (xs ++ []) ≡ xs
++-identityʳ _ = ++-identityʳ-eqFree
{-# WARNING_ON_USAGE ++-identityʳ
"Warning: ++-identityʳ was deprecated in v2.2.
Please use ++-identityʳ-eqFree instead, which does not take eq."
#-}

unfold-∷ʳ : ∀ .(eq : suc n ≡ n + 1) x (xs : Vec A n) → cast eq (xs ∷ʳ x) ≡ xs ++ [ x ]
unfold-∷ʳ _ = unfold-∷ʳ-eqFree
{-# WARNING_ON_USAGE unfold-∷ʳ
"Warning: unfold-∷ʳ was deprecated in v2.2.
Please use unfold-∷ʳ-eqFree instead, which does not take eq."
#-}

++-∷ʳ : ∀ .(eq : suc (m + n) ≡ m + suc n) z (xs : Vec A m) (ys : Vec A n) →
        cast eq ((xs ++ ys) ∷ʳ z) ≡ xs ++ (ys ∷ʳ z)
++-∷ʳ _ = ++-∷ʳ-eqFree
{-# WARNING_ON_USAGE ++-∷ʳ
"Warning: ++-∷ʳ was deprecated in v2.2.
Please use ++-∷ʳ-eqFree instead, which does not take eq."
#-}

∷ʳ-++ : ∀ .(eq : (suc n) + m ≡ n + suc m) a (xs : Vec A n) {ys} →
        cast eq ((xs ∷ʳ a) ++ ys) ≡ xs ++ (a ∷ ys)
∷ʳ-++ _ = ∷ʳ-++-eqFree
{-# WARNING_ON_USAGE ∷ʳ-++
"Warning: ∷ʳ-++ was deprecated in v2.2.
Please use ∷ʳ-++-eqFree instead, which does not take eq."
#-}

reverse-++ : ∀ .(eq : m + n ≡ n + m) (xs : Vec A m) (ys : Vec A n) →
             cast eq (reverse (xs ++ ys)) ≡ reverse ys ++ reverse xs
reverse-++ _ = reverse-++-eqFree
{-# WARNING_ON_USAGE reverse-++
"Warning: reverse-++ was deprecated in v2.2.
Please use reverse-++-eqFree instead, which does not take eq."
#-}

∷-ʳ++ : ∀ .(eq : (suc m) + n ≡ m + suc n) a (xs : Vec A m) {ys} →
        cast eq ((a ∷ xs) ʳ++ ys) ≡ xs ʳ++ (a ∷ ys)
∷-ʳ++ _ a xs {ys} = ʳ++-ʳ++-eqFree (a ∷ []) {ys = xs} {zs = ys}

{-# WARNING_ON_USAGE ∷-ʳ++
"Warning: ∷-ʳ++ was deprecated in v2.2.
Please use ∷-ʳ++-eqFree instead, which does not take eq."
#-}

++-ʳ++ : ∀ .(eq : m + n + o ≡ n + (m + o)) (xs : Vec A m) {ys : Vec A n} {zs : Vec A o} →
         cast eq ((xs ++ ys) ʳ++ zs) ≡ ys ʳ++ (xs ʳ++ zs)
++-ʳ++ _ = ++-ʳ++-eqFree
{-# WARNING_ON_USAGE ++-ʳ++
"Warning: ++-ʳ++ was deprecated in v2.2.
Please use ++-ʳ++-eqFree instead, which does not take eq."
#-}

ʳ++-ʳ++ : ∀ .(eq : (m + n) + o ≡ n + (m + o)) (xs : Vec A m) {ys : Vec A n} {zs} →
          cast eq ((xs ʳ++ ys) ʳ++ zs) ≡ ys ʳ++ (xs ++ zs)
ʳ++-ʳ++ _ = ʳ++-ʳ++-eqFree
{-# WARNING_ON_USAGE ʳ++-ʳ++
"Warning: ʳ++-ʳ++ was deprecated in v2.2.
Please use ʳ++-ʳ++-eqFree instead, which does not take eq."
#-}

++-assoc : ∀ .(eq : (m + n) + o ≡ m + (n + o)) (xs : Vec A m) (ys : Vec A n) (zs : Vec A o) →
           cast eq ((xs ++ ys) ++ zs) ≡ xs ++ (ys ++ zs)
++-assoc _ = ++-assoc-eqFree
{-# WARNING_ON_USAGE ++-assoc
"Warning: ++-assoc was deprecated in v2.2.
Please use ++-assoc-eqFree instead, which does not take eq."
#-}

-- Version 2.0

updateAt-id-relative = updateAt-id-local
{-# WARNING_ON_USAGE updateAt-id-relative
"Warning: updateAt-id-relative was deprecated in v2.0.
Please use updateAt-id-local instead."
#-}

updateAt-compose-relative = updateAt-updateAt-local
{-# WARNING_ON_USAGE updateAt-compose-relative
"Warning: updateAt-compose-relative was deprecated in v2.0.
Please use updateAt-updateAt-local instead."
#-}

updateAt-compose = updateAt-updateAt
{-# WARNING_ON_USAGE updateAt-compose
"Warning: updateAt-compose was deprecated in v2.0.
Please use updateAt-updateAt instead."
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
take-drop-id = take++drop≡id
{-# WARNING_ON_USAGE take-drop-id
"Warning: take-drop-id was deprecated in v2.0.
Please use take++drop≡id instead."
#-}
take-distr-zipWith = take-zipWith
{-# WARNING_ON_USAGE take-distr-zipWith
"Warning: take-distr-zipWith was deprecated in v2.0.
Please use take-zipWith instead."
#-}
take-distr-map = take-map
{-# WARNING_ON_USAGE take-distr-map
"Warning: take-distr-map was deprecated in v2.0.
Please use take-map instead."
#-}
drop-distr-zipWith = drop-zipWith
{-# WARNING_ON_USAGE drop-distr-zipWith
"Warning: drop-distr-zipWith was deprecated in v2.0.
Please use drop-zipWith instead."
#-}
drop-distr-map = drop-map
{-# WARNING_ON_USAGE drop-distr-map
"Warning: drop-distr-map was deprecated in v2.0.
Please use drop-map instead."
#-}

map-insert = map-insertAt
{-# WARNING_ON_USAGE map-insert
"Warning: map-insert was deprecated in v2.0.
Please use map-insertAt instead."
#-}
insert-lookup = insertAt-lookup
{-# WARNING_ON_USAGE insert-lookup
"Warning: insert-lookup was deprecated in v2.0.
Please use insertAt-lookup instead."
#-}
insert-punchIn = insertAt-punchIn
{-# WARNING_ON_USAGE insert-punchIn
"Warning: insert-punchIn was deprecated in v2.0.
Please use insertAt-punchIn instead."
#-}
remove-PunchOut = removeAt-punchOut
{-# WARNING_ON_USAGE remove-PunchOut
"Warning: remove-PunchOut was deprecated in v2.0.
Please use removeAt-punchOut instead."
#-}
remove-insert = removeAt-insertAt
{-# WARNING_ON_USAGE remove-insert
"Warning: remove-insert was deprecated in v2.0.
Please use removeAt-insertAt instead."
#-}
insert-remove = insertAt-removeAt
{-# WARNING_ON_USAGE insert-remove
"Warning: insert-remove was deprecated in v2.0.
Please use insertAt-removeAt instead."
#-}

lookup-inject≤-take : ∀ m (m≤m+n : m ≤ m + n) (i : Fin m) (xs : Vec A (m + n)) →
                      lookup xs (Fin.inject≤ i m≤m+n) ≡ lookup (take m xs) i
lookup-inject≤-take m m≤m+n i xs = sym (begin
  lookup (take m xs) i
    ≡⟨ lookup-take-inject≤ xs i ⟩
  lookup xs (Fin.inject≤ i _)
    ≡⟨⟩
  lookup xs (Fin.inject≤ i m≤m+n)
    ∎) where open ≡-Reasoning
{-# WARNING_ON_USAGE lookup-inject≤-take
"Warning: lookup-inject≤-take was deprecated in v2.0.
Please use lookup-take-inject≤ or lookup-truncate, take≡truncate instead."
#-}

-- Version 2.4

truncate-irrelevant : (m≤n₁ m≤n₂ : m ≤ n) → truncate {A = A} m≤n₁ ≗ truncate m≤n₂
truncate-irrelevant _ _ _ = refl
{-# WARNING_ON_USAGE truncate-irrelevant
"Warning: truncate-irrelevant was deprecated in v2.4.
Definition of truncate has been made definitionally proof-irrelevant."
#-}

