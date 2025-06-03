------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of padRight for Vec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Padrightpropertiesdraft where

open import Data.Fin.Base using (Fin; zero; suc; inject≤)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m+n∸m≡n)
open import Data.Vec.Base
open import Data.Vec.Properties using (map-replicate; zipWith-replicate; padRight-trans)
open import Function.Base using (_∘_; _$_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    m n p : ℕ


------------------------------------------------------------------------
-- Interaction with map

padRight-map : ∀ (f : A → B) (m≤n : m ≤ n) (a : A) (xs : Vec A m) →
               map f (padRight m≤n a xs) ≡ padRight m≤n (f a) (map f xs)
padRight-map f z≤n a [] = map-replicate f a _
padRight-map f (s≤s m≤n) a (x ∷ xs) = cong (f x ∷_) (padRight-map f m≤n a xs)

------------------------------------------------------------------------
-- Interaction with lookup

padRight-lookup : ∀ (m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin m) →
                  lookup (padRight m≤n a xs) (inject≤ i m≤n) ≡ lookup xs i
padRight-lookup (s≤s m≤n) a (x ∷ xs) zero = refl
padRight-lookup (s≤s m≤n) a (x ∷ xs) (suc i) = padRight-lookup m≤n a xs i

------------------------------------------------------------------------
-- Interaction with zipWith

-- When both vectors have the same original length
padRight-zipWith : ∀ (f : A → B → C) (m≤n : m ≤ n) (a : A) (b : B)
                   (xs : Vec A m) (ys : Vec B m) →
                   zipWith f (padRight m≤n a xs) (padRight m≤n b ys) ≡
                   padRight m≤n (f a b) (zipWith f xs ys)
padRight-zipWith f z≤n a b [] [] = zipWith-replicate f a b
padRight-zipWith f (s≤s m≤n) a b (x ∷ xs) (y ∷ ys) =
  cong (f x y ∷_) (padRight-zipWith f m≤n a b xs ys)

-- When vectors have different original lengths
padRight-zipWith₁ : ∀ {p} (f : A → B → C) (m≤n : m ≤ n) (p≤m : p ≤ m)
                    (a : A) (b : B) (xs : Vec A m) (ys : Vec B p) →
                    zipWith f (padRight m≤n a xs) (padRight (≤-trans p≤m m≤n) b ys) ≡
                    padRight m≤n (f a b) (zipWith f xs (padRight p≤m b ys))
padRight-zipWith₁ {p} f m≤n p≤m a b xs ys =
  trans (cong (zipWith f (padRight m≤n a xs)) (padRight-trans p≤m m≤n b ys))
        (padRight-zipWith f m≤n a b xs (padRight p≤m b ys))

------------------------------------------------------------------------
-- Interaction with take and drop

padRight-take : ∀ {p} (m≤n : m ≤ n) (a : A) (xs : Vec A m) (n≡m+p : n ≡ m + p) →
                take m (subst (Vec A) n≡m+p (padRight m≤n a xs)) ≡ xs
padRight-take {m = zero} z≤n a [] refl = refl
padRight-take {m = suc m} {p = p} (s≤s m≤n) a (x ∷ xs) refl =
  cong (x ∷_) (padRight-take {p = p} m≤n a xs refl)

-- Helper lemma: commuting subst with drop
subst-drop : ∀ {m n p : ℕ} {A : Set} (eq : n ≡ m + p) (xs : Vec A n) →
             drop m (subst (Vec A) eq xs) ≡ subst (Vec A) (cong (_∸ m) eq) (drop m xs)
subst-drop refl xs = refl

-- Helper lemma: dropping from padded vector gives replicate  
drop-padRight : ∀ {m n p} (m≤n : m ≤ n) (a : A) (xs : Vec A m) →
                n ≡ m + p → drop m (padRight m≤n a xs) ≡ replicate p a
drop-padRight {m = zero} z≤n a [] refl = refl
drop-padRight {m = suc m} {p = p} (s≤s m≤n) a (x ∷ xs) refl =
  drop-padRight {p = p} m≤n a xs refl

padRight-drop : ∀ {p} (m≤n : m ≤ n) (a : A) (xs : Vec A m) (n≡m+p : n ≡ m + p) →
                drop m (subst (Vec A) n≡m+p (padRight m≤n a xs)) ≡ replicate p a
padRight-drop {p = p} m≤n a xs n≡m+p =
  trans (subst-drop n≡m+p (padRight m≤n a xs))
        (cong (subst (Vec A) (cong (_∸ _) n≡m+p)) (drop-padRight m≤n a xs n≡m+p))

------------------------------------------------------------------------
-- Interaction with updateAt

padRight-updateAt : ∀ (m≤n : m ≤ n) (xs : Vec A m) (f : A → A) (i : Fin m) (x : A) →
                    updateAt (padRight m≤n x xs) (inject≤ i m≤n) f ≡
                    padRight m≤n x (updateAt xs i f)
padRight-updateAt (s≤s m≤n) (y ∷ xs) f zero x = refl
padRight-updateAt (s≤s m≤n) (y ∷ xs) f (suc i) x =
  cong (y ∷_) (padRight-updateAt m≤n xs f i x)





