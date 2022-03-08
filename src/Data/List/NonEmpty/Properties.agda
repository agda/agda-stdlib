------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.NonEmpty.Properties where

open import Level using (Level)

open import Effect.Monad
open import Data.Nat
open import Data.Nat.Properties
open import Data.Maybe.Properties using (just-injective)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Effectful using () renaming (monad to listMonad)
open import Data.List.NonEmpty.Effectful using () renaming (monad to list⁺Monad)
open import Data.List.NonEmpty as List⁺
import Data.List.Properties as Listₚ
open import Function
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
private
  open module LMo {a} =
         RawMonad {f = a} listMonad
           using () renaming (_>>=_ to _⋆>>=_)
  open module L⁺Mo {a} =
         RawMonad {f = a} list⁺Monad

  variable
    a     : Level
    A B C : Set a

η : ∀ {a} {A : Set a}
    (xs : List⁺ A) → head xs ∷ tail xs ≡ List⁺.toList xs
η _ = refl

toList-fromList : ∀ {a} {A : Set a} x (xs : List A) →
                  x ∷ xs ≡ List⁺.toList (x ∷ xs)
toList-fromList _ _ = refl

toList-⁺++ : ∀ {a} {A : Set a} (xs : List⁺ A) ys →
             List⁺.toList xs ++ ys ≡
             List⁺.toList (xs ⁺++ ys)
toList-⁺++ _ _ = refl

toList-⁺++⁺ : ∀ {a} {A : Set a} (xs ys : List⁺ A) →
              List⁺.toList xs ++ List⁺.toList ys ≡
              List⁺.toList (xs ⁺++⁺ ys)
toList-⁺++⁺ _ _ = refl

toList->>= : ∀ {ℓ} {A B : Set ℓ}
             (f : A → List⁺ B) (xs : List⁺ A) →
             (List⁺.toList xs ⋆>>= List⁺.toList ∘ f) ≡
             (List⁺.toList (xs >>= f))
toList->>= f (x ∷ xs) = begin
  List.concat (List.map (List⁺.toList ∘ f) (x ∷ xs))
    ≡⟨ cong List.concat $ Listₚ.map-compose {g = List⁺.toList} (x ∷ xs) ⟩
  List.concat (List.map List⁺.toList (List.map f (x ∷ xs)))
    ∎

length-++⁺ : (xs : List A) (ys : List⁺ A) → length (xs ++⁺ ys) ≡ List.length xs + length ys
length-++⁺ [] ys                                = refl
length-++⁺ (x ∷ xs) ys rewrite length-++⁺ xs ys = refl

length-++⁺-tail : (xs : List A) (ys : List⁺ A) → length (xs ++⁺ ys) ≡ suc (List.length xs + List.length (List⁺.tail ys))
length-++⁺-tail [] ys                                     = refl
length-++⁺-tail (x ∷ xs) ys rewrite length-++⁺-tail xs ys = refl

++-++⁺ : (xs : List A) → ∀ {ys zs} → (xs ++ ys) ++⁺ zs ≡ xs ++⁺ ys ++⁺ zs
++-++⁺ []      = refl
++-++⁺ (x ∷ l) = cong (x ∷_) (cong toList (++-++⁺ l))

++⁺-cancelˡ′ : ∀ xs ys {zs zs′ : List⁺ A} → xs ++⁺ zs ≡ ys ++⁺ zs′ → List.length xs ≡ List.length ys → zs ≡ zs′
++⁺-cancelˡ′ [] [] eq eqxs            = eq
++⁺-cancelˡ′ (x ∷ xs) (y ∷ ys) eq eql = ++⁺-cancelˡ′ xs ys (just-injective (cong fromList (cong List⁺.tail eq)))
                                                           (suc-injective eql)

++⁺-cancelˡ : ∀ xs {ys zs : List⁺ A} → xs ++⁺ ys ≡ xs ++⁺ zs → ys ≡ zs
++⁺-cancelˡ xs eq = ++⁺-cancelˡ′ xs xs eq refl

drop-+-++⁺ : ∀ (xs : List A) ys → drop+ (List.length xs) (xs ++⁺ ys) ≡ ys
drop-+-++⁺ []       ys = refl
drop-+-++⁺ (x ∷ xs) ys = drop-+-++⁺ xs ys

map-++⁺-commute : ∀ (f : A → B) xs ys →
                 map f (xs ++⁺ ys) ≡ List.map f xs ++⁺ map f ys
map-++⁺-commute f [] ys       = refl
map-++⁺-commute f (x ∷ xs) ys = cong (λ zs → f x ∷ toList zs) (map-++⁺-commute f xs ys)

length-map : ∀ (f : A → B) xs → length (map f xs) ≡ length xs
length-map f (_ ∷ xs) = cong suc (Listₚ.length-map f xs)

map-cong : ∀ {f g : A → B} → f ≗ g → map f ≗ map g
map-cong f≗g (x ∷ xs) = cong₂ _∷_ (f≗g x) (Listₚ.map-cong f≗g xs)

map-compose : {g : B → C} {f : A → B} → map (g ∘ f) ≗ map g ∘ map f
map-compose (x ∷ xs) = cong (_ ∷_) (Listₚ.map-compose xs)
