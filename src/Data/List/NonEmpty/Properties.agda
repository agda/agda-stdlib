------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.NonEmpty.Properties where

open import Level using (Level)

open import Category.Monad
open import Data.Nat
open import Data.Nat.Properties
open import Data.Maybe.Properties using (just-injective)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Categorical using () renaming (monad to listMonad)
open import Data.List.NonEmpty.Categorical using () renaming (monad to list⁺Monad)
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

length-++⁺ : (l : List A) (l′ : List⁺ A) → length (l ++⁺ l′) ≡ List.length l + length l′
length-++⁺ [] l′          = refl
length-++⁺ (x ∷ l) l′
  rewrite length-++⁺ l l′ = refl

length-++⁺′ : (l : List A) (l′ : List⁺ A) → length (l ++⁺ l′) ≡ suc (List.length l + List.length (List⁺.tail l′))
length-++⁺′ [] l′          = refl
length-++⁺′ (x ∷ l) l′
  rewrite length-++⁺′ l l′ = refl

++-++⁺ : (l : List A) → ∀ {l′ l″} → (l ++ l′) ++⁺ l″ ≡ l ++⁺ l′ ++⁺ l″
++-++⁺ []      = refl
++-++⁺ (x ∷ l) = cong (x ∷_) (cong toList (++-++⁺ l))

++⁺-cancelˡ′ : ∀ l l′ {l″ l‴ : List⁺ A} → l ++⁺ l″ ≡ l′ ++⁺ l‴ → List.length l ≡ List.length l′ → l″ ≡ l‴
++⁺-cancelˡ′ [] [] eq eql            = eq
++⁺-cancelˡ′ (x ∷ l) (y ∷ l′) eq eql = ++⁺-cancelˡ′ l l′ (just-injective (cong fromList (cong List⁺.tail eq)))
                                                         (suc-injective eql)

++⁺-cancelˡ : ∀ l {l″ l‴ : List⁺ A} → l ++⁺ l″ ≡ l ++⁺ l‴ → l″ ≡ l‴
++⁺-cancelˡ l eq = ++⁺-cancelˡ′ l l eq refl

drop-++⁺ : ∀ (xs : List A) ys → drop (List.length xs) (xs ++⁺ ys) ≡ ys
drop-++⁺ []       ys = refl
drop-++⁺ (x ∷ xs) ys = drop-++⁺ xs ys

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
