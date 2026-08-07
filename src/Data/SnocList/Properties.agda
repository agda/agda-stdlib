------------------------------------------------------------------------
-- The Agda standard library
--
-- SnocList properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.SnocList.Properties where

open import Algebra.Definitions as AlgebraicDefinitions using ()
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (suc; _+_)
open import Data.Product.Base using (_,_)
open import Data.SnocList.Base
open import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Level using (Level)

open ≡-Reasoning

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- Yummy! Best gotten from Penarth Pier :-)
fish-and-chips : ∀ (xs : List> A) (sx : List< A) (ys : List> A) →
                   (sx <>< xs) <>> ys ≡ sx <>> ( ([] <>< xs) <>> ys )
fish-and-chips []        sx ys = refl
fish-and-chips xs'@(x :> xs) sx ys = begin
  (sx <>< (x :> xs)) <>> ys                   ≡⟨⟩
  ((sx <: x) <>< xs) <>> ys                   ≡⟨ fish-and-chips xs (sx <: x) ys ⟩
  (sx <: x) <>> (([] <>< xs) <>> ys)          ≡⟨⟩
  sx <>> (x :> (([] <>< xs) <>> ys))          ≡⟨⟩
  sx <>> (([] <: x) <>> (([] <>< xs) <>> ys)) ≡⟨ sym (cong (λ hole → sx <>> hole) (fish-and-chips xs ([] <: x) ys)) ⟩
  sx <>> ((([] <: x) <>< xs) <>> ys)          ≡⟨⟩
  sx <>> (([] <>< (x :> xs)) <>> ys)          ∎

toList>-fromList> : ∀ (xs : List> A) → toList> (fromList> xs) ≡ xs
toList>-fromList> [] = refl
toList>-fromList> (x :> xs) = begin
  toList> (fromList> (x :> xs))        ≡⟨⟩
  (([] <: x) <>< xs) <>> []            ≡⟨ fish-and-chips xs ([] <: x) [] ⟩
  ([] <: x) <>> (([] <>< xs) <>> [])   ≡⟨⟩
  [] <>> (x :> (([] <>< xs) <>> []))   ≡⟨⟩
  [] <>> (x :> toList> (fromList> xs)) ≡⟨ cong (λ e → [] <>> (x :> e)) (toList>-fromList> xs) ⟩
  [] <>> (x :> xs)                     ≡⟨⟩
  x :> xs                              ∎

¬xs<>>ys≡[] : ∀ {x} {xs : List< A} {ys : List> A} → xs <>> (x :> ys) ≢ []
¬xs<>>ys≡[] {xs = []} ()
¬xs<>>ys≡[] {xs = xs <: x} wrong = ¬xs<>>ys≡[] {xs = xs} wrong

xs<>>[]≡[] : ∀ {xs : List< A} → xs <>> [] ≡ [] → xs ≡ []
xs<>>[]≡[] {xs = []} xs<>>[]≡[] = refl
xs<>>[]≡[] {xs = (xs <: x)} xs<>>[]≡[] = ⊥-elim (¬xs<>>ys≡[] {xs = xs} {ys = []} xs<>>[]≡[])

-- ([] <: x <>< xs) <>> [] ≡ x :> xs
[]<><xs<>>[]≡xs : ∀ {xs : List> A} → ([] <>< xs) <>> [] ≡ xs
[]<><xs<>>[]≡xs {xs = []} = refl
[]<><xs<>>[]≡xs {xs = x :> xs} = begin
  ([] <: x <>< xs) <>> []   ≡⟨ aux {y = x} {ys = xs} ⟩
  x :> (([] <>< xs) <>> []) ≡⟨ cong (_:>_ x) ([]<><xs<>>[]≡xs {xs = xs}) ⟩
  x :> xs                   ∎
  where
    -- Goal: ([] <: y <>< ys) <>> [] ≡ y :> ([] <>< ys) <>> []
    aux : ∀ {y} {ys : List> A} → ([] <: y <>< ys) <>> [] ≡ y :> (([] <>< ys) <>> [])
    aux {y = y} {ys = ys} = begin
      ([] <: y <>< ys) <>> []            ≡⟨ fish-and-chips ys ([] <: y) [] ⟩
      ([] <: y) <>> (([] <>< ys) <>> []) ≡⟨⟩
      [] <>> (y :> (([] <>< ys) <>> [])) ≡⟨⟩
      y :> (([] <>< ys) <>> [])          ∎

------------------------------------------------------------------------
-- Properties of ++

length-++ : ∀ (xs : List< A) {ys} →
            length (ys ++ xs) ≡ length xs + length ys
length-++ []        = refl
length-++ (xs <: x) = cong suc (length-++ xs)

module _ {A : Set a} where

  open AlgebraicDefinitions {A = List< A} _≡_

  ++-identityˡ : LeftIdentity [] _++_
  ++-identityˡ [] = refl
  ++-identityˡ (xs <: x) = cong (_<: x) (++-identityˡ xs)

  ++-identityʳ : RightIdentity [] _++_
  ++-identityʳ xs = refl

  ++-identity : Identity [] _++_
  ++-identity = ++-identityˡ , ++-identityʳ
