------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on the Stream type
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Stream.Properties where

open import Level using (Level)
open import Size
open import Codata.Sized.Thunk as Thunk using (Thunk; force)
open import Codata.Sized.Stream
open import Codata.Sized.Stream.Bisimilarity

open import Data.Nat.Base
open import Data.Nat.GeneralisedArithmetic using (fold; fold-pull)

open import Data.List.Base as List using ([]; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
import Data.List.Relation.Binary.Equality.Propositional as Eq
open import Data.Product as Prod using (_,_)
open import Data.Vec.Base as Vec using (_∷_)

open import Function.Base using (id; _$_; _∘′_; const)
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_; _≢_)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    i : Size

------------------------------------------------------------------------
-- repeat

lookup-repeat-identity : (n : ℕ) (a : A) → lookup (repeat a) n ≡ a
lookup-repeat-identity zero    a = P.refl
lookup-repeat-identity (suc n) a = lookup-repeat-identity n a

take-repeat-identity : (n : ℕ) (a : A) → take n (repeat a) ≡ Vec.replicate a
take-repeat-identity zero    a = P.refl
take-repeat-identity (suc n) a = P.cong (a Vec.∷_) (take-repeat-identity n a)

splitAt-repeat-identity : (n : ℕ) (a : A) → splitAt n (repeat a) ≡ (Vec.replicate a , repeat a)
splitAt-repeat-identity zero    a = P.refl
splitAt-repeat-identity (suc n) a = P.cong (Prod.map₁ (a ∷_)) (splitAt-repeat-identity n a)

replicate-repeat : ∀ {i} (n : ℕ) (a : A) → i ⊢ List.replicate n a ++ repeat a ≈ repeat a
replicate-repeat zero    a = refl
replicate-repeat (suc n) a = P.refl ∷ λ where .force → replicate-repeat n a

cycle-replicate : ∀ {i} (n : ℕ) (n≢0 : n ≢ 0) (a : A) → i ⊢ cycle (List⁺.replicate n n≢0 a) ≈ repeat a
cycle-replicate {i} n n≢0 a = let as = List⁺.replicate n n≢0 a in begin
  cycle as                           ≡⟨⟩
  as ⁺++ _                           ≈⟨ ⁺++⁺ Eq.≋-refl (λ where .force → cycle-replicate n n≢0 a) ⟩
  as ⁺++ (λ where .force → repeat a) ≈⟨ P.refl ∷ (λ where .force → replicate-repeat (pred n) a) ⟩
  repeat a                           ∎ where open ≈-Reasoning

module _ {a b} {A : Set a} {B : Set b} where

  map-repeat : ∀ (f : A → B) a {i} → i ⊢ map f (repeat a) ≈ repeat (f a)
  map-repeat f a = P.refl ∷ λ where .force → map-repeat f a

  ap-repeat : ∀ (f : A → B) a {i} → i ⊢ ap (repeat f) (repeat a) ≈ repeat (f a)
  ap-repeat f a = P.refl ∷ λ where .force → ap-repeat f a

  ap-repeatˡ : ∀ (f : A → B) as {i} → i ⊢ ap (repeat f) as ≈ map f as
  ap-repeatˡ f (a ∷ as) = P.refl ∷ λ where .force → ap-repeatˡ f (as .force)

  ap-repeatʳ : ∀ (fs : Stream (A → B) ∞) (a : A) {i} → i ⊢ ap fs (repeat a) ≈ map (_$ a) fs
  ap-repeatʳ (f ∷ fs) a = P.refl ∷ λ where .force → ap-repeatʳ (fs .force) a

  map-++ : ∀ {i} (f : A → B) as xs → i ⊢ map f (as ++ xs) ≈ List.map f as ++ map f xs
  map-++ f []       xs = refl
  map-++ f (a ∷ as) xs = P.refl ∷ λ where .force → map-++ f as xs

  map-⁺++ : ∀ {i} (f : A → B) as xs → i ⊢ map f (as ⁺++ xs) ≈ List⁺.map f as ⁺++ Thunk.map (map f) xs
  map-⁺++ f (a ∷ as) xs = P.refl ∷ (λ where .force → map-++ f as (xs .force))

  map-cycle : ∀ {i} (f : A → B) as → i ⊢ map f (cycle as) ≈ cycle (List⁺.map f as)
  map-cycle f as = begin
    map f (cycle as)       ≈⟨ map-⁺++ f as _ ⟩
    List⁺.map f as ⁺++ _   ≈⟨ ⁺++⁺ Eq.≋-refl (λ where .force → map-cycle f as) ⟩
    cycle (List⁺.map f as) ∎ where open ≈-Reasoning

------------------------------------------------------------------------
-- Functor laws

map-id : ∀ (as : Stream A ∞) → i ⊢ map id as ≈ as
map-id (a ∷ as) = P.refl ∷ λ where .force → map-id (as .force)

map-∘ : ∀ (f : A → B) (g : B → C) as → i ⊢ map g (map f as) ≈ map (g ∘′ f) as
map-∘ f g (a ∷ as) = P.refl ∷ λ where .force → map-∘ f g (as .force)


------------------------------------------------------------------------
-- splitAt

splitAt-map : ∀ n (f : A → B) xs →
  splitAt n (map f xs) ≡ Prod.map (Vec.map f) (map f) (splitAt n xs)
splitAt-map zero    f xs       = P.refl
splitAt-map (suc n) f (x ∷ xs) =
  P.cong (Prod.map₁ (f x Vec.∷_)) (splitAt-map n f (xs .force))

------------------------------------------------------------------------
-- iterate

lookup-iterate-identity : ∀ n f (a : A) → lookup (iterate f a) n ≡ fold a f n
lookup-iterate-identity zero     f a = P.refl
lookup-iterate-identity (suc n)  f a = begin
  lookup (iterate f a) (suc n) ≡⟨⟩
  lookup (iterate f (f a)) n   ≡⟨ lookup-iterate-identity n f (f a) ⟩
  fold (f a) f n               ≡⟨ fold-pull a f (const ∘′ f) (f a) P.refl (λ _ → P.refl) n ⟩
  f (fold a f n)               ≡⟨⟩
  fold a f (suc n)             ∎ where open P.≡-Reasoning

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-identity = map-id
{-# WARNING_ON_USAGE map-identity
"Warning: map-identity was deprecated in v2.0.
Please use map-id instead."
#-}

map-map-fusion = map-∘
{-# WARNING_ON_USAGE map-map-fusion
"Warning: map-map-fusion was deprecated in v2.0.
Please use map-∘ instead."
#-}
