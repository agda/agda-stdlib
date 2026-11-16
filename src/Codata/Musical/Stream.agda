------------------------------------------------------------------------
-- The Agda standard library
--
-- Streams
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Codata.Musical.Stream where

open import Level using (Level)
open import Codata.Musical.Notation
open import Codata.Musical.Colist using (Colist; []; _∷_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Stream (A : Set a) : Set a where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

{-# FOREIGN GHC
  data AgdaStream a = Cons a (MAlonzo.RTE.Inf (AgdaStream a))
  type AgdaStream' l a = AgdaStream a
  #-}
{-# COMPILE GHC Stream = data AgdaStream' (Cons) #-}

------------------------------------------------------------------------
-- Some operations

head : Stream A → A
head (x ∷ xs) = x

tail : Stream A → Stream A
tail (x ∷ xs) = ♭ xs

map : (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

zipWith : (A → B → C) → Stream A → Stream B → Stream C
zipWith _∙_ (x ∷ xs) (y ∷ ys) = (x ∙ y) ∷ ♯ zipWith _∙_ (♭ xs) (♭ ys)

take : ∀ n → Stream A → Vec A n
take zero    xs       = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

drop : ℕ → Stream A → Stream A
drop zero    xs       = xs
drop (suc n) (x ∷ xs) = drop n (♭ xs)

repeat : A → Stream A
repeat x = x ∷ ♯ repeat x

iterate : (A → A) → A → Stream A
iterate f x = x ∷ ♯ iterate f (f x)

-- Interleaves the two streams.

infixr 5 _⋎_

_⋎_ : Stream A → Stream A → Stream A
(x ∷ xs) ⋎ ys = x ∷ ♯ (ys ⋎ ♭ xs)

mutual

  -- Takes every other element from the stream, starting with the
  -- first one.

  evens : Stream A → Stream A
  evens (x ∷ xs) = x ∷ ♯ odds (♭ xs)

  -- Takes every other element from the stream, starting with the
  -- second one.

  odds : Stream A → Stream A
  odds (x ∷ xs) = evens (♭ xs)

toColist : Stream A → Colist A
toColist (x ∷ xs) = x ∷ ♯ toColist (♭ xs)

lookup : Stream A → ℕ → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc n) = lookup (♭ xs) n

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → Colist A → Stream A → Stream A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

------------------------------------------------------------------------
-- Equality and other relations

-- xs ≈ ys means that xs and ys are equal.

infix 4 _≈_

data _≈_ {A : Set a} : Stream A → Stream A → Set a where
  _∷_ : ∀ {x y xs ys}
        (x≡ : x ≡ y) (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ y ∷ ys

-- x ∈ xs means that x is a member of xs.

infix 4 _∈_

data _∈_ {A : Set a} : A → Stream A → Set a where
  here  : ∀ {x   xs}                   → x ∈ x ∷ xs
  there : ∀ {x y xs} (x∈xs : x ∈ ♭ xs) → x ∈ y ∷ xs

-- xs ⊑ ys means that xs is a prefix of ys.

infix 4 _⊑_

data _⊑_ {A : Set a} : Colist A → Stream A → Set a where
  []  : ∀ {ys}                            → []     ⊑ ys
  _∷_ : ∀ x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) → x ∷ xs ⊑ x ∷ ys

------------------------------------------------------------------------
-- Some proofs

setoid : ∀ {a} → Set a → Setoid _ _
setoid A = record
  { Carrier       = Stream A
  ; _≈_           = _≈_ {A = A}
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {_ ∷ _} = ≡.refl ∷ ♯ refl

  sym : Symmetric _≈_
  sym (x≡ ∷ xs≈) = ≡.sym x≡ ∷ ♯ sym (♭ xs≈)

  trans : Transitive _≈_
  trans (x≡ ∷ xs≈) (y≡ ∷ ys≈) = ≡.trans x≡ y≡ ∷ ♯ trans (♭ xs≈) (♭ ys≈)

head-cong : {xs ys : Stream A} → xs ≈ ys → head xs ≡ head ys
head-cong (x≡ ∷ _) = x≡

tail-cong : {xs ys : Stream A} → xs ≈ ys → tail xs ≈ tail ys
tail-cong (_ ∷ xs≈) = ♭ xs≈

map-cong : ∀ (f : A → B) {xs ys} →
           xs ≈ ys → map f xs ≈ map f ys
map-cong f (x≡ ∷ xs≈) = ≡.cong f x≡ ∷ ♯ map-cong f (♭ xs≈)

zipWith-cong : ∀ (_∙_ : A → B → C) {xs xs′ ys ys′} →
               xs ≈ xs′ → ys ≈ ys′ →
               zipWith _∙_ xs ys ≈ zipWith _∙_ xs′ ys′
zipWith-cong _∙_ (x≡ ∷ xs≈) (y≡ ∷ ys≈) =
  ≡.cong₂ _∙_ x≡ y≡ ∷ ♯ zipWith-cong _∙_ (♭ xs≈) (♭ ys≈)

infixr 5 _⋎-cong_

_⋎-cong_ : {xs xs′ ys ys′ : Stream A} →
           xs ≈ xs′ → ys ≈ ys′ → xs ⋎ ys ≈ xs′ ⋎ ys′
(x ∷ xs≈) ⋎-cong ys≈ = x ∷ ♯ (ys≈ ⋎-cong ♭ xs≈)
