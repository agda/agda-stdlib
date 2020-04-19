------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.NonEmpty where

open import Level using (Level)
open import Category.Monad
open import Data.Bool.Base using (Bool; false; true; not; T)
open import Data.Bool.Properties
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Data.Nat.Base as ℕ
open import Data.Product as Prod using (∃; _×_; proj₁; proj₂; _,_; -,_)
open import Data.These.Base as These using (These; this; that; these)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using () renaming (module Equivalence to Eq)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (isYes)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Non-empty lists

infixr 5 _∷_

record List⁺ (A : Set a) : Set a where
  constructor _∷_
  field
    head : A
    tail : List A

open List⁺ public

-- Basic combinators

uncons : List⁺ A → A × List A
uncons (hd ∷ tl) = hd , tl

[_] : A → List⁺ A
[ x ] = x ∷ []

infixr 5 _∷⁺_

_∷⁺_ : A → List⁺ A → List⁺ A
x ∷⁺ y ∷ xs = x ∷ y ∷ xs

length : List⁺ A → ℕ
length (x ∷ xs) = suc (List.length xs)

------------------------------------------------------------------------
-- Conversion

toList : List⁺ A → List A
toList (x ∷ xs) = x ∷ xs

fromList : List A → Maybe (List⁺ A)
fromList []       = nothing
fromList (x ∷ xs) = just (x ∷ xs)

fromVec : ∀ {n} → Vec A (suc n) → List⁺ A
fromVec (x ∷ xs) = x ∷ Vec.toList xs

toVec : (xs : List⁺ A) → Vec A (length xs)
toVec (x ∷ xs) = x ∷ Vec.fromList xs

lift : (∀ {m} → Vec A (suc m) → ∃ λ n → Vec B (suc n)) →
       List⁺ A → List⁺ B
lift f xs = fromVec (proj₂ (f (toVec xs)))

------------------------------------------------------------------------
-- Other operations

map : (A → B) → List⁺ A → List⁺ B
map f (x ∷ xs) = (f x ∷ List.map f xs)

replicate : ∀ n → n ≢ 0 → A → List⁺ A
replicate n n≢0 a = a ∷ List.replicate (pred n) a

-- Right fold. Note that s is only applied to the last element (see
-- the examples below).

foldr : (A → B → B) → (A → B) → List⁺ A → B
foldr {A = A} {B = B} c s (x ∷ xs) = foldr′ x xs
  where
  foldr′ : A → List A → B
  foldr′ x []       = s x
  foldr′ x (y ∷ xs) = c x (foldr′ y xs)

-- Right fold.

foldr₁ : (A → A → A) → List⁺ A → A
foldr₁ f = foldr f id

-- Left fold. Note that s is only applied to the first element (see
-- the examples below).

foldl : (B → A → B) → (A → B) → List⁺ A → B
foldl c s (x ∷ xs) = List.foldl c (s x) xs

-- Left fold.

foldl₁ : (A → A → A) → List⁺ A → A
foldl₁ f = foldl f id

-- Append (several variants).

infixr 5 _⁺++⁺_ _++⁺_ _⁺++_

_⁺++⁺_ : List⁺ A → List⁺ A → List⁺ A
(x ∷ xs) ⁺++⁺ (y ∷ ys) = x ∷ (xs List.++ y ∷ ys)

_⁺++_ : List⁺ A → List A → List⁺ A
(x ∷ xs) ⁺++ ys = x ∷ (xs List.++ ys)

_++⁺_ : List A → List⁺ A → List⁺ A
xs ++⁺ ys = List.foldr _∷⁺_ ys xs

concat : List⁺ (List⁺ A) → List⁺ A
concat (xs ∷ xss) = xs ⁺++ List.concat (List.map toList xss)

concatMap : (A → List⁺ B) → List⁺ A → List⁺ B
concatMap f = concat ∘′ map f

-- Reverse

reverse : List⁺ A → List⁺ A
reverse = lift (-,_ ∘′ Vec.reverse)

-- Align and Zip

alignWith : (These A B → C) → List⁺ A → List⁺ B → List⁺ C
alignWith f (a ∷ as) (b ∷ bs) = f (these a b) ∷ List.alignWith f as bs

zipWith : (A → B → C) → List⁺ A → List⁺ B → List⁺ C
zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ List.zipWith f as bs

unalignWith : (A → These B C) → List⁺ A → These (List⁺ B) (List⁺ C)
unalignWith f = foldr (These.alignWith mcons mcons ∘′ f)
                    (These.map [_] [_] ∘′ f)

  where mcons : ∀ {e} {E : Set e} → These E (List⁺ E) → List⁺ E
        mcons = These.fold [_] id _∷⁺_

unzipWith : (A → B × C) → List⁺ A → List⁺ B × List⁺ C
unzipWith f (a ∷ as) = Prod.zip _∷_ _∷_ (f a) (List.unzipWith f as)

align : List⁺ A → List⁺ B → List⁺ (These A B)
align = alignWith id

zip : List⁺ A → List⁺ B → List⁺ (A × B)
zip = zipWith _,_

unalign : List⁺ (These A B) → These (List⁺ A) (List⁺ B)
unalign = unalignWith id

unzip : List⁺ (A × B) → List⁺ A × List⁺ B
unzip = unzipWith id

-- Snoc.

infixl 5 _∷ʳ_ _⁺∷ʳ_

_∷ʳ_ : List A → A → List⁺ A
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs List.∷ʳ y)

_⁺∷ʳ_ : List⁺ A → A → List⁺ A
xs ⁺∷ʳ x = toList xs ∷ʳ x

-- A snoc-view of non-empty lists.

infixl 5 _∷ʳ′_

data SnocView {A : Set a} : List⁺ A → Set a where
  _∷ʳ′_ : (xs : List A) (x : A) → SnocView (xs ∷ʳ x)

snocView : (xs : List⁺ A) → SnocView xs
snocView (x ∷ xs)              with List.initLast xs
snocView (x ∷ .[])             | []            = []       ∷ʳ′ x
snocView (x ∷ .(xs List.∷ʳ y)) | xs List.∷ʳ' y = (x ∷ xs) ∷ʳ′ y

-- The last element in the list.

last : List⁺ A → A
last xs with snocView xs
last .(ys ∷ʳ y) | ys ∷ʳ′ y = y

-- Groups all contiguous elements for which the predicate returns the
-- same result into lists.

split : (p : A → Bool) → List A →
        List (List⁺ (∃ (T ∘ p)) ⊎ List⁺ (∃ (T ∘ not ∘ p)))
split p []       = []
split p (x ∷ xs) with p x | P.inspect p x | split p xs
... | true  | P.[ px≡t ] | inj₁ xs′ ∷ xss = inj₁ ((x , Eq.from T-≡     ⟨$⟩ px≡t) ∷⁺ xs′) ∷ xss
... | true  | P.[ px≡t ] | xss            = inj₁ [ x , Eq.from T-≡     ⟨$⟩ px≡t ]        ∷ xss
... | false | P.[ px≡f ] | inj₂ xs′ ∷ xss = inj₂ ((x , Eq.from T-not-≡ ⟨$⟩ px≡f) ∷⁺ xs′) ∷ xss
... | false | P.[ px≡f ] | xss            = inj₂ [ x , Eq.from T-not-≡ ⟨$⟩ px≡f ]        ∷ xss

-- If we flatten the list returned by split, then we get the list we
-- started with.

flatten : ∀ {p q} {P : A → Set p} {Q : A → Set q} →
          List (List⁺ (∃ P) ⊎ List⁺ (∃ Q)) → List A
flatten = List.concat ∘
          List.map Sum.[ toList ∘ map proj₁ , toList ∘ map proj₁ ]

flatten-split : (p : A → Bool) (xs : List A) → flatten (split p xs) ≡ xs
flatten-split p []       = refl
flatten-split p (x ∷ xs)
  with p x | P.inspect p x | split p xs | flatten-split p xs
... | true  | P.[ _ ] | []         | hyp = P.cong (_∷_ x) hyp
... | true  | P.[ _ ] | inj₁ _ ∷ _ | hyp = P.cong (_∷_ x) hyp
... | true  | P.[ _ ] | inj₂ _ ∷ _ | hyp = P.cong (_∷_ x) hyp
... | false | P.[ _ ] | []         | hyp = P.cong (_∷_ x) hyp
... | false | P.[ _ ] | inj₁ _ ∷ _ | hyp = P.cong (_∷_ x) hyp
... | false | P.[ _ ] | inj₂ _ ∷ _ | hyp = P.cong (_∷_ x) hyp

-- Groups all contiguous elements /not/ satisfying the predicate into
-- lists. Elements satisfying the predicate are dropped.

wordsBy : (A → Bool) → List A → List (List⁺ A)
wordsBy p =
  List.mapMaybe Sum.[ const nothing , just ∘′ map proj₁ ] ∘ split p

------------------------------------------------------------------------
-- Examples

-- Note that these examples are simple unit tests, because the type
-- checker verifies them.

private
 module Examples {A B : Set}
                 (_⊕_ : A → B → B)
                 (_⊗_ : B → A → B)
                 (_⊙_ : A → A → A)
                 (f : A → B)
                 (a b c : A)
                 where

  hd : head (a ∷⁺ b ∷⁺ [ c ]) ≡ a
  hd = refl

  tl : tail (a ∷⁺ b ∷⁺ [ c ]) ≡ b ∷ c ∷ []
  tl = refl

  mp : map f (a ∷⁺ b ∷⁺ [ c ]) ≡ f a ∷⁺ f b ∷⁺ [ f c ]
  mp = refl

  right : foldr _⊕_ f (a ∷⁺ b ∷⁺ [ c ]) ≡ (a ⊕ (b ⊕ f c))
  right = refl

  right₁ : foldr₁ _⊙_ (a ∷⁺ b ∷⁺ [ c ]) ≡ (a ⊙ (b ⊙ c))
  right₁ = refl

  left : foldl _⊗_ f (a ∷⁺ b ∷⁺ [ c ]) ≡ ((f a ⊗ b) ⊗ c)
  left = refl

  left₁ : foldl₁ _⊙_ (a ∷⁺ b ∷⁺ [ c ]) ≡ ((a ⊙ b) ⊙ c)
  left₁ = refl

  ⁺app⁺ : (a ∷⁺ b ∷⁺ [ c ]) ⁺++⁺ (b ∷⁺ [ c ]) ≡
          a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  ⁺app⁺ = refl

  ⁺app : (a ∷⁺ b ∷⁺ [ c ]) ⁺++ (b ∷ c ∷ []) ≡
          a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  ⁺app = refl

  app⁺ : (a ∷ b ∷ c ∷ []) ++⁺ (b ∷⁺ [ c ]) ≡
          a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  app⁺ = refl

  conc : concat ((a ∷⁺ b ∷⁺ [ c ]) ∷⁺ [ b ∷⁺ [ c ] ]) ≡
         a ∷⁺ b ∷⁺ c ∷⁺ b ∷⁺ [ c ]
  conc = refl

  rev : reverse (a ∷⁺ b ∷⁺ [ c ]) ≡ c ∷⁺ b ∷⁺ [ a ]
  rev = refl

  snoc : (a ∷ b ∷ c ∷ []) ∷ʳ a ≡ a ∷⁺ b ∷⁺ c ∷⁺ [ a ]
  snoc = refl

  snoc⁺ : (a ∷⁺ b ∷⁺ [ c ]) ⁺∷ʳ a ≡ a ∷⁺ b ∷⁺ c ∷⁺ [ a ]
  snoc⁺ = refl

  split-true : split (const true) (a ∷ b ∷ c ∷ []) ≡
               inj₁ ((a , tt) ∷⁺ (b , tt) ∷⁺ [ c , tt ]) ∷ []
  split-true = refl

  split-false : split (const false) (a ∷ b ∷ c ∷ []) ≡
                inj₂ ((a , tt) ∷⁺ (b , tt) ∷⁺ [ c , tt ]) ∷ []
  split-false = refl

  split-≡1 :
    split (ℕ._≡ᵇ 1) (1 ∷ 2 ∷ 3 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ []) ≡
    inj₁ [ 1 , tt ] ∷ inj₂ ((2 , tt) ∷⁺ [ 3 , tt ]) ∷
    inj₁ ((1 , tt) ∷⁺ [ 1 , tt ]) ∷ inj₂ [ 2 , tt ] ∷ inj₁ [ 1 , tt ] ∷
    []
  split-≡1 = refl

  wordsBy-true : wordsBy (const true) (a ∷ b ∷ c ∷ []) ≡ []
  wordsBy-true = refl

  wordsBy-false : wordsBy (const false) (a ∷ b ∷ c ∷ []) ≡
                  (a ∷⁺ b ∷⁺ [ c ]) ∷ []
  wordsBy-false = refl

  wordsBy-≡1 :
    wordsBy (ℕ._≡ᵇ 1) (1 ∷ 2 ∷ 3 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷ []) ≡
    (2 ∷⁺ [ 3 ]) ∷ [ 2 ] ∷ []
  wordsBy-≡1 = refl
