------------------------------------------------------------------------
-- The Agda standard library
--
-- Alternative implementation of non-empty lists
------------------------------------------------------------------------

module Data.List.NonEmpty2 where

open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.Vec as Vec using (Vec ; [] ; _∷_)
open import Data.Nat
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; ∃ ; ,_ ; _×_)

open import Category.Monad
open import Function

not-empty : ∀ {a} {A : Set a} → List A → Set
not-empty []      = ⊥
not-empty (_ ∷ _) = ⊤

List⁺ : ∀ {a} (A : Set a) → Set a
List⁺ A = Σ (List A) not-empty

module _ {a} {A : Set a} where
  [_] : A → List⁺ A
  [ x ] = x ∷ [] , tt

  tup : List⁺ A → A × List A
  tup ([] , ())
  tup (x ∷ xs , tt) = x , xs

  head : List⁺ A → A
  head = proj₁ ∘ tup

  tail : List⁺ A → List A
  tail = proj₂ ∘ tup

  infixr 5 _∷⁺_

  _∷⁺_ : A → List⁺ A → List⁺ A
  x ∷⁺ (l , _) = (x ∷ l) , _

  toList : List⁺ A → List A
  toList = proj₁

  length : List⁺ A → ℕ
  length = List.length ∘ toList

  ------------------------------------------------------------------------
  -- Conversion

  fromList : List A → Maybe (List⁺ A)
  fromList []       = nothing
  fromList (x ∷ xs) = just (x ∷ xs , tt)

  fromVec : ∀ {n} → Vec A (suc n) → List⁺ A
  fromVec (x ∷ xs) = (x ∷ Vec.toList xs) , _

  toVec : (xs : List⁺ A) → Vec A (length xs)
  toVec = Vec.fromList ∘ toList

  toVec′ : List⁺ A → ∃ λ n → Vec A (suc n)
  toVec′ ([] , ())
  toVec′ l@(_ ∷ xs , tt) = List.length xs , toVec l

lift : ∀ {a b} {A : Set a} {B : Set b} →
       (∀ {m} → Vec A (suc m) → ∃ λ n → Vec B (suc n)) →
       List⁺ A → List⁺ B
lift f xs = fromVec $ proj₂ $ f $ proj₂ $ toVec′ xs

------------------------------------------------------------------------
-- Other operations

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List⁺ A → List⁺ B
map f ([] , ())
map f (x ∷ xs , tt) = List.map f (x ∷ xs) , tt

-- Right fold. Note that s is only applied to the last element

foldr : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → B) → (A → B) → List⁺ A → B
foldr c s ([] , ())
foldr c s (x ∷ xs , tt) = List.foldr c (s x) xs

-- Right fold.

foldr₁ : ∀ {a} {A : Set a} → (A → A → A) → List⁺ A → A
foldr₁ f = foldr f id

-- Left fold. Note that s is only applied to the first element

foldl : ∀ {a b} {A : Set a} {B : Set b} →
        (B → A → B) → (A → B) → List⁺ A → B
foldl c s ([] , ())
foldl c s (x ∷ xs , tt) = List.foldl c (s x) xs

-- Left fold.

foldl₁ : ∀ {a} {A : Set a} → (A → A → A) → List⁺ A → A
foldl₁ f = foldl f id

-- Append (several variants).

infixr 5 _⁺++⁺_ _++⁺_ _⁺++_

_⁺++⁺_ : ∀ {a} {A : Set a} → List⁺ A → List⁺ A → List⁺ A
([] , ()) ⁺++⁺ ys
(x ∷ xs , tt) ⁺++⁺ ys = (x ∷ xs List.++ toList ys) , tt

_⁺++_ : ∀ {a} {A : Set a} → List⁺ A → List A → List⁺ A
([] , ()) ⁺++ ys
(x ∷ xs , tt) ⁺++ ys = (x ∷ xs List.++ ys) , tt

_++⁺_ : ∀ {a} {A : Set a} → List A → List⁺ A → List⁺ A
[] ++⁺ ys = ys
(x ∷ xs) ++⁺ ys = (x ∷ xs , _) ⁺++⁺ ys

concat : ∀ {a} {A : Set a} → List⁺ (List⁺ A) → List⁺ A
concat ([] , ())
concat (xs ∷ xss , tt) = xs ⁺++ List.concat (List.map toList xss)

monad : ∀ {f} → RawMonad (List⁺ {a = f})
monad = record
  { return = [_]
  ; _>>=_  = λ xs f → concat (map f xs)
  }

reverse : ∀ {a} {A : Set a} → List⁺ A → List⁺ A
reverse = lift (,_ ∘′ Vec.reverse)

-- Snoc.

infixl 5 _∷ʳ_ _⁺∷ʳ_

_∷ʳ_ : ∀ {a} {A : Set a} → List A → A → List⁺ A
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs List.∷ʳ y) , _

_⁺∷ʳ_ : ∀ {a} {A : Set a} → List⁺ A → A → List⁺ A
xs ⁺∷ʳ x = toList xs ∷ʳ x

-- The last element in the list.

last : ∀ {a} {A : Set a} → List⁺ A → A
last = Vec.last ∘ proj₂ ∘ toVec′

-- we show that this definition is the same as the other one

open import Relation.Binary.PropositionalEquality
open import Data.List.NonEmpty as Alt using (_∷_)
  renaming (List⁺ to List⁺′ ; head to head′ ; tail to tail′)

module _ {a} {A : Set a} where

  List⁺⇒List⁺′ : List⁺ A → List⁺′ A
  List⁺⇒List⁺′ xs with tup xs
  ... | (h , t) = h ∷ t

  List⁺′⇒List⁺ : List⁺′ A → List⁺ A
  List⁺′⇒List⁺ (x ∷ xs) = x ∷ xs , tt

  List⁺≡List⁺′ : ∀ l → toList l ≡ Alt.toList (List⁺⇒List⁺′ l)
  List⁺≡List⁺′ ([] , ())
  List⁺≡List⁺′ (x ∷ l , tt) = refl

  List⁺′≡List⁺ : ∀ l → Alt.toList l ≡ toList (List⁺′⇒List⁺ l)
  List⁺′≡List⁺ (h ∷ t) = refl
