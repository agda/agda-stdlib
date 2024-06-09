------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors, basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Base where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Nat.Base
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base as List using (List)
open import Data.Product.Base as Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.These.Base as These using (These; this; that; these)
open import Function.Base using (const; _∘′_; id; _∘_; _$_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; trans; cong)
open import Relation.Nullary.Decidable.Core using (does; T?)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    a b c p : Level
    A : Set a
    B : Set b
    C : Set c
    m n : ℕ

------------------------------------------------------------------------
-- Types

infixr 5 _∷_

data Vec (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ (x : A) (xs : Vec A n) → Vec A (suc n)

infix 4 _[_]=_

data _[_]=_ {A : Set a} : Vec A n → Fin n → A → Set a where
  here  : ∀     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
  there : ∀ {i} {x y} {xs : Vec A n}
    (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x

------------------------------------------------------------------------
-- Basic operations

length : Vec A n → ℕ
length {n = n} _ = n

head : Vec A (1 + n) → A
head (x ∷ xs) = x

tail : Vec A (1 + n) → Vec A n
tail (x ∷ xs) = xs

lookup : Vec A n → Fin n → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

iterate : (A → A) → A → ∀ n → Vec A n
iterate s z zero    = []
iterate s z (suc n) = z ∷ iterate s (s z) n

insertAt : Vec A n → Fin (suc n) → A → Vec A (suc n)
insertAt xs       zero     v = v ∷ xs
insertAt (x ∷ xs) (suc i)  v = x ∷ insertAt xs i v

removeAt : Vec A (suc n) → Fin (suc n) → Vec A n
removeAt (x ∷ xs)         zero    = xs
removeAt (x ∷ xs@(_ ∷ _)) (suc i) = x ∷ removeAt xs i

updateAt : Vec A n → Fin n → (A → A) → Vec A n
updateAt (x ∷ xs) zero    f = f x ∷ xs
updateAt (x ∷ xs) (suc i) f = x   ∷ updateAt xs i f

-- xs [ i ]%= f  modifies the i-th element of xs according to f

infixl 6 _[_]%=_ _[_]≔_

_[_]%=_ : Vec A n → Fin n → (A → A) → Vec A n
xs [ i ]%= f = updateAt xs i f

-- xs [ i ]≔ y  overwrites the i-th element of xs with y

_[_]≔_ : Vec A n → Fin n → A → Vec A n
xs [ i ]≔ y = xs [ i ]%= const y

------------------------------------------------------------------------
-- Operations for transforming vectors

-- See README.Data.Vec.Relation.Binary.Equality.Cast for the reasoning
-- system of `cast`-ed equality.
cast : .(eq : m ≡ n) → Vec A m → Vec A n
cast {n = zero}  eq []       = []
cast {n = suc _} eq (x ∷ xs) = x ∷ cast (cong pred eq) xs

map : (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Concatenation.

infixr 5 _++_

_++_ : Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : Vec (Vec A m) n → Vec A (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

-- Align, Restrict, and Zip.

alignWith : (These A B → C) → Vec A m → Vec B n → Vec C (m ⊔ n)
alignWith f []         bs       = map (f ∘′ that) bs
alignWith f as@(_ ∷ _) []       = map (f ∘′ this) as
alignWith f (a ∷ as)   (b ∷ bs) = f (these a b) ∷ alignWith f as bs

restrictWith : (A → B → C) → Vec A m → Vec B n → Vec C (m ⊓ n)
restrictWith f []       bs       = []
restrictWith f (_ ∷ _)  []       = []
restrictWith f (a ∷ as) (b ∷ bs) = f a b ∷ restrictWith f as bs

zipWith : (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith f []       []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

unzipWith : (A → B × C) → Vec A n → Vec B n × Vec C n
unzipWith f []       = [] , []
unzipWith f (a ∷ as) = Product.zip _∷_ _∷_ (f a) (unzipWith f as)

align : Vec A m → Vec B n → Vec (These A B) (m ⊔ n)
align = alignWith id

restrict : Vec A m → Vec B n → Vec (A × B) (m ⊓ n)
restrict = restrictWith _,_

zip : Vec A n → Vec B n → Vec (A × B) n
zip = zipWith _,_

unzip : Vec (A × B) n → Vec A n × Vec B n
unzip = unzipWith id

-- Interleaving.

infixr 5 _⋎_

_⋎_ : Vec A m → Vec A n → Vec A (m +⋎ n)
[]       ⋎ ys = ys
(x ∷ xs) ⋎ ys = x ∷ (ys ⋎ xs)

-- Pointwise application

infixl 4 _⊛_

_⊛_ : Vec (A → B) n → Vec A n → Vec B n
[]       ⊛ []       = []
(f ∷ fs) ⊛ (x ∷ xs) = f x ∷ (fs ⊛ xs)

-- Multiplication

module CartesianBind where
  infixl 1 _>>=_

  _>>=_ : Vec A m → (A → Vec B n) → Vec B (m * n)
  xs >>= f = concat (map f xs)

infixl 4 _⊛*_

_⊛*_ : Vec (A → B) m → Vec A n → Vec B (m * n)
fs ⊛* xs = fs CartesianBind.>>= λ f → map f xs

allPairs : Vec A m → Vec B n → Vec (A × B) (m * n)
allPairs xs ys = map _,_ xs ⊛* ys

-- Diagonal

diagonal : Vec (Vec A n) n → Vec A n
diagonal [] = []
diagonal (xs ∷ xss) = head xs ∷ diagonal (map tail xss)

module DiagonalBind where
  infixl 1 _>>=_

  _>>=_ : Vec A n → (A → Vec B n) → Vec B n
  xs >>= f = diagonal (map f xs)


------------------------------------------------------------------------
-- Operations for reducing vectors

-- Dependent folds

module _ (A : Set a) (B : ℕ → Set b) where

  FoldrOp = ∀ {n} → A → B n → B (suc n)
  FoldlOp = ∀ {n} → B n → A → B (suc n)

foldr : ∀ (B : ℕ → Set b) → FoldrOp A B → B zero → Vec A n → B n
foldr B _⊕_ e []       = e
foldr B _⊕_ e (x ∷ xs) = x ⊕ foldr B _⊕_ e xs

foldl : ∀ (B : ℕ → Set b) → FoldlOp A B → B zero → Vec A n → B n
foldl B _⊕_ e []       = e
foldl B _⊕_ e (x ∷ xs) = foldl (B ∘ suc) _⊕_ (e ⊕ x) xs

-- Non-dependent folds

foldr′ : (A → B → B) → B → Vec A n → B
foldr′ _⊕_ = foldr _ _⊕_

foldl′ : (B → A → B) → B → Vec A n → B
foldl′ _⊕_ = foldl _ _⊕_

-- Non-empty folds

foldr₁ : (A → A → A) → Vec A (suc n) → A
foldr₁ _⊕_ (x ∷ [])     = x
foldr₁ _⊕_ (x ∷ y ∷ ys) = x ⊕ foldr₁ _⊕_ (y ∷ ys)

foldl₁ : (A → A → A) → Vec A (suc n) → A
foldl₁ _⊕_ (x ∷ xs) = foldl _ _⊕_ x xs

-- Special folds

sum : Vec ℕ n → ℕ
sum = foldr _ _+_ 0

count : ∀ {P : Pred A p} → Decidable P → Vec A n → ℕ
count P? []       = zero
count P? (x ∷ xs) = if does (P? x) then suc else id $ count P? xs

countᵇ : (A → Bool) → Vec A n → ℕ
countᵇ p = count (T? ∘ p)

------------------------------------------------------------------------
-- Operations for building vectors

[_] : A → Vec A 1
[ x ] = x ∷ []

replicate : (n : ℕ) → A → Vec A n
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

tabulate : (Fin n → A) → Vec A n
tabulate {n = zero}  f = []
tabulate {n = suc n} f = f zero ∷ tabulate (f ∘ suc)

allFin : ∀ n → Vec (Fin n) n
allFin _ = tabulate id

------------------------------------------------------------------------
-- Operations for dividing vectors

splitAt : ∀ m {n} (xs : Vec A (m + n)) →
          ∃₂ λ (ys : Vec A m) (zs : Vec A n) → xs ≡ ys ++ zs
splitAt zero    xs                = [] , xs , refl
splitAt (suc m) (x ∷ xs) =
  let ys , zs , eq = splitAt m xs in x ∷ ys , zs , cong (x ∷_) eq

take : ∀ m {n} → Vec A (m + n) → Vec A m
take m xs = proj₁ (splitAt m xs)

drop : ∀ m {n} → Vec A (m + n) → Vec A n
drop m xs = proj₁ (proj₂ (splitAt m xs))

group : ∀ n k (xs : Vec A (n * k)) →
        ∃ λ (xss : Vec (Vec A k) n) → xs ≡ concat xss
group zero    k []                  = ([] , refl)
group (suc n) k xs  =
  let ys , zs , eq-split = splitAt k xs in
  let zss , eq-group     = group n k zs in
   (ys ∷ zss) , trans eq-split (cong (ys ++_) eq-group)

split : Vec A n → Vec A ⌈ n /2⌉ × Vec A ⌊ n /2⌋
split []           = ([]     , [])
split (x ∷ [])     = (x ∷ [] , [])
split (x ∷ y ∷ xs) = Product.map (x ∷_) (y ∷_) (split xs)

uncons : Vec A (suc n) → A × Vec A n
uncons (x ∷ xs) = x , xs

------------------------------------------------------------------------
-- Operations involving ≤

-- Take the first 'm' elements of a vector.
truncate : ∀ {m n} → m ≤ n → Vec A n → Vec A m
truncate {m = zero} _ _    = []
truncate (s≤s le) (x ∷ xs) = x ∷ (truncate le xs)

-- Pad out a vector with extra elements.
padRight : ∀ {m n} → m ≤ n → A → Vec A m → Vec A n
padRight z≤n      a xs       = replicate _ a
padRight (s≤s le) a (x ∷ xs) = x ∷ padRight le a xs

------------------------------------------------------------------------
-- Operations for converting between lists

toList : Vec A n → List A
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : (xs : List A) → Vec A (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs

------------------------------------------------------------------------
-- Operations for reversing vectors

-- snoc

infixl 5 _∷ʳ_

_∷ʳ_ : Vec A n → A → Vec A (suc n)
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

-- vanilla reverse

reverse : Vec A n → Vec A n
reverse = foldl (Vec _) (λ rev x → x ∷ rev) []

-- reverse-append

infix 5 _ʳ++_

_ʳ++_ : Vec A m → Vec A n → Vec A (m + n)
xs ʳ++ ys = foldl (Vec _ ∘ (_+ _)) (λ rev x → x ∷ rev) ys xs

-- init and last

initLast : ∀ (xs : Vec A (1 + n)) → ∃₂ λ ys y → xs ≡ ys ∷ʳ y
initLast {n = zero}  (x ∷ []) = [] , x , refl
initLast {n = suc n} (x ∷ xs) =
  let ys , y , eq = initLast xs in
  x ∷ ys , y , cong (x ∷_) eq

init : Vec A (1 + n) → Vec A n
init xs = proj₁ (initLast xs)

last : Vec A (1 + n) → A
last xs = proj₁ (proj₂ (initLast xs))

------------------------------------------------------------------------
-- Other operations

transpose : Vec (Vec A n) m → Vec (Vec A m) n
transpose {n = n} []          = replicate n []
transpose {n = n} (as ∷ ass) = ((replicate n _∷_) ⊛ as) ⊛ transpose ass

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

remove = removeAt
{-# WARNING_ON_USAGE remove
"Warning: remove was deprecated in v2.0.
Please use removeAt instead."
#-}
insert = insertAt
{-# WARNING_ON_USAGE insert
"Warning: insert was deprecated in v2.0.
Please use insertAt instead."
#-}
