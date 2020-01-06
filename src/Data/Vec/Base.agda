------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors, basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Base where

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base as List using (List)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_)
open import Data.These.Base as These using (These; this; that; these)
open import Function
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    a b c p : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Types

infixr 5 _∷_

data Vec (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

infix 4 _[_]=_

data _[_]=_ {A : Set a} : ∀ {n} → Vec A n → Fin n → A → Set a where
  here  : ∀ {n}     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
  there : ∀ {n} {i} {x y} {xs : Vec A n}
          (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x

------------------------------------------------------------------------
-- Basic operations

length : ∀ {n} → Vec A n → ℕ
length {n = n} _ = n

head : ∀ {n} → Vec A (1 + n) → A
head (x ∷ xs) = x

tail : ∀ {n} → Vec A (1 + n) → Vec A n
tail (x ∷ xs) = xs

lookup : ∀ {n} → Vec A n → Fin n → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

insert : ∀ {n} → Vec A n → Fin (suc n) → A → Vec A (suc n)
insert xs       zero     v = v ∷ xs
insert (x ∷ xs) (suc i)  v = x ∷ insert xs i v

remove : ∀ {n} → Vec A (suc n) → Fin (suc n) → Vec A n
remove (_ ∷ xs)     zero     = xs
remove (x ∷ y ∷ xs) (suc i)  = x ∷ remove (y ∷ xs) i

updateAt : ∀ {n} → Fin n → (A → A) → Vec A n → Vec A n
updateAt zero    f (x ∷ xs) = f x ∷ xs
updateAt (suc i) f (x ∷ xs) = x   ∷ updateAt i f xs

-- xs [ i ]%= f  modifies the i-th element of xs according to f

infixl 6 _[_]%=_

_[_]%=_ : ∀ {n} → Vec A n → Fin n → (A → A) → Vec A n
xs [ i ]%= f = updateAt i f xs

-- xs [ i ]≔ y  overwrites the i-th element of xs with y

infixl 6 _[_]≔_

_[_]≔_ : ∀ {n} → Vec A n → Fin n → A → Vec A n
xs [ i ]≔ y = xs [ i ]%= const y

------------------------------------------------------------------------
-- Operations for transforming vectors

map : ∀ {n} → (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Concatenation.

infixr 5 _++_

_++_ : ∀ {m n} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

concat : ∀ {m n} → Vec (Vec A m) n → Vec A (n * m)
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

-- Align, Restrict, and Zip.

alignWith : ∀ {m n} → (These A B → C) → Vec A m → Vec B n → Vec C (m ⊔ n)
alignWith f []         bs       = map (f ∘′ that) bs
alignWith f as@(_ ∷ _) []       = map (f ∘′ this) as
alignWith f (a ∷ as)   (b ∷ bs) = f (these a b) ∷ alignWith f as bs

restrictWith : ∀ {m n} → (A → B → C) → Vec A m → Vec B n → Vec C (m ⊓ n)
restrictWith f []       bs       = []
restrictWith f (_ ∷ _)  []       = []
restrictWith f (a ∷ as) (b ∷ bs) = f a b ∷ restrictWith f as bs

zipWith : ∀ {n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith f []       []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

unzipWith : ∀ {n} → (A → B × C) → Vec A n → Vec B n × Vec C n
unzipWith f []       = [] , []
unzipWith f (a ∷ as) = Prod.zip _∷_ _∷_ (f a) (unzipWith f as)

align : ∀ {m n} → Vec A m → Vec B n → Vec (These A B) (m ⊔ n)
align = alignWith id

restrict : ∀ {m n} → Vec A m → Vec B n → Vec (A × B) (m ⊓ n)
restrict = restrictWith _,_

zip : ∀ {n} → Vec A n → Vec B n → Vec (A × B) n
zip = zipWith _,_

unzip : ∀ {n} → Vec (A × B) n → Vec A n × Vec B n
unzip = unzipWith id

-- Interleaving.

infixr 5 _⋎_

_⋎_ : ∀ {m n} → Vec A m → Vec A n → Vec A (m +⋎ n)
[]       ⋎ ys = ys
(x ∷ xs) ⋎ ys = x ∷ (ys ⋎ xs)

-- Pointwise application

infixl 4 _⊛_

_⊛_ : ∀ {n} → Vec (A → B) n → Vec A n → Vec B n
[]       ⊛ _        = []
(f ∷ fs) ⊛ (x ∷ xs) = f x ∷ (fs ⊛ xs)

-- Multiplication

infixl 1 _>>=_

_>>=_ : ∀ {m n} → Vec A m → (A → Vec B n) → Vec B (m * n)
xs >>= f = concat (map f xs)

infixl 4 _⊛*_

_⊛*_ : ∀ {m n} → Vec (A → B) m → Vec A n → Vec B (m * n)
fs ⊛* xs = fs >>= λ f → map f xs

allPairs : ∀ {m n} → Vec A m → Vec B n → Vec (A × B) (m * n)
allPairs xs ys = map _,_ xs ⊛* ys

------------------------------------------------------------------------
-- Operations for reducing vectors

foldr : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → A → B n → B (suc n)) →
        B zero →
        Vec A m → B m
foldr b _⊕_ n []       = n
foldr b _⊕_ n (x ∷ xs) = x ⊕ foldr b _⊕_ n xs

foldr₁ : ∀ {n} → (A → A → A) → Vec A (suc n) → A
foldr₁ _⊕_ (x ∷ [])     = x
foldr₁ _⊕_ (x ∷ y ∷ ys) = x ⊕ foldr₁ _⊕_ (y ∷ ys)

foldl : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero →
        Vec A m → B m
foldl b _⊕_ n []       = n
foldl b _⊕_ n (x ∷ xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs

foldl₁ : ∀ {n} → (A → A → A) → Vec A (suc n) → A
foldl₁ _⊕_ (x ∷ xs) = foldl _ _⊕_ x xs

-- Special folds

sum : ∀ {n} → Vec ℕ n → ℕ
sum = foldr _ _+_ 0

count : ∀ {P : Pred A p} → Decidable P → ∀ {n} → Vec A n → ℕ
count P? []       = zero
count P? (x ∷ xs) with does (P? x)
... | true  = suc (count P? xs)
... | false = count P? xs

------------------------------------------------------------------------
-- Operations for building vectors

[_] : A → Vec A 1
[ x ] = x ∷ []

replicate : ∀ {n} → A → Vec A n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

tabulate : ∀ {n} → (Fin n → A) → Vec A n
tabulate {n = zero}  f = []
tabulate {n = suc n} f = f zero ∷ tabulate (f ∘ suc)

allFin : ∀ n → Vec (Fin n) n
allFin _ = tabulate id

------------------------------------------------------------------------
-- Operations for dividing vectors

splitAt : ∀ m {n} (xs : Vec A (m + n)) →
          ∃₂ λ (ys : Vec A m) (zs : Vec A n) → xs ≡ ys ++ zs
splitAt zero    xs                = ([] , xs , refl)
splitAt (suc m) (x ∷ xs)          with splitAt m xs
splitAt (suc m) (x ∷ .(ys ++ zs)) | (ys , zs , refl) =
  ((x ∷ ys) , zs , refl)

take : ∀ m {n} → Vec A (m + n) → Vec A m
take m xs          with splitAt m xs
take m .(ys ++ zs) | (ys , zs , refl) = ys

drop : ∀ m {n} → Vec A (m + n) → Vec A n
drop m xs          with splitAt m xs
drop m .(ys ++ zs) | (ys , zs , refl) = zs

group : ∀ n k (xs : Vec A (n * k)) →
        ∃ λ (xss : Vec (Vec A k) n) → xs ≡ concat xss
group zero    k []                  = ([] , refl)
group (suc n) k xs                  with splitAt k xs
group (suc n) k .(ys ++ zs)         | (ys , zs , refl) with group n k zs
group (suc n) k .(ys ++ concat zss) | (ys , ._ , refl) | (zss , refl) =
  ((ys ∷ zss) , refl)

split : ∀ {n} → Vec A n → Vec A ⌈ n /2⌉ × Vec A ⌊ n /2⌋
split []           = ([]     , [])
split (x ∷ [])     = (x ∷ [] , [])
split (x ∷ y ∷ xs) = Prod.map (x ∷_) (y ∷_) (split xs)

uncons : ∀ {n} → Vec A (suc n) → A × Vec A n
uncons (x ∷ xs) = x , xs

------------------------------------------------------------------------
-- Operations for converting between lists

toList : ∀ {n} → Vec A n → List A
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : (xs : List A) → Vec A (List.length xs)
fromList List.[]         = []
fromList (List._∷_ x xs) = x ∷ fromList xs

------------------------------------------------------------------------
-- Operations for reversing vectors

reverse : ∀ {n} → Vec A n → Vec A n
reverse {A = A} = foldl (Vec A) (λ rev x → x ∷ rev) []

infixl 5 _∷ʳ_

_∷ʳ_ : ∀ {n} → Vec A n → A → Vec A (1 + n)
[]       ∷ʳ y = [ y ]
(x ∷ xs) ∷ʳ y = x ∷ (xs ∷ʳ y)

initLast : ∀ {n} (xs : Vec A (1 + n)) →
           ∃₂ λ (ys : Vec A n) (y : A) → xs ≡ ys ∷ʳ y
initLast {n = zero}  (x ∷ [])         = ([] , x , refl)
initLast {n = suc n} (x ∷ xs)         with initLast xs
initLast {n = suc n} (x ∷ .(ys ∷ʳ y)) | (ys , y , refl) =
  ((x ∷ ys) , y , refl)

init : ∀ {n} → Vec A (1 + n) → Vec A n
init xs         with initLast xs
init .(ys ∷ʳ y) | (ys , y , refl) = ys

last : ∀ {n} → Vec A (1 + n) → A
last xs         with initLast xs
last .(ys ∷ʳ y) | (ys , y , refl) = y

------------------------------------------------------------------------
-- Other operations

transpose : ∀ {m n} → Vec (Vec A n) m → Vec (Vec A m) n
transpose []         = replicate []
transpose (as ∷ ass) = replicate _∷_ ⊛ as ⊛ transpose ass
