------------------------------------------------------------------------
-- The Agda standard library
--
-- The Covec type and some operations
------------------------------------------------------------------------

module Codata.Covec where

open import Size

open import Codata.Thunk using (Thunk; force)
open import Codata.Conat as Conat
open import Codata.Conat.Bisimilarity
open import Codata.Conat.Properties
open import Codata.Cofin as Cofin using (Cofin; zero; suc)
open import Codata.Colist as Colist using (Colist ; [] ; _∷_)
open import Codata.Stream as Stream using (Stream ; _∷_)
open import Function

data Covec {ℓ} (A : Set ℓ) (i : Size) : Conat ∞ → Set ℓ where
  []  : Covec A i zero
  _∷_ : ∀ {n} → A → Thunk (λ i → Covec A i (n .force)) i → Covec A i (suc n)

module _ {ℓ} {A : Set ℓ} where

 head : ∀ {n i} → Covec A i (suc n) → A
 head (x ∷ _) = x

 tail : ∀ {n} → Covec A ∞ (suc n) → Covec A ∞ (n .force)
 tail (_ ∷ xs) = xs .force

 lookup : ∀ {n} → Cofin n → Covec A ∞ n → A
 lookup zero    = head
 lookup (suc k) = lookup k ∘′ tail

 replicate : ∀ {i} → (n : Conat ∞) → A → Covec A i n
 replicate zero    a = []
 replicate (suc n) a = a ∷ λ where .force → replicate (n .force) a

 cotake : ∀ {i} → (n : Conat ∞) → Stream A i → Covec A i n
 cotake zero    xs       = []
 cotake (suc n) (x ∷ xs) = x ∷ λ where .force → cotake (n .force) (xs .force)

 infixr 5 _++_
 _++_ : ∀ {i m n} → Covec A i m → Covec A i n → Covec A i (m + n)
 []       ++ ys = ys
 (x ∷ xs) ++ ys = x ∷ λ where .force → xs .force ++ ys

 fromColist : ∀ {i} → (xs : Colist A ∞) → Covec A i (Colist.length xs)
 fromColist []       = []
 fromColist (x ∷ xs) = x ∷ λ where .force → fromColist (xs .force)

 toColist : ∀ {i n} → Covec A i n → Colist A i
 toColist []       = []
 toColist (x ∷ xs) = x ∷ λ where .force → toColist (xs .force)

 fromStream : ∀ {i} → Stream A i → Covec A i infinity
 fromStream = cotake infinity

 cast : ∀ {i} {m n} → i ⊢ m ≈ n → Covec A i m → Covec A i n
 cast zero     []       = []
 cast (suc eq) (a ∷ as) = a ∷ λ where .force → cast (eq .force) (as .force)

module _ {a b} {A : Set a} {B : Set b} where

 map : ∀ {i n} (f : A → B) → Covec A i n → Covec B i n
 map f []       = []
 map f (a ∷ as) = f a ∷ λ where .force → map f (as .force)

 ap : ∀ {i n} → Covec (A → B) i n → Covec A i n → Covec B i n
 ap []       []       = []
 ap (f ∷ fs) (a ∷ as) = (f a) ∷ λ where .force → ap (fs .force) (as .force)

 scanl : ∀ {i n} → (B → A → B) → B → Covec A i n → Covec B i (1 ℕ+ n)
 scanl c n []       = n ∷ λ where .force → []
 scanl c n (a ∷ as) = n ∷ λ where
   .force → cast (suc λ where .force → 0ℕ+-identity)
                 (scanl c (c n a) (as .force))

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 zipWith : ∀ {i n} → (A → B → C) → Covec A i n → Covec B i n → Covec C i n
 zipWith f []       []       = []
 zipWith f (a ∷ as) (b ∷ bs) =
   f a b ∷ λ where .force → zipWith f (as .force) (bs .force)
