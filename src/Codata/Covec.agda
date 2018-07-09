------------------------------------------------------------------------
-- The Agda standard library
--
-- The Covec type and some operations
------------------------------------------------------------------------

module Codata.Covec where

open import Size

open import Codata.Thunk
open import Codata.Conat as Conat hiding (fromMusical)
open import Codata.Conat.Bisimilarity
open import Codata.Conat.Properties
open import Codata.Colist as Colist using (Colist ; [] ; _∷_)
open import Codata.Stream as Stream using (Stream ; _∷_)

data Covec {ℓ} (A : Set ℓ) (i : Size) : Conat ∞ → Set ℓ where
  []  : Covec A i zero
  _∷_ : ∀ {n} → A → Thunk (λ i → Covec A i (n .force)) i → Covec A i (suc n)

module _ {ℓ} {A : Set ℓ} where

 replicate : (n : Conat ∞) → A → ∀ {i} → Covec A i n
 replicate zero    a = []
 replicate (suc n) a = a ∷ λ where .force → replicate (n .force) a

 cotake : (n : Conat ∞) → ∀ {i} → Stream A i → Covec A i n
 cotake zero    xs       = []
 cotake (suc n) (x ∷ xs) = x ∷ λ where .force → cotake (n .force) (xs .force)

 infixr 5 _++_
 _++_ : ∀ {i m n} → Covec A i m → Covec A i n → Covec A i (m + n)
 []       ++ ys = ys
 (x ∷ xs) ++ ys = x ∷ λ where .force → xs .force ++ ys

 fromColist : (xs : Colist A ∞) → ∀ {i} → Covec A i (Colist.length xs)
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

 map : ∀ (f : A → B) → ∀ {i n} → Covec A i n → Covec B i n
 map f []       = []
 map f (a ∷ as) = f a ∷ λ where .force → map f (as .force)

 ap : ∀ {i n} → Covec (A → B) i n → Covec A i n → Covec B i n
 ap []       []       = []
 ap (f ∷ fs) (a ∷ as) = (f a) ∷ λ where .force → ap (fs .force) (as .force)

 scanl : (B → A → B) → B → ∀ {i n} → Covec A i n → Covec B i (1 ℕ+ n)
 scanl c n []       = n ∷ λ where .force → []
 scanl c n (a ∷ as) = n ∷ λ where
   .force → cast (suc λ where .force → 0ℕ+-identity)
                 (scanl c (c n a) (as .force))

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

 zipWith : (A → B → C) → ∀ {i n} → Covec A i n → Covec B i n → Covec C i n
 zipWith f []       []       = []
 zipWith f (a ∷ as) (b ∷ bs) =
   f a b ∷ λ where .force → zipWith f (as .force) (bs .force)



------------------------------------------------------------------------
-- Legacy

open import Coinduction
import Codata.Musical.Covec as M

fromMusical : ∀ {a} {A : Set a} {n} →
              M.Covec A n → ∀ {i} → Covec A i (Conat.fromMusical n)
fromMusical M.[]       = []
fromMusical (x M.∷ xs) = x ∷ λ where .force → fromMusical (♭ xs)
