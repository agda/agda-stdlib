------------------------------------------------------------------------
-- The Agda standard library
--
-- Nondependent N-ary functions manipulating lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Nary.NonDependent where

open import Data.Nat.Base using (zero; suc)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product as Prod using (_,_)
open import Data.Product.Nary.NonDependent using (Product)
open import Function.Base using ()
open import Function.Nary.NonDependent.Base

------------------------------------------------------------------------
-- n-ary smart constructors

nilₙ : ∀ n {ls} {as : Sets n ls} → Product n (List <$> as)
nilₙ 0               = _
nilₙ 1               = []
nilₙ (suc n@(suc _)) = [] , nilₙ n

consₙ : ∀ n {ls} {as : Sets n ls} →
        Product n as → Product n (List <$> as) → Product n (List <$> as)
consₙ 0               _        _          = _
consₙ 1               a        as         = a ∷ as
consₙ (suc n@(suc _)) (a , xs) (as , xss) = a ∷ as , consₙ n xs xss

------------------------------------------------------------------------
-- n-ary zipWith-like operations

zipWith : ∀ n {ls} {as : Sets n ls} {r} {R : Set r} →
          Arrows n as R → Arrows n (List <$> as) (List R)
zipWith 0               f       = []
zipWith 1               f xs    = List.map f xs
zipWith (suc n@(suc _)) f xs ys =
  zipWith n (Prod.uncurry f) (List.zipWith _,_ xs ys)

unzipWith : ∀ n {ls} {as : Sets n ls} {a} {A : Set a} →
            (A → Product n as) → (List A → Product n (List <$> as))
unzipWith n f []       = nilₙ n
unzipWith n f (a ∷ as) = consₙ n (f a) (unzipWith n f as)
