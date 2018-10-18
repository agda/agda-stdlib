------------------------------------------------------------------------
-- The Agda standard library
--
-- The Colist type and some operations
------------------------------------------------------------------------

module Codata.Colist where

open import Size
open import Data.Unit
open import Data.Nat.Base
open import Data.Product using (_×_ ; _,_)
open import Data.These using (These; this; that; these)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.BoundedVec as BVec using (BoundedVec)
open import Function

open import Codata.Thunk using (Thunk; force)
open import Codata.Conat as Conat using (Conat ; zero ; suc)
open import Codata.Cowriter as CW using (Cowriter; _∷_)
open import Codata.Delay as Delay using (Delay ; now ; later)
open import Codata.Stream using (Stream ; _∷_)


data Colist {a} (A : Set a) (i : Size) : Set a where
  []  : Colist A i
  _∷_ : A → Thunk (Colist A) i → Colist A i

module _ {w a} {W : Set w} {A : Set a} where

------------------------------------------------------------------------
-- Relationship to Cowriter.

  fromCowriter : ∀ {i} → Cowriter W A i → Colist W i
  fromCowriter CW.[ _ ] = []
  fromCowriter (w ∷ ca) = w ∷ λ where .force → fromCowriter (ca .force)

module _ {a} {A : Set a} where

  toCowriter : ∀ {i} → Colist A i → Cowriter A ⊤ i
  toCowriter []       = CW.[ _ ]
  toCowriter (a ∷ as) = a ∷ λ where .force → toCowriter (as .force)

------------------------------------------------------------------------
-- Basic functions.

  [_] : A → Colist A ∞
  [ a ] = a ∷ λ where .force → []

  length : ∀ {i} → Colist A i → Conat i
  length []       = zero
  length (x ∷ xs) = suc λ where .force → length (xs .force)

  replicate : ∀ {i} → Conat i → A → Colist A i
  replicate zero    a = []
  replicate (suc n) a = a ∷ λ where .force → replicate (n .force) a

  infixr 5 _++_ _⁺++_
  _++_ : ∀ {i} → Colist A i → Colist A i → Colist A i
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ λ where .force → xs .force ++ ys

  lookup : ℕ → Colist A ∞ → Maybe A
  lookup n       []       = nothing
  lookup zero    (a ∷ as) = just a
  lookup (suc n) (a ∷ as) = lookup n (as .force)

  colookup : ∀ {i} → Conat i → Colist A i → Delay (Maybe A) i
  colookup n       []       = now nothing
  colookup zero    (a ∷ as) = now (just a)
  colookup (suc n) (a ∷ as) =
    later λ where .force → colookup (n .force) (as .force)

  take : ∀ (n : ℕ) → Colist A ∞ → BoundedVec A n
  take zero    xs       = BVec.[]
  take n       []       = BVec.[]
  take (suc n) (x ∷ xs) = x BVec.∷ take n (xs .force)

  cotake : ∀ {i} → Conat i → Stream A i → Colist A i
  cotake zero    xs       = []
  cotake (suc n) (x ∷ xs) = x ∷ λ where .force → cotake (n .force) (xs .force)

  fromList : List A → Colist A ∞
  fromList []       = []
  fromList (x ∷ xs) = x ∷ λ where .force → fromList xs

  _⁺++_ : ∀ {i} → List⁺ A → Thunk (Colist A) i → Colist A i
  (x ∷ xs) ⁺++ ys = x ∷ λ where .force → fromList xs ++ ys .force

  fromStream : ∀ {i} → Stream A i → Colist A i
  fromStream = cotake Conat.infinity

module _ {ℓ} {A : Set ℓ} where

  chunksOf : (n : ℕ) → Colist A ∞ → Cowriter (Vec A n) (BoundedVec A n) ∞
  chunksOf n = chunksOfAcc n id id module ChunksOf where

    chunksOfAcc : ∀ {i} m →
      -- We have two continuations but we are only ever going to use one.
      -- If we had linear types, we would write the type using the & conjunction here.
      (k≤ : BoundedVec A m → BoundedVec A n) →
      (k≡ : Vec A m → Vec A n) →
      -- Finally we chop up the input stream.
      Colist A ∞ → Cowriter (Vec A n) (BoundedVec A n) i
    chunksOfAcc zero    k≤ k≡ as       = k≡ [] ∷ λ where .force → chunksOfAcc n id id as
    chunksOfAcc (suc k) k≤ k≡ []       = CW.[ k≤ BVec.[] ]
    chunksOfAcc (suc k) k≤ k≡ (a ∷ as) =
      chunksOfAcc k (k≤ ∘ (a BVec.∷_)) (k≡ ∘ (a ∷_)) (as .force)

module _ {a b} {A : Set a} {B : Set b} where

 map : ∀ {i} (f : A → B) → Colist A i → Colist B i
 map f []       = []
 map f (a ∷ as) = f a ∷ λ where .force → map f (as .force)

 unfold :  ∀ {i} → (A → Maybe (A × B)) → A → Colist B i
 unfold next seed with next seed
 ... | nothing          = []
 ... | just (seed′ , b) = b ∷ λ where .force → unfold next seed′

 scanl : ∀ {i} → (B → A → B) → B → Colist A i → Colist B i
 scanl c n []       = n ∷ λ where .force → []
 scanl c n (a ∷ as) = n ∷ λ where .force → scanl c (c n a) (as .force)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

  alignWith : ∀ {i} → (These A B → C) → Colist A i → Colist B i → Colist C i
  alignWith f []         bs       = map (f ∘′ that) bs
  alignWith f as@(_ ∷ _) []       = map (f ∘′ this) as
  alignWith f (a ∷ as)   (b ∷ bs) =
    f (these a b) ∷ λ where .force → alignWith f (as .force) (bs .force)

  zipWith : ∀ {i} → (A → B → C) → Colist A i → Colist B i → Colist C i
  zipWith f []       bs       = []
  zipWith f as       []       = []
  zipWith f (a ∷ as) (b ∷ bs) =
    f a b ∷ λ where .force → zipWith f (as .force) (bs .force)

module _ {a b} {A : Set a} {B : Set b} where

  align : ∀ {i} → Colist A i → Colist B i → Colist (These A B) i
  align = alignWith id

  zip : ∀ {i} → Colist A i → Colist B i → Colist (A × B) i
  zip = zipWith _,_

  ap : ∀ {i} → Colist (A → B) i → Colist A i → Colist B i
  ap = zipWith _$′_

------------------------------------------------------------------------
-- Legacy

open import Codata.Musical.Notation using (♭; ♯_)
import Codata.Musical.Colist as M

module _ {a} {A : Set a} where

  fromMusical : ∀ {i} → M.Colist A → Colist A i
  fromMusical M.[]       = []
  fromMusical (x M.∷ xs) = x ∷ λ where .force → fromMusical (♭ xs)

  toMusical : Colist A ∞ → M.Colist A
  toMusical []       = M.[]
  toMusical (x ∷ xs) = x M.∷ ♯ toMusical (xs .force)
