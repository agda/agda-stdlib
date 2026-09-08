------------------------------------------------------------------------
-- The Agda standard library
--
-- Nondependent heterogeneous N-ary products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Nary.NonDependent where

------------------------------------------------------------------------
-- Concrete examples can be found in README.Nary. This file's comments
-- are more focused on the implementation details and the motivations
-- behind the design decisions.
------------------------------------------------------------------------

open import Level using (Level)
open import Data.Product.Base as Prod
import Data.Product.Properties as Prodₚ
open import Data.Sum.Base using (_⊎_)
open import Data.Nat.Base using (ℕ; zero; suc; pred)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Unit.Base using (⊤)
open import Function.Base using (const; _∘′_; _∘_)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no; _×?_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong₂)

open import Function.Nary.NonDependent.Base

-- Provided n Levels and a corresponding "vector" of `n` Sets, we can
-- build a big right-nested product type packing a value for each one
-- of these Sets.
-- We have two distinct but equivalent definitions:
-- the first which is always ⊤-terminated
-- the other which has a special case for n = 1 because we want our
-- `(un)curryₙ` functions to work for user-written functions and
-- products and they rarely are ⊤-terminated.

Product⊤ : ∀ n {ls} → Sets n ls → Set (⨆ n ls)
Product⊤ zero    as       = ⊤
Product⊤ (suc n) (a , as) = a × Product⊤ n as

Product : ∀ n {ls} → Sets n ls → Set (⨆ n ls)
Product 0       _        = ⊤
Product 1       (a , _)  = a
Product (suc n) (a , as) = a × Product n as

-- An n-ary product where every element of the product lives at the same universe level.

HomoProduct′ : ∀ n {a} → (Fin n → Set a) → Set (lconst n a)
HomoProduct′ n f = Product n (stabulate n (const _) f)

-- An n-ary product where every element of the product lives in the same type.

HomoProduct : ∀ n {a} → Set a → Set (lconst n a)
HomoProduct n A = HomoProduct′ n (const A)

-- Pointwise lifting of a relation over n-ary products

Pointwiseₙ : (∀ {a} {A : Set a} → Rel A a) →
             ∀ n {ls} {as : Sets n ls} (l r : Product n as) → Sets n ls
Pointwiseₙ R 0               l       r       = _
Pointwiseₙ R 1               a       b       = R a b , _
Pointwiseₙ R (suc n@(suc _)) (a , l) (b , r) = R a b , Pointwiseₙ R n l r

-- Pointwise lifting of propositional equality over n-ary products

Equalₙ : ∀ n {ls} {as : Sets n ls} (l r : Product n as) → Sets n ls
Equalₙ = Pointwiseₙ _≡_

------------------------------------------------------------------------
-- Generic Programs
------------------------------------------------------------------------

-- Once we have these type definitions, we can write generic programs
-- over them. They will typically be split into two or three definitions:

-- 1. action on the vector of n levels (if any)
-- 2. action on the corresponding vector of n Sets
-- 3. actual program, typed thank to the function defined in step 2.

-- see Relation.Binary.PropositionalEquality for congₙ and substₙ, two
-- equality-related generic programs.

------------------------------------------------------------------------
-- equivalence of Product and Product⊤

toProduct : ∀ n {ls} {as : Sets n ls} → Product⊤ n as → Product n as
toProduct 0               _        = _
toProduct 1               (v , _)  = v
toProduct (suc n@(suc _)) (v , vs) = v , toProduct n vs

toProduct⊤ : ∀ n {ls} {as : Sets n ls} → Product n as → Product⊤ n as
toProduct⊤ 0               _        = _
toProduct⊤ 1               v        = v , _
toProduct⊤ (suc n@(suc _)) (v , vs) = v , toProduct⊤ n vs

------------------------------------------------------------------------
-- (un)curry

-- We start by defining `curryₙ` and `uncurryₙ` converting back and forth
-- between `A₁ → ⋯ → Aₙ → B` and `(A₁ × ⋯ × Aₙ) → B` by induction on `n`.

curryₙ : ∀ n {ls} {as : Sets n ls} {r} {b : Set r} →
         (Product n as → b) → as ⇉ b
curryₙ 0               f = f _
curryₙ 1               f = f
curryₙ (suc n@(suc _)) f = curryₙ n ∘′ curry f

uncurryₙ : ∀ n {ls} {as : Sets n ls} {r} {b : Set r} →
           as ⇉ b → (Product n as → b)
uncurryₙ 0               f = const f
uncurryₙ 1               f = f
uncurryₙ (suc n@(suc _)) f = uncurry (uncurryₙ n ∘′ f)

-- Variants for Product⊤

curry⊤ₙ : ∀ n {ls} {as : Sets n ls} {r} {b : Set r} →
          (Product⊤ n as → b) → as ⇉ b
curry⊤ₙ zero    f = f _
curry⊤ₙ (suc n) f = curry⊤ₙ n ∘′ curry f

uncurry⊤ₙ : ∀ n {ls} {as : Sets n ls} {r} {b : Set r} →
            as ⇉ b → (Product⊤ n as → b)
uncurry⊤ₙ zero    f = const f
uncurry⊤ₙ (suc n) f = uncurry (uncurry⊤ₙ n ∘′ f)

------------------------------------------------------------------------
-- decidability

Product⊤-dec : ∀ n {ls} {as : Sets n ls} → Product⊤ n (Dec <$> as) → Dec (Product⊤ n as)
Product⊤-dec zero    _          = yes _
Product⊤-dec (suc n) (p? , ps?) = p? ×? Product⊤-dec n ps?

Product-dec : ∀ n {ls} {as : Sets n ls} → Product n (Dec <$> as) → Dec (Product n as)
Product-dec 0               _          = yes _
Product-dec 1               p?         = p?
Product-dec (suc n@(suc _)) (p? , ps?) = p? ×? Product-dec n ps?

------------------------------------------------------------------------
-- pointwise liftings

toEqualₙ : ∀ n {ls} {as : Sets n ls} {l r : Product n as} →
           l ≡ r → Product n (Equalₙ n l r)
toEqualₙ 0               eq = _
toEqualₙ 1               eq = eq
toEqualₙ (suc n@(suc _)) eq = Prod.map₂ (toEqualₙ n) (Prodₚ.,-injective eq)

fromEqualₙ : ∀ n {ls} {as : Sets n ls} {l r : Product n as} →
             Product n (Equalₙ n l r) → l ≡ r
fromEqualₙ 0               eq = refl
fromEqualₙ 1               eq = eq
fromEqualₙ (suc n@(suc _)) eq = uncurry (cong₂ _,_) (Prod.map₂ (fromEqualₙ n) eq)

------------------------------------------------------------------------
-- projection of the k-th component

-- To know at which Set level the k-th projection out of an n-ary
-- product lives, we need to extract said level, by induction on k.

Levelₙ : ∀ {n} → Levels n → Fin n → Level
Levelₙ (l , _)  zero    = l
Levelₙ (_ , ls) (suc k) = Levelₙ ls k

-- Once we have the Sets used in the product, we can extract the one we
-- are interested in, once more by induction on k.

Projₙ : ∀ {n ls} → Sets n ls → ∀ k → Set (Levelₙ ls k)
Projₙ (a , _)  zero    = a
Projₙ (_ , as) (suc k) = Projₙ as k

-- Finally, provided a Product of these sets, we can extract the k-th
-- value. `projₙ` takes both `n` and `k` explicitly because we expect
-- the user will be using a concrete `k` (potentially manufactured
-- using `Data.Fin`'s `#_`) and it will not be possible to infer `n`
-- from it.

projₙ : ∀ n {ls} {as : Sets n ls} k → Product n as → Projₙ as k
projₙ 1               zero    v        = v
projₙ (suc n@(suc _)) zero    (v , _)  = v
projₙ (suc n@(suc _)) (suc k) (_ , vs) = projₙ n k vs

------------------------------------------------------------------------
-- zip

zipWith : ∀ n {lsa lsb lsc}
          {as : Sets n lsa} {bs : Sets n lsb} {cs : Sets n lsc} →
          (∀ k → Projₙ as k → Projₙ bs k → Projₙ cs k) →
          Product n as → Product n bs → Product n cs
zipWith 0               f _        _        = _
zipWith 1               f v        w        = f zero v w
zipWith (suc n@(suc _)) f (v , vs) (w , ws) =
  f zero v w , zipWith n (λ k → f (suc k)) vs ws

------------------------------------------------------------------------
-- removal of the k-th component

Levelₙ⁻ : ∀ {n} → Levels n → Fin n → Levels (pred n)
Levelₙ⁻               (_ , ls) zero    = ls
Levelₙ⁻ {suc (suc _)} (l , ls) (suc k) = l , Levelₙ⁻ ls k

Removeₙ : ∀ {n ls} → Sets n ls → ∀ k → Sets (pred n) (Levelₙ⁻ ls k)
Removeₙ               (_ , as) zero    = as
Removeₙ {suc (suc _)} (a , as) (suc k) = a , Removeₙ as k

removeₙ : ∀ n {ls} {as : Sets n ls} k →
          Product n as → Product (pred n) (Removeₙ as k)
removeₙ (suc zero)          zero    _        = _
removeₙ (suc (suc _))       zero    (_ , vs) = vs
removeₙ (suc (suc zero))    (suc k) (v , _)  = v
removeₙ (suc (suc (suc _))) (suc k) (v , vs) = v , removeₙ _ k vs

------------------------------------------------------------------------
-- insertion of a k-th component

Levelₙ⁺ : ∀ {n} → Levels n → Fin (suc n) → Level → Levels (suc n)
Levelₙ⁺         ls       zero    l⁺ = l⁺ , ls
Levelₙ⁺ {suc _} (l , ls) (suc k) l⁺ = l , Levelₙ⁺ ls k l⁺

Insertₙ : ∀ {n ls l⁺} → Sets n ls → ∀ k (a⁺ : Set l⁺) → Sets (suc n) (Levelₙ⁺ ls k l⁺)
Insertₙ         as       zero    a⁺ = a⁺ , as
Insertₙ {suc _} (a , as) (suc k) a⁺ = a , Insertₙ as k a⁺

insertₙ : ∀ n {ls l⁺} {as : Sets n ls} {a⁺ : Set l⁺} k (v⁺ : a⁺) →
          Product n as → Product (suc n) (Insertₙ as k a⁺)
insertₙ 0               zero    v⁺ vs       = v⁺
insertₙ (suc n)         zero    v⁺ vs       = v⁺ , vs
insertₙ 1               (suc k) v⁺ vs       = vs , insertₙ 0 k v⁺ _
insertₙ (suc n@(suc _)) (suc k) v⁺ (v , vs) = v , insertₙ n k v⁺ vs

------------------------------------------------------------------------
-- update of a k-th component

Levelₙᵘ : ∀ {n} → Levels n → Fin n → Level → Levels n
Levelₙᵘ (_ , ls) zero    lᵘ = lᵘ , ls
Levelₙᵘ (l , ls) (suc k) lᵘ = l , Levelₙᵘ ls k lᵘ

Updateₙ : ∀ {n ls lᵘ} (as : Sets n ls) k (aᵘ : Set lᵘ) → Sets n (Levelₙᵘ ls k lᵘ)
Updateₙ (_ , as) zero    aᵘ = aᵘ , as
Updateₙ (a , as) (suc k) aᵘ = a , Updateₙ as k aᵘ

updateₙ : ∀ n {ls lᵘ} {as : Sets n ls} k {aᵘ : _ → Set lᵘ} (f : ∀ v → aᵘ v)
          (vs : Product n as) → Product n (Updateₙ as k (aᵘ (projₙ n k vs)))
updateₙ 1               zero    f v        = f v
updateₙ (suc (suc _))   zero    f (v , vs) = f v , vs
updateₙ (suc n@(suc _)) (suc k) f (v , vs) = v , updateₙ n k f vs

updateₙ′ : ∀ n {ls lᵘ} {as : Sets n ls} k {aᵘ : Set lᵘ} (f : Projₙ as k → aᵘ) →
           Product n as → Product n (Updateₙ as k aᵘ)
updateₙ′ n k = updateₙ n k

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.3

Allₙ = Pointwiseₙ
{-# WARNING_ON_USAGE Allₙ
"Warning: Allₙ was deprecated in v2.3. Please use Pointwiseₙ instead."
#-}
