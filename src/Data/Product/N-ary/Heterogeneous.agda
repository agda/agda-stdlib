------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous N-ary Products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.N-ary.Heterogeneous where

open import Level as L using (Level; _⊔_; Lift)
open import Agda.Builtin.Unit
open import Data.Product
open import Data.Nat.Base using (ℕ; zero; suc; pred)
open import Data.Fin.Base using (Fin; zero; suc)
open import Function

------------------------------------------------------------------------
-- Type Definition

-- We want to define n-ary products and generic n-ary operations on them
-- such as currying and uncurrying. We want users to be able to use these
-- seamlessly whenever n is concrete. In other words, we want Agda to infer
-- the sets `A₁, ⋯, Aₙ` when we write `uncurryₙ n f` where `f` has type
-- `A₁ → ⋯ → Aₙ → B`. For this to happen, we need the structure in which
-- these Sets are stored to effectively η-expand to `A₁, ⋯, Aₙ` when the
-- parameter `n` is known.
-- Hence the following definitions:

-- First, a "vector" of `n` Levels (defined by induction on n so that it
-- may be built by η-expansion and unification). Each Level will be that
-- of one of the Sets we want to take the n-ary product of.

Levels : ℕ → Set
Levels zero    = ⊤
Levels (suc n) = Level × Levels n

-- The overall product's Level will be the least upper bound of all of the
-- Levels involved.

toLevel : ∀ n → Levels n → Level
toLevel zero    _        = L.zero
toLevel (suc n) (l , ls) = l ⊔ toLevel n ls

-- Second, a "vector" of `n` Sets whose respective Levels are determined
-- by the `Levels n` input.

Sets : ∀ n (ls : Levels n) → Set (L.suc (toLevel n ls))
Sets zero    _        = Lift _ ⊤
Sets (suc n) (l , ls) = Set l × Sets n ls

-- Third, the n-ary product itself: provided n Levels and a corresponding
-- "vector" of `n` Sets, we can build a big right-nested product type packing
-- a value for each one of these Sets. We have a special case for 1 because
-- we want our `(un)curryₙ` functions to work for user-written functions and
-- they rarely are ⊤-terminated.

Product : ∀ n {ls} → Sets n ls → Set (toLevel n ls)
Product 0       _        = ⊤
Product 1       (a , _)  = a
Product (suc n) (a , as) = a × Product n as

------------------------------------------------------------------------
-- Generic Programs: (un)curry
-- see Relation.Binary.PropositionalEquality for other examples (congₙ, substₙ)

-- To be able to talk about (un)currying, we need to be able to form the
-- type `A₁ → ⋯ → Aₙ → B`. This is what `Arrows` does, by induction on `n`.

Arrows : ∀ n {r ls} → Sets n ls → Set r → Set (toLevel n ls ⊔ r)
Arrows zero    _        b = b
Arrows (suc n) (a , as) b = a → Arrows n as b

-- Finally, we can define `curryₙ` and `uncurryₙ` converting back and forth
-- between `A₁ → ⋯ → Aₙ → B` and `(A₁ × ⋯ × Aₙ) → B` by induction on `n`.

curryₙ : ∀ n {ls} {as : Sets n ls} {r} {b : Set r} →
         (Product n as → b) → Arrows n as b
curryₙ 0               f = f _
curryₙ 1               f = f
curryₙ (suc n@(suc _)) f = curryₙ n ∘′ curry f

uncurryₙ : ∀ n {ls : Levels n} {as : Sets n ls} {r} {b : Set r} →
           Arrows n as b → (Product n as → b)
uncurryₙ 0               f = const f
uncurryₙ 1               f = f
uncurryₙ (suc n@(suc _)) f = uncurry (uncurryₙ n ∘′ f)

------------------------------------------------------------------------
-- Generic Programs: projection of the k-th component

-- To know at which Set level the k-th projection out of an n-ary product
-- lives, we need to extract said level, by induction on k.

Levelₙ : ∀ {n} → Levels n → Fin n → Level
Levelₙ (l , _)  zero    = l
Levelₙ (_ , ls) (suc k) = Levelₙ ls k

-- Once we have the Sets used in the product, we can extract the one we
-- are interested in, once more by induction on k.

Projₙ : ∀ {n ls} → Sets n ls → ∀ k → Set (Levelₙ ls k)
Projₙ (a , _)  zero    = a
Projₙ (_ , as) (suc k) = Projₙ as k

-- Finally, provided a Product of these sets, we can extract the k-th value.
-- `projₙ` takes both `n` and `k` explicitly because we expect the user will
-- be using a concrete `k` (potentially manufactured using `Data.Fin`'s `#_`)
-- and it will not be possible to infer `n` from it.

projₙ : ∀ n {ls} {as : Sets n ls} k → Product n as → Projₙ as k
projₙ 1               zero    v        = v
projₙ (suc n@(suc _)) zero    (v , _)  = v
projₙ (suc n@(suc _)) (suc k) (_ , vs) = projₙ n k vs
projₙ 1 (suc ()) v

------------------------------------------------------------------------
-- Generic Programs: removal of the k-th component

Levelₙ⁻ : ∀ {n} → Levels n → Fin n → Levels (pred n)
Levelₙ⁻               (_ , ls) zero    = ls
Levelₙ⁻ {suc (suc _)} (l , ls) (suc k) = l , Levelₙ⁻ ls k
Levelₙ⁻ {1} _ (suc ())

Removeₙ : ∀ {n ls} → Sets n ls → ∀ k → Sets (pred n) (Levelₙ⁻ ls k)
Removeₙ               (_ , as) zero    = as
Removeₙ {suc (suc _)} (a , as) (suc k) = a , Removeₙ as k
Removeₙ {1} _ (suc ())

removeₙ : ∀ n {ls} {as : Sets n ls} k →
          Product n as → Product (pred n) (Removeₙ as k)
removeₙ (suc zero)          zero    _        = _
removeₙ (suc (suc _))       zero    (_ , vs) = vs
removeₙ (suc (suc zero))    (suc k) (v , _)  = v
removeₙ (suc (suc (suc _))) (suc k) (v , vs) = v , removeₙ _ k vs
removeₙ (suc zero) (suc ()) _

------------------------------------------------------------------------
-- Generic Programs: insertion of a k-th component

Levelₙ⁺ : ∀ {n} → Levels n → Fin (suc n) → Level → Levels (suc n)
Levelₙ⁺         ls       zero    l⁺ = l⁺ , ls
Levelₙ⁺ {suc _} (l , ls) (suc k) l⁺ = l , Levelₙ⁺ ls k l⁺
Levelₙ⁺ {0} _ (suc ())

Insertₙ : ∀ {n ls l⁺} → Sets n ls → ∀ k (a⁺ : Set l⁺) → Sets (suc n) (Levelₙ⁺ ls k l⁺)
Insertₙ         as       zero    a⁺ = a⁺ , as
Insertₙ {suc _} (a , as) (suc k) a⁺ = a , Insertₙ as k a⁺
Insertₙ {zero} _ (suc ()) _

insertₙ : ∀ n {ls l⁺} {as : Sets n ls} {a⁺ : Set l⁺} k (v⁺ : a⁺) →
          Product n as → Product (suc n) (Insertₙ as k a⁺)
insertₙ 0             zero    v⁺ vs       = v⁺
insertₙ (suc n)       zero    v⁺ vs       = v⁺ , vs
insertₙ 1             (suc k) v⁺ vs       = vs , insertₙ 0 k v⁺ _
insertₙ (suc (suc n)) (suc k) v⁺ (v , vs) = v , insertₙ _ k v⁺ vs
insertₙ 0 (suc ()) _ _

------------------------------------------------------------------------
-- Generic Programs: update of a k-th component

Levelₙᵘ : ∀ {n} → Levels n → Fin n → Level → Levels n
Levelₙᵘ (_ , ls) zero    lᵘ = lᵘ , ls
Levelₙᵘ (l , ls) (suc k) lᵘ = l , Levelₙᵘ ls k lᵘ

Updateₙ : ∀ {n ls lᵘ} (as : Sets n ls) k (aᵘ : Set lᵘ) → Sets n (Levelₙᵘ ls k lᵘ)
Updateₙ (_ , as) zero    aᵘ = aᵘ , as
Updateₙ (a , as) (suc k) aᵘ = a , Updateₙ as k aᵘ

updateₙ : ∀ n {ls lᵘ} {as : Sets n ls} k {aᵘ : _ → Set lᵘ} (f : ∀ v → aᵘ v)
          (vs : Product n as) → Product n (Updateₙ as k (aᵘ (projₙ n k vs)))
updateₙ 1             zero    f v        = f v
updateₙ (suc (suc _)) zero    f (v , vs) = f v , vs
updateₙ (suc (suc _)) (suc k) f (v , vs) = v , updateₙ _ k f vs
updateₙ 1 (suc ()) _ _

updateₙ′ : ∀ n {ls lᵘ} {as : Sets n ls} k {aᵘ : Set lᵘ} (f : Projₙ as k → aᵘ) →
           Product n as → Product n (Updateₙ as k aᵘ)
updateₙ′ n k = updateₙ n k

mapₙ : ∀ n {ls r lᵘ} {as : Sets n ls} {b : Set r} {aᵘ : Set lᵘ} k →
       (aᵘ → Projₙ as k) → Arrows n as b → Arrows n (Updateₙ as k aᵘ) b
mapₙ _ zero    f g = g ∘′ f
mapₙ _ (suc k) f g = mapₙ _ k f ∘′ g
