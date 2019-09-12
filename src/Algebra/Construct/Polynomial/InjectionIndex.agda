{-# OPTIONS --without-K --safe #-}

----------------------------------------------------------------------
-- Gaps
----------------------------------------------------------------------
-- Polynomials can be represented as lists of their coefficients,
-- stored in increasing powers of x:
--
--   3 + 2x² + 4x⁵ + 2x⁷
-- ≡⟨ making the missing xs explicit ⟩
--   3x⁰ + 0x¹ + 2x² + 0x³ + 0x⁴ + 4x⁵ + 0x⁶ + 2x⁷
-- ≡⟨ in list notation ⟩
--   [3,0,2,0,0,4,0,2]
--
-- This approach is wasteful with space. Instead, we will pair each
-- coefficient with the size of the preceding gap, meaning that the
-- above expression is instead written as:
--
--   [(3,0),(2,1),(4,2),(2,1)]
--
-- Which can be thought of as a representation of the expression:
--
--   x⁰ * (3 + x * x¹ * (2 + x * x² * (4 + x * x¹ * (2 + x * 0))))
--
-- To add multiple variables to a polynomial, you can *nest* them,
-- making the coefficients of the outer polynomial polynomials
-- themselves. However, this is *also* wasteful, in a similar way to
-- above: the constant polynomial, for instance, will be represented
-- as many nestings of constant polynomials around a final variable.
-- However, this approach presents a difficulty: the polynomial will
-- have the kind ℕ → Set (...). In other words, it's indexed by the
-- number of variables it contains. The gap we store, then, has to
-- be accomanied with some information about how it relates to that
-- index.
--
-- The first approach I tried was to forget about storing the gaps,
-- and instead store the number of variables in the nested coefficient,
-- along with a proof that the number was smaller than the outer. The
-- proof was _≤_ from Data.Nat:
--
-- data _≤_ : Rel ℕ 0ℓ where
--   z≤n : ∀ {n}                 → zero  ≤ n
--   s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
--
-- While this worked, this will actually give you a worse complexity
-- than the naive encoding without gaps.
--
-- For any of the binary operations, you need to be able to "line up"
-- the two arguments in terms of the gaps. For addition, for instance,
-- the argument with fewer variables should be added to the constant
-- term of the argument with more. To do this, you need to compare the
-- gaps.
--
-- To see why that's a problem, consider the following sequence of
-- nestings:
--
--   (5 ≤ 6), (4 ≤ 5), (3 ≤ 4), (1 ≤ 3), (0 ≤ 1)
--
-- The outer polynomial has 6 variables, but it has a gap to its inner
-- polynomial of 5, and so on. What we compare in this case is the
-- number of variables in the tail: like repeatedly taking the length of
-- the tail of a list, it's quadratic.
--
-- The second approach was to try and mimic the powers structure
-- (which only compared the gaps, which is linear), and store the gaps
-- in a proof like the following:
--
-- record _≤″_ (m n : ℕ) : Set where
--   constructor less-than-or-equal
--   field
--     {k}   : ℕ
--     proof : m + k ≡ n
--
-- Here, k is the size of the gap. The problem of this approach was
-- twofold: it was difficult to show that comparisons on the k
-- corresponded to comparisons on the m, and working with ≡ instead of
-- some inductive structure was messy. However, it had the advantage
-- of being erasable: both proofs of the correspondence and the
-- equality proof itself. That said, I'm not very familiar with the
-- soundness of erasure, and in particular how it interacts with axiom
-- K (which I'd managed to avoid up until this point, but started to
-- creep in).
--
-- I may have had more luck if I swapped the arguments too +:
--
-- record _≤″_ (m n : ℕ) : Set where
--   constructor less-than-or-equal
--   field
--     {k}   : ℕ
--     proof : k + m ≡ n
--
-- But I did not try it. The solution I ended up with was superior,
-- regardless:
--
-- infix 4 _≤_
-- data _≤_ (m : ℕ) : ℕ → Set where
--   m≤m : m ≤ m
--   ≤-s : ∀ {n} → (m≤n : m ≤ n) → m ≤ suc n
--
-- (This is a rewritten version of _≤′_ from Data.Nat.Base).
--
-- While this structure stores the same information as ≤, it does so
-- by induction on the *gap*. This became apparent when I realised you
-- could use it to write a comparison function which was linear in the
-- size of the gap (even though it was comparing the length of the
-- tail):

-- data Ordering : ℕ → ℕ → Set where
--   less    : ∀ {n m} → n ≤ m → Ordering n (suc m)
--   greater : ∀ {n m} → m ≤ n → Ordering (suc n) m
--   equal   : ∀ {n}           → Ordering n n

-- ≤-compare : ∀ {i j n}
--           → (i≤n : i ≤ n)
--           → (j≤n : j ≤ n)
--           → Ordering i j
-- ≤-compare m≤m m≤m = equal
-- ≤-compare m≤m (≤-s m≤n) = greater m≤n
-- ≤-compare (≤-s m≤n) m≤m = less m≤n
-- ≤-compare (≤-s i≤n) (≤-s j≤n) = ≤-compare i≤n j≤n
--
-- A few things to note here:
--
-- 1. The ≤-compare function is one of those reassuring ones for which
--    Agda can completely fill in the type for me.
-- 2. This function looks somewhat similar to the one for comparing ℕ
--    in Data.Nat, and as a result, the "matching" logic for degree
--    and number of variables began too look similar.
--
-- While this approach allowed me too write all the functions I
-- needed, I hit another roadblock when it came time to prove the
-- ring homomorphism. The first thing I realised I needed to prove was
-- basically the following:
--
--   ∀ {i j n}
--   → (i≤n : i ≤ n)
--   → (j≤n : j ≤ n)
--   → ∀ xs Ρ
--   → Σ⟦ xs ⟧ (drop-1 i≤n Ρ) ≈ Σ⟦ xs ⟧ (drop-1 j≤n Ρ)
--
-- In effect, if the inequalities are over the same numbers, then
-- they'll behave the same way when used in evaluation.
--
-- The above is really just a consequence of ≤ being irrelevant:
--
--   ∀ {i n}
--   → (x : i ≤ n)
--   → (y : i ≤ n)
--   → x ≡ y
--
-- Trying to prove this convinced me that it might not even be possible
-- without K. On top of that, I also noticed that I would need to
-- prove things like:
--
--   ∀ {i j n}
--   → (i≤j : i ≤ j)
--   → (j≤n : j ≤ n)
--   → (x : FlatPoly i)
--   → (Ρ : Vec Carrier n)
--   → ⟦ x Π (i≤j ⟨ ≤′-trans ⟩ j≤n) ⟧ Ρ ≈ ⟦ x Π i≤j ⟧ (drop j≤n Ρ)
--
-- Effectively, I needed to prove that transitivity was a
-- homomorphism.
--
-- I realised that I had not run into these difficulties with the
-- comparison function I was using for the exponent gaps: why? Well
-- that function provides a proof about its *arguments* whereas the
-- one I wrote above only provides a proof about the i and j.
--
-- data Ordering : Rel ℕ 0ℓ where
--   less    : ∀ m k → Ordering m (suc (m + k))
--   equal   : ∀ m   → Ordering m m
--   greater : ∀ m k → Ordering (suc (m + k)) m
--
-- If I tried to mimick the above as closely as possible, I would also
-- need an analogue to +: of course this was ≤′-trans, so I was going
-- to get my transitivity proof as well as everything else. The result
-- is as follows.

module Algebra.Construct.Polynomial.InjectionIndex where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat using (_≤′_; ≤′-refl; ≤′-step; _<′_) public
open import Data.Nat.Properties using (≤′-trans) public
open import Function

data InjectionOrdering {n : ℕ} : ∀ {i j}
                      → (i≤n : i ≤′ n)
                      → (j≤n : j ≤′ n)
                      → Set
                      where
  inj-lt : ∀ {i j-1}
     → (i≤j-1 : i ≤′ j-1)
     → (j≤n : suc j-1 ≤′ n)
     → InjectionOrdering (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) j≤n
  inj-gt : ∀ {i-1 j}
     → (i≤n : suc i-1 ≤′ n)
     → (j≤i-1 : j ≤′ i-1)
     → InjectionOrdering i≤n (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n)
  inj-eq : ∀ {i} → (i≤n : i ≤′ n) → InjectionOrdering i≤n i≤n

inj-compare : ∀ {i j n}
    → (x : i ≤′ n)
    → (y : j ≤′ n)
    → InjectionOrdering x y
inj-compare ≤′-refl ≤′-refl = inj-eq ≤′-refl
inj-compare ≤′-refl (≤′-step y) = inj-gt ≤′-refl y
inj-compare (≤′-step x) ≤′-refl = inj-lt x ≤′-refl
inj-compare (≤′-step x) (≤′-step y) = case inj-compare x y of
    λ { (inj-lt i≤j-1 .y) → inj-lt i≤j-1 (≤′-step y)
      ; (inj-gt .x j≤i-1) → inj-gt (≤′-step x) j≤i-1
      ; (inj-eq .x) → inj-eq (≤′-step x)
      }

open import Data.Fin as Fin using (Fin)

space : ∀ {n} → Fin n → ℕ
space f = suc (go f)
  where
  go : ∀ {n} → Fin n → ℕ
  go {suc n} Fin.zero = n
  go (Fin.suc x) = go x

Fin⇒≤ : ∀ {n} (x : Fin n) → space x ≤′ n
Fin⇒≤ Fin.zero = ≤′-refl
Fin⇒≤ (Fin.suc x) = ≤′-step (Fin⇒≤ x)
