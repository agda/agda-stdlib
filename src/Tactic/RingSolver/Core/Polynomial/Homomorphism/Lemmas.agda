------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas for use in proving the polynomial homomorphism.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Bool                                  using (Bool;true;false)
open import Data.Nat.Base as ℕ                              using (ℕ; suc; zero; compare; _≤′_; ≤′-step; ≤′-refl)
open import Data.Nat.Properties as ℕₚ                  using (≤′-trans)
open import Data.Vec.Base as Vec                            using (Vec; _∷_)
open import Data.Fin                                   using (Fin; zero; suc)
open import Data.List                                  using (_∷_; [])
open import Data.Unit using (tt)
open import Data.List.Kleene
open import Data.Product                               using (_,_; proj₁; proj₂; map₁; _×_)
open import Data.Empty                                 using (⊥-elim)
open import Data.Maybe                                 using (nothing; just)
open import Function
open import Level                                      using (lift)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Homomorphism homo hiding (_^_)
open import Tactic.RingSolver.Core.Polynomial.Reasoning to
open import Tactic.RingSolver.Core.Polynomial.Base from
open import Tactic.RingSolver.Core.Polynomial.Semantics homo

open import Algebra.Operations.Ring rawRing

------------------------------------------------------------------------
-- Power lemmas
--
-- We prove some things about our odd exponentiation operator (described
-- in Algebra.Operations.Ring.Compact) here.

-- First, that the optimised operator is the same as normal
-- exponentiation.
pow-opt : ∀ x ρ i → x *⟨ ρ ⟩^ i ≈ ρ ^ i * x
pow-opt x ρ ℕ.zero = sym (*-identityˡ x)
pow-opt x ρ (suc i) = refl

-- Some normal identities on exponentiation.
--  xⁿxᵐ = xⁿ⁺ᵐ
pow-add′ : ∀ x i j → (x ^ i +1) * (x ^ j +1) ≈ x ^ (j ℕ.+ suc i) +1
pow-add′ x i ℕ.zero = refl
pow-add′ x i (suc j) =
  begin
    x ^ i +1 * (x ^ j +1 * x)
  ≈⟨ sym (*-assoc _ _ _) ⟩
    x ^ i +1 * x ^ j +1 * x
  ≈⟨ ≪* pow-add′ x i j ⟩
    x ^ (j ℕ.+ suc i) +1 * x
  ∎

pow-add : ∀ x y i j → y ^ j +1 * x *⟨ y ⟩^ i  ≈ x *⟨ y ⟩^ (i ℕ.+ suc j)
pow-add x y ℕ.zero j = refl
pow-add x y (suc i) j = go x y i j
  where
  go : ∀ x y i j → y ^ j +1 * ((y ^ i +1) * x) ≈ y ^ (i ℕ.+ suc j) +1 * x
  go x y ℕ.zero j =  sym (*-assoc _ _ _)
  go x y (suc i) j =
    begin
      y ^ j +1 * (y ^ i +1 * y * x)
    ≈⟨ *≫ *-assoc _ y x ⟩
      y ^ j +1 * (y ^ i +1 * (y * x))
    ≈⟨ go (y * x) y i j ⟩
      y ^ (i ℕ.+ suc j) +1 * (y * x)
    ≈⟨ sym (*-assoc _ y x) ⟩
      y ^ suc (i ℕ.+ suc j) +1 * x
    ∎

-- Here we show a homomorphism on exponentiation, i.e. that using the
-- exponentiation function on polynomials and then evaluating is the same
-- as evaluating and then exponentiating.
pow-hom : ∀ {n} i
        → (xs : Coeff n +)
        → ∀ ρ ρs
        → ⅀⟦ xs ⟧ (ρ , ρs) *⟨ ρ ⟩^ i ≈ ⅀⟦ xs ⍓+ i ⟧ (ρ , ρs)
pow-hom ℕ.zero (x Δ j & xs) ρ ρs rewrite ℕₚ.+-identityʳ j = refl
pow-hom (suc i) (x ≠0 Δ j & xs) ρ ρs =
  begin
    ρ ^ i +1 * (((x , xs) ⟦∷⟧ (ρ , ρs)) *⟨ ρ ⟩^ j)
  ≈⟨ pow-add _ ρ j i ⟩
    (((x , xs) ⟦∷⟧ (ρ , ρs)) *⟨ ρ ⟩^ (j ℕ.+ suc i))
  ∎

-- Proving a congruence (we don't get this for free because we're using
-- setoids).
pow-mul-cong : ∀ {x y} → x ≈ y → ∀ ρ i → x *⟨ ρ ⟩^ i ≈ y *⟨ ρ ⟩^ i
pow-mul-cong x≈y ρ ℕ.zero = x≈y
pow-mul-cong x≈y ρ (suc i₁) = *≫ x≈y

-- The identity:
--  (xy)ⁿ = xⁿyⁿ
pow-distrib-+1 : ∀ x y i → (x * y) ^ i +1 ≈ x ^ i +1 * y ^ i +1
pow-distrib-+1 x y ℕ.zero = refl
pow-distrib-+1 x y (suc i) =
  begin
    (x * y) ^ i +1 * (x * y)
  ≈⟨ ≪* pow-distrib-+1 x y i ⟩
    (x ^ i +1 * y ^ i +1) * (x * y)
  ≈⟨ *-assoc _ _ _ ⟨ trans ⟩ (*≫ (sym (*-assoc _ _ _) ⟨ trans ⟩ (≪* *-comm _ _))) ⟩
    x ^ i +1 * (x * y ^ i +1 * y)
  ≈⟨ (*≫ *-assoc _ _ _) ⟨ trans ⟩ sym (*-assoc _ _ _) ⟩
    (x ^ i +1 * x) * (y ^ i +1 * y)
  ∎

pow-distrib : ∀ x y i → (x * y) ^ i ≈ x ^ i * y ^ i
pow-distrib x y ℕ.zero = sym (*-identityˡ _)
pow-distrib x y (suc i) = pow-distrib-+1 x y i

-- This proves the identity:
--   (xⁿ)ᵐ = xⁿᵐ
-- The reason it looks different is because we're using the special exponentiation
-- operator.
pow-mult-+1 : ∀ x i j → (x ^ i +1) ^ j +1 ≈ x ^ (i ℕ.+ j ℕ.* suc i) +1
pow-mult-+1 x i ℕ.zero rewrite ℕₚ.+-identityʳ i = refl
pow-mult-+1 x i (suc j) =
  begin
    (x ^ i +1) ^ j +1 * (x ^ i +1)
  ≈⟨ ≪* pow-mult-+1 x i j ⟩
    (x ^ (i ℕ.+ j ℕ.* suc i) +1) * (x ^ i +1)
  ≈⟨ pow-add′ x _ i ⟩
    x ^ (i ℕ.+ suc (i ℕ.+ j ℕ.* suc i)) +1
  ∎

pow-cong-+1 : ∀ {x y} i → x ≈ y → x ^ i +1 ≈ y ^ i +1
pow-cong-+1 ℕ.zero x≈y = x≈y
pow-cong-+1 (suc i) x≈y = pow-cong-+1 i x≈y ⟨ *-cong ⟩ x≈y

pow-cong : ∀ {x y} i → x ≈ y → x ^ i ≈ y ^ i
pow-cong ℕ.zero x≈y = refl
pow-cong (suc i) x≈y = pow-cong-+1 i x≈y

-- Demonstrating that the proof of zeroness is correct.
zero-hom : ∀ {n} (p : Poly n) → Zero p → (ρs : Vec Carrier n) → 0# ≈ ⟦ p ⟧ ρs
zero-hom (Κ x  ⊐ i≤n) p≡0 ρs = Zero-C⟶Zero-R x p≡0

--   x¹⁺ⁿ = xxⁿ
pow-suc : ∀ x i → x ^ suc i ≈ x * x ^ i
pow-suc x ℕ.zero  = sym (*-identityʳ _)
pow-suc x (suc i) = *-comm _ _

--   x¹⁺ⁿ = xⁿx
pow-sucʳ : ∀ x i → x ^ suc i ≈ x ^ i * x
pow-sucʳ x ℕ.zero  = sym (*-identityˡ _)
pow-sucʳ x (suc i) = refl

-- In the proper evaluation function, we avoid ever inserting an unnecessary 0#
-- like we do here. However, it is easier to prove with the form that does insert
-- 0#. So we write one here, and then prove that it's equivalent to the one that
-- adds a 0#.
⅀?⟦_⟧ : ∀ {n} (xs : Coeff n *) → Carrier × Vec Carrier n → Carrier
⅀?⟦ []  ⟧ _ = 0#
⅀?⟦ ∹ x ⟧   = ⅀⟦ x ⟧

_⟦∷⟧?_ : ∀ {n} (x : Poly n × Coeff n *) → Carrier × Vec Carrier n → Carrier
(x , xs) ⟦∷⟧? (ρ , ρs) = ρ * ⅀?⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs

⅀?-hom : ∀ {n} (xs : Coeff n +) → ∀ ρ → ⅀?⟦ ∹ xs ⟧ ρ ≈ ⅀⟦ xs ⟧ ρ
⅀?-hom _ _ = refl

⟦∷⟧?-hom : ∀ {n} (x : Poly n) → ∀ xs ρ ρs → (x , xs) ⟦∷⟧? (ρ , ρs) ≈ (x , xs) ⟦∷⟧ (ρ , ρs)
⟦∷⟧?-hom x (∹ xs ) ρ ρs = refl
⟦∷⟧?-hom x [] ρ ρs =  (≪+ zeroʳ _) ⟨ trans ⟩ +-identityˡ _

pow′-hom : ∀ {n} i (xs : Coeff n *) → ∀ ρ ρs → ((⅀?⟦ xs ⟧ (ρ , ρs)) *⟨ ρ ⟩^ i) ≈ (⅀?⟦ xs ⍓* i ⟧ (ρ , ρs))
pow′-hom i (∹ xs ) ρ ρs = pow-hom i xs ρ ρs
pow′-hom zero [] ρ ρs = refl
pow′-hom (suc i) [] ρ ρs = zeroʳ _

-- Here, we show that the normalising cons is correct.
-- This lets us prove with respect to the non-normalising form, especially
-- when we're using the folds.
∷↓-hom-0 : ∀ {n} (x : Poly n) → ∀ xs ρ ρs → ⅀?⟦ x Δ 0 ∷↓ xs ⟧ (ρ , ρs) ≈ (x , xs) ⟦∷⟧ (ρ , ρs)
∷↓-hom-0 x xs      ρ ρs with zero? x
∷↓-hom-0 x xs      ρ ρs | no ¬p = refl
∷↓-hom-0 x []      ρ ρs | yes p = zero-hom x p ρs
∷↓-hom-0 x (∹ xs ) ρ ρs | yes p =
  begin
    ⅀⟦ xs ⍓+ 1 ⟧ (ρ , ρs)
  ≈⟨ sym (pow-hom 1 xs ρ ρs) ⟩
    ρ * ⅀⟦ xs ⟧ (ρ , ρs)
  ≈⟨ sym (+-identityʳ _) ⟨ trans ⟩ (+≫ zero-hom x p ρs) ⟩
    ρ * ⅀⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs
  ∎

∷↓-hom-s : ∀ {n} (x : Poly n) → ∀ i xs ρ ρs → ⅀?⟦ x Δ suc i ∷↓ xs ⟧ (ρ , ρs) ≈ (ρ ^ i +1) * (x , xs) ⟦∷⟧ (ρ , ρs)
∷↓-hom-s x i xs ρ ρs with zero? x
∷↓-hom-s x i xs ρ ρs | no ¬p = refl
∷↓-hom-s x i [] ρ ρs | yes p = sym ((*≫ sym (zero-hom x p ρs)) ⟨ trans ⟩ zeroʳ _)
∷↓-hom-s x i (∹ xs ) ρ ρs | yes p =
  begin
    ⅀⟦ xs ⍓+ (suc (suc i)) ⟧ (ρ , ρs)
  ≈⟨ sym (pow-hom (suc (suc i)) xs ρ ρs) ⟩
    (ρ ^ suc i +1) * ⅀⟦ xs ⟧ (ρ , ρs)
  ≈⟨ *-assoc _ _ _ ⟩
    (ρ ^ i +1) * (ρ * ⅀⟦ xs ⟧ (ρ , ρs))
  ≈⟨ *≫ (sym (+-identityʳ _) ⟨ trans ⟩ (+≫ zero-hom x p ρs)) ⟩
    ρ ^ i +1 * (ρ * ⅀⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs)
  ∎

∷↓-hom : ∀ {n}
       → (x : Poly n)
       → ∀ i xs ρ ρs
       → ⅀?⟦ x Δ i ∷↓ xs ⟧ (ρ , ρs) ≈ ρ ^ i * ((x , xs) ⟦∷⟧ (ρ , ρs))
∷↓-hom x ℕ.zero  xs ρ ρs = ∷↓-hom-0 x xs ρ ρs ⟨ trans ⟩ sym (*-identityˡ _)
∷↓-hom x (suc i) xs ρ ρs = ∷↓-hom-s x i xs ρ ρs

⟦∷⟧-hom : ∀ {n}
       → (x : Poly n)
       → (xs : Coeff n *)
       → ∀ ρ ρs → (x , xs) ⟦∷⟧ (ρ , ρs) ≈ ρ * ⅀?⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs
⟦∷⟧-hom x []     ρ ρs = sym ((≪+ zeroʳ _) ⟨ trans ⟩ +-identityˡ _)
⟦∷⟧-hom x (∹ xs) ρ ρs = refl

-- This proves that injecting a polynomial into more variables is correct.
-- Basically, we show that if a polynomial doesn't care about the first few
-- variables, we can drop them from the input vector.
⅀-⊐↑-hom : ∀ {i n m}
         → (xs : Coeff i +)
         → (si≤n : suc i ≤′ n)
         → (sn≤m : suc n ≤′ m)
         → ∀ ρ
         → ⅀⟦ xs ⟧ (drop-1 (≤′-step si≤n ⟨ ≤′-trans ⟩ sn≤m) ρ)
         ≈ ⅀⟦ xs ⟧ (drop-1 si≤n (proj₂ (drop-1 sn≤m ρ)))
⅀-⊐↑-hom xs si≤n ≤′-refl        (_ ∷ _) = refl
⅀-⊐↑-hom xs si≤n (≤′-step sn≤m) (_ ∷ ρ) = ⅀-⊐↑-hom xs si≤n sn≤m ρ

⊐↑-hom : ∀ {n m}
       → (x : Poly n)
       → (sn≤m : suc n ≤′ m)
       → ∀ ρ
       → ⟦ x ⊐↑ sn≤m ⟧ ρ ≈ ⟦ x ⟧ (proj₂ (drop-1 sn≤m ρ))
⊐↑-hom (Κ x  ⊐ i≤sn) _ _ = refl
⊐↑-hom (⅀ xs ⊐ i≤sn) = ⅀-⊐↑-hom xs i≤sn

trans-join-coeffs-hom : ∀ {i j-1 n}
                      → (i≤j-1 : suc i ≤′ j-1)
                      → (j≤n   : suc j-1 ≤′ n)
                      → (xs : Coeff i +)
                      → ∀ ρ
                      → ⅀⟦ xs ⟧ (drop-1 i≤j-1 (proj₂ (drop-1 j≤n ρ))) ≈ ⅀⟦ xs ⟧ (drop-1 (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) ρ)
trans-join-coeffs-hom i<j-1 ≤′-refl       xs (_ ∷ _) = refl
trans-join-coeffs-hom i<j-1 (≤′-step j<n) xs (_ ∷ ρ) = trans-join-coeffs-hom i<j-1 j<n xs ρ

trans-join-hom : ∀ {i j-1 n}
      → (i≤j-1 : i ≤′ j-1)
      → (j≤n   : suc j-1 ≤′ n)
      → (x : FlatPoly i)
      → ∀ ρ
      → ⟦ x ⊐ i≤j-1 ⟧ (proj₂ (drop-1 j≤n ρ)) ≈ ⟦ x ⊐ (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) ⟧ ρ
trans-join-hom i≤j-1 j≤n (Κ x) _ = refl
trans-join-hom i≤j-1 j≤n (⅀ x) = trans-join-coeffs-hom i≤j-1 j≤n x

⊐↓-hom : ∀ {n m}
       → (xs : Coeff n *)
       → (sn≤m : suc n ≤′ m)
       → ∀ ρ
       → ⟦ xs ⊐↓ sn≤m ⟧ ρ ≈ ⅀?⟦ xs ⟧ (drop-1 sn≤m ρ)
⊐↓-hom []                       sn≤m _ = 0-homo
⊐↓-hom (∹ x₁   Δ zero  & ∹ xs) sn≤m _ = refl
⊐↓-hom (∹ x    Δ suc j & xs )      sn≤m _ = refl
⊐↓-hom (∹ _≠0 x {x≠0} Δ zero  & []) sn≤m ρs =
  let (ρ , ρs′) = drop-1 sn≤m ρs
  in
  begin
    ⟦ x ⊐↑ sn≤m ⟧ ρs
  ≈⟨ ⊐↑-hom x sn≤m ρs ⟩
    ⟦ x ⟧ ρs′
  ∎

drop-1⇒lookup : ∀ {n} (i : Fin n) (ρs : Vec Carrier n) →
                proj₁ (drop-1 (space≤′n i) ρs) ≡ Vec.lookup ρs i
drop-1⇒lookup zero    (ρ ∷ ρs) = ≡.refl
drop-1⇒lookup (suc i) (ρ ∷ ρs) = drop-1⇒lookup i ρs

-- The fold: this function saves us hundreds of lines of proofs in the rest of the
-- homomorphism proof.
-- Many of the functions on polynomials are defined using para: this function allows
-- us to prove properties of those functions (in a foldr-fusion style) *ignoring*
-- optimisations we have made to the polynomial structure.
poly-foldR : ∀ {n} ρ ρs
        → ([f] : Fold n)
        → (f : Carrier → Carrier)
        → (∀ {x y} → x ≈ y → f x ≈ f y)
        → (∀ x y → x * f y ≈ f (x * y))
        → (∀ y {ys} zs → ⅀?⟦ ys ⟧ (ρ , ρs) ≈ f (⅀?⟦ zs ⟧ (ρ , ρs)) → [f] (y , ys) ⟦∷⟧? (ρ , ρs) ≈ f ((y , zs) ⟦∷⟧? (ρ , ρs)) )
        → (f 0# ≈ 0#)
        → ∀ xs
        → ⅀?⟦ para [f] xs ⟧ (ρ , ρs) ≈ f (⅀⟦ xs ⟧ (ρ , ρs))
poly-foldR ρ ρs f e cng dist step base (x ≠0 Δ suc i & []) =
  let y,ys = f (x , [])
      y = proj₁ y,ys
      ys = proj₂ y,ys
  in
  begin
    ⅀?⟦ y Δ suc i ∷↓ ys ⟧ (ρ , ρs)
  ≈⟨ ∷↓-hom-s y i ys ρ ρs ⟩
    (ρ ^ i +1) * ((y , ys) ⟦∷⟧ (ρ , ρs))
  ≈˘⟨ *≫ ⟦∷⟧?-hom y ys ρ ρs ⟩
    (ρ ^ i +1) * ((y , ys) ⟦∷⟧? (ρ , ρs))
  ≈⟨ *≫ step x [] (sym base) ⟩
    (ρ ^ i +1) * e ((x , []) ⟦∷⟧? (ρ , ρs))
  ≈⟨ *≫ cng (⟦∷⟧?-hom x [] ρ ρs) ⟩
    (ρ ^ i +1) * e ((x , []) ⟦∷⟧ (ρ , ρs))
  ≈⟨ dist _ _   ⟩
    e (ρ ^ i +1 * ((x , []) ⟦∷⟧ (ρ , ρs)))
  ∎
poly-foldR ρ ρs f e cng dist step base (x ≠0 Δ suc i & ∹ xs) =
  let ys = para f xs
      y,zs = f (x , ys)
      y = proj₁ y,zs
      zs = proj₂ y,zs
  in
  begin
    ⅀?⟦ y Δ suc i ∷↓ zs ⟧ (ρ , ρs)
  ≈⟨ ∷↓-hom-s y i zs ρ ρs ⟩
    (ρ ^ i +1) * ((y , zs) ⟦∷⟧ (ρ , ρs))
  ≈˘⟨ *≫ ⟦∷⟧?-hom y zs ρ ρs ⟩
    (ρ ^ i +1) * ((y , zs) ⟦∷⟧? (ρ , ρs))
  ≈⟨ *≫ step x (∹ xs) (poly-foldR ρ ρs f e cng dist step base xs) ⟩
    (ρ ^ i +1) * e ((x , (∹ xs )) ⟦∷⟧? (ρ , ρs))
  ≈⟨ *≫ cng (⟦∷⟧?-hom x (∹ xs ) ρ ρs) ⟩
    (ρ ^ i +1) * e ((x , (∹ xs )) ⟦∷⟧ (ρ , ρs))
  ≈⟨ dist _ _   ⟩
    e (ρ ^ i +1 * ((x , (∹ xs )) ⟦∷⟧ (ρ , ρs)))
  ∎
poly-foldR ρ ρs f e cng dist step base (x ≠0 Δ ℕ.zero & []) =
  let y,zs = f (x , [])
      y = proj₁ y,zs
      zs = proj₂ y,zs
  in
  begin
    ⅀?⟦ y Δ ℕ.zero ∷↓ zs ⟧ (ρ , ρs)
  ≈⟨ ∷↓-hom-0 y zs ρ ρs ⟩
    ((y , zs) ⟦∷⟧ (ρ , ρs))
  ≈˘⟨ ⟦∷⟧?-hom y zs ρ ρs ⟩
    ((y , zs) ⟦∷⟧? (ρ , ρs))
  ≈⟨ step x [] (sym base) ⟩
    e ((x , []) ⟦∷⟧? (ρ , ρs))
  ≈⟨ cng (⟦∷⟧?-hom x [] ρ ρs) ⟩
    e ((x , []) ⟦∷⟧ (ρ , ρs))
  ∎
poly-foldR ρ ρs f e cng dist step base (x ≠0 Δ ℕ.zero & (∹ xs )) =
  let ys = para f xs
      y,zs = f (x , ys)
      y = proj₁ y,zs
      zs = proj₂ y,zs
  in
  begin
    ⅀?⟦ y Δ ℕ.zero ∷↓ zs ⟧ (ρ , ρs)
  ≈⟨ ∷↓-hom-0 y zs ρ ρs ⟩
    ((y , zs) ⟦∷⟧ (ρ , ρs))
  ≈˘⟨ ⟦∷⟧?-hom y zs ρ ρs ⟩
    ((y , zs) ⟦∷⟧? (ρ , ρs))
  ≈⟨ step x (∹ xs ) (poly-foldR ρ ρs f e cng dist step base xs) ⟩
    e ((x , (∹ xs )) ⟦∷⟧ (ρ , ρs))
  ≈⟨ cng (⟦∷⟧?-hom x (∹ xs ) ρ ρs) ⟩
    e ((x , (∹ xs )) ⟦∷⟧ (ρ , ρs))
  ∎

poly-mapR : ∀ {n} ρ ρs
          → ([f] : Poly n → Poly n)
          → (f : Carrier → Carrier)
          → (∀ {x y} → x ≈ y → f x ≈ f y)
          → (∀ x y → x * f y ≈ f (x * y))
          → (∀ x y → f (x + y) ≈ f x + f y)
          → (∀ y → ⟦ [f] y ⟧ ρs ≈ f (⟦ y ⟧ ρs) )
          → (f 0# ≈ 0#)
          → ∀ xs
          → ⅀?⟦ poly-map [f] xs ⟧ (ρ , ρs) ≈ f (⅀⟦ xs ⟧ (ρ , ρs))
poly-mapR ρ ρs [f] f cng *-dist +-dist step′ base xs = poly-foldR ρ ρs (map₁ [f]) f cng *-dist step base xs
  where
  step : ∀ y {ys} zs → ⅀?⟦ ys ⟧ (ρ , ρs) ≈ f (⅀?⟦ zs ⟧ (ρ , ρs)) →(map₁ [f] (y , ys) ⟦∷⟧? (ρ , ρs)) ≈ f ((y , zs) ⟦∷⟧? (ρ , ρs))
  step y {ys} zs ys≋zs =
    begin
      map₁ [f] (y , ys) ⟦∷⟧? (ρ , ρs)
    ≡⟨⟩
      ρ * ⅀?⟦ ys ⟧ (ρ , ρs) + ⟦ [f] y ⟧ ρs
    ≈⟨ ((*≫ ys≋zs) ⟨ trans ⟩ *-dist ρ _) ⟨ +-cong ⟩ step′ y ⟩
      f (ρ * ⅀?⟦ zs ⟧ (ρ , ρs)) + f (⟦ y ⟧ ρs)
    ≈⟨ sym (+-dist _ _) ⟩
      f ((y , zs) ⟦∷⟧? (ρ , ρs))
    ∎
