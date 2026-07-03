------------------------------------------------------------------------
-- The Agda standard library
--
-- Levenshtein distance: the Dist relation and its properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Silence user warnings because we import an internal module
{-# OPTIONS --warning=noUserWarning #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Distance.Levenshtein.Dist.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

open import Data.Nat.Base using (ℕ; suc; _+_; _≤_; z≤n; s≤s; _<ᵇ_; _⊓′_; _⊓_)
open import Data.Nat.ListAction using (minimum)
open import Data.Nat.ListAction.Properties using (minimum-selective; minimum-≤)

open import Data.Nat.Properties
  using (≤-antisym; ≤-trans; module ≤-Reasoning; +-comm; n≤1+n; m⊓n≤m; ⊓≡⊓′; m⊓n≤n)
open import Data.Product.Base using (∃; _,_)

open import Level using (Level; _⊔_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Data.List.Relation.Binary.Distance.Levenshtein.Edit.Setoid S as Edit
  using (Edit; done; delL; delR; skip; same; swap)

open import Data.List.Relation.Binary.Distance.Levenshtein.Core
  using (Unique; Triangle)

private module S = Setoid S
open S
  renaming (Carrier to A)
  using (_≈_)

private
  variable
    x y : A
    xs ys zs : List A
    k l m : ℕ

------------------------------------------------------------------------
-- We saw in Data.List.Relation.Binary.Distance.Levenshtein.Edit
-- that Edit lacks some properties we expect from a distance.
-- That is due to the fact it is not enforced to be minimal.
--
-- We can define Dist as the minimal Edit and this time the relation
-- will be well behaved.

record Dist (xs ys : List A) (cost : ℕ) : Set (c ⊔ ℓ) where
  constructor _,_
  field
    edit : Edit xs ys cost
    minimal : ∀ cost' → Edit xs ys cost' → cost ≤ cost'

  dist : ℕ
  dist = cost

  source : List A
  source = xs

  target : List A
  target = ys

open Dist public

reflexive : Dist xs xs 0
reflexive .edit = Edit.reflexive
reflexive .minimal = λ _ _ → z≤n

symmetric : Dist xs ys k → Dist ys xs k
symmetric (d , m) .edit = Edit.symmetric d
symmetric (d , m) .minimal = λ c d′ → m c (Edit.symmetric d′)

-- The relation is indeed unique
unique : Unique {A = List A} Dist
unique _ _ _ _ (dk , mk) (dl , ml) = ≤-antisym (mk _ dl) (ml _ dk)

-- And it respects the triangle inequality
triangle : Triangle {A = List A} Dist
triangle _ _ _ _ _ _ (dlm , _) (dmr , _) (dlr , mlr)
  = let (m , dlr′ , m≤) = Edit.compose dlm dmr in
  ≤-trans (mlr m dlr′) m≤

------------------------------------------------------------------------
-- Known distances

-- Our edits to the empty list were already minimal

dist-[]ˡ : Dist [] ys (length ys)
dist-[]ˡ .edit = Edit.edit-[]ˡ
dist-[]ˡ .minimal cost' done        = z≤n
dist-[]ˡ .minimal cost' (delR edit) = s≤s (dist-[]ˡ .minimal _ edit)

dist-[]ʳ : Dist xs [] (length xs)
dist-[]ʳ = symmetric dist-[]ˡ

-- From Dist's minimality we can get lower bounds on bigger edits

delR-invert : ∀ {c} → Dist xs ys k → Edit xs (x ∷ ys) c → k ≤ suc c
delR-invert {xs = xs} {ys = ys} {k = k}  {x = x} {c = c} dxx ec =
  let e1 : Edit (x ∷ ys) ys 1
      e1 = delL Edit.reflexive in
  let (kc , ekc , kc≤c+1) = Edit.compose ec e1 in
  let open ≤-Reasoning in begin
  k     ≤⟨ dxx .minimal kc ekc ⟩
  kc    ≤⟨ kc≤c+1 ⟩
  c + 1 ≡⟨ +-comm c 1 ⟩
  1 + c ∎

delL-invert : ∀ {c} → Dist xs ys k → Edit (x ∷ xs) ys c → k ≤ 1 + c
delL-invert dxx ec = delR-invert (symmetric dxx) (Edit.symmetric ec)

-- Provided that we know the distances between
-- 1. xs and ys
-- 2. xs and (y ∷ ys)
-- 3. (x ∷ xs) and ys
-- then we can compute the distance between (x ∷ xs) and (y ∷ ys)

module Step
  ((k , dxy) : ∃ (Dist      xs       ys))
  ((l , dx)  : ∃ (Dist      xs  (y ∷ ys)))
  ((m , dy)  : ∃ (Dist (x ∷ xs)      ys))
  where


  private
    min : ℕ
    min = minimum k (l ∷ m ∷ [])

    min3 : min ∈ (k ∷ l ∷ m ∷ [])
    min3 = minimum-selective k (l ∷ m ∷ [])

    pattern first eq = here eq
    pattern second eq = there (here eq)
    pattern third eq = there (there (here eq))

    min3-≤ : ∀ {x} → x ∈ (k ∷ l ∷ m ∷ []) → min ≤ x
    min3-≤ = minimum-≤ k (l ∷ m ∷ [])


  costStep : (x≈?y : Dec (x ≈ y)) → ℕ
  costStep (yes _) = k
  costStep (no _) = 1 + min

  editStep : (x≈?y : Dec (x ≈ y)) → Edit (x ∷ xs) (y ∷ ys) (costStep x≈?y)
  editStep (yes x≈y) = skip x≈y (edit dxy)
  editStep (no _) with min3
  ... | first eq  = Edit.cast (cong suc (sym eq)) (swap (edit dxy))
  ... | second eq = Edit.cast (cong suc (sym eq)) (delL (edit dx))
  ... | third eq  = Edit.cast (cong suc (sym eq)) (delR (edit dy))

  open ≤-Reasoning

  miniStep : (x≈?y : Dec (x ≈ y)) → ∀ c → Edit (x ∷ xs) (y ∷ ys) c → costStep x≈?y ≤ c
  miniStep x≈?y@(yes x≈y) c (delL edit) = delR-invert dxy edit
  miniStep x≈?y@(yes x≈y) c (delR edit) = delL-invert dxy edit
  miniStep x≈?y@(yes x≈y) c (skip r edit) = dxy .minimal c edit
  miniStep x≈?y@(yes x≈y) (.suc c) (swap edit) = begin
    costStep x≈?y ≤⟨ dxy .minimal c edit ⟩
    c             ≤⟨ n≤1+n c ⟩
    suc c         ∎
  miniStep (no x≉y) c (skip x≈y x) = contradiction x≈y x≉y
  miniStep x≈?y@(no x≉y) c (delL edit) = begin
    costStep x≈?y ≤⟨ s≤s (min3-≤ (second refl)) ⟩
    1 + l         ≤⟨ s≤s (dx .minimal _ edit) ⟩
    c             ∎
  miniStep x≈?y@(no x≉y) c (delR edit) = begin
    costStep x≈?y ≤⟨ s≤s (min3-≤ (third refl)) ⟩
    1 + m         ≤⟨ s≤s (dy .minimal _ edit) ⟩
    c             ∎
  miniStep x≈?y@(no x≉y) c (swap edit) = begin
    costStep x≈?y ≤⟨ s≤s (min3-≤ (first refl)) ⟩
    suc k         ≤⟨ s≤s (dxy .minimal _ edit) ⟩
    c             ∎

  step : Dec (x ≈ y) → ∃ (Dist (x ∷ xs) (y ∷ ys))
  step x≈?y = costStep x≈?y , (editStep x≈?y , miniStep x≈?y)

open Step using (step) public
