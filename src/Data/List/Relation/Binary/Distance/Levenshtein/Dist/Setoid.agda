------------------------------------------------------------------------
-- The Agda standard library
--
-- Levenshtein distance: the Dist relation and its properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Distance.Levenshtein.Dist.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (ℕ; suc; _+_; _≤_; z≤n; s≤s; _<ᵇ_; _⊓′_; _⊓_)
open import Data.Nat.Properties
  using (≤-antisym; ≤-trans; module ≤-Reasoning; +-comm; n≤1+n; m⊓n≤m; ⊓≡⊓′; m⊓n≤n)
open import Data.Product.Base using (∃; _,_)

open import Level using (Level; _⊔_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Data.List.Relation.Binary.Distance.Levenshtein.Edit.Setoid S as Edit
  using (Edit; done; delL; delR; skip; same; swap; Unique; Triangle)

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
    mini : ∀ cost' → Edit xs ys cost' → cost ≤ cost'
open Dist public

dist : Dist xs ys k → ℕ
dist {k = k} _ = k

reflexive : Dist xs xs 0
edit reflexive = Edit.reflexive
mini reflexive = λ _ _ → z≤n

symmetric : Dist xs ys k → Dist ys xs k
edit (symmetric (d , m)) = Edit.symmetric d
mini (symmetric (d , m)) = λ c d′ → m c (Edit.symmetric d′)

-- The relation is indeed unique
unique : Unique {A = List A} Dist
unique _ _ _ _ (dk , mk) (dl , ml) = ≤-antisym (mk _ dl) (ml _ dk)

-- And it respects the triangle inequality
triangle : Triangle {A = List A} Dist
triangle _ _ _ _ _ _ (dlm , _) (dmr , _) (dlr , mlr)
  = let (m , dlr′ , m≤) = Edit.compose dlm dmr in
  ≤-trans (mlr m dlr′) m≤


-- This should surely go somewhere else

data Min3 (k l m : ℕ) : Set where
  first  : k ⊓′ l ⊓′ m ≡ k → Min3 k l m
  second : k ⊓′ l ⊓′ m ≡ l → Min3 k l m
  third  : k ⊓′ l ⊓′ m ≡ m → Min3 k l m

min3 : (k l m : ℕ) → Min3 k l m
min3 k l m with first {k} {l} {m} | second {k} {l} {m} | third {k} {l} {m}
... | f | s | t with k <ᵇ l
min3 k l m | f | s | t | false with l <ᵇ m
... | true  = s refl
... | false = t refl
min3 k l m | f | s | t | true with k <ᵇ m
... | true = f refl
... | false = t refl

m⊓′n⊓′o≤m : ∀ m n o → m ⊓′ n ⊓′ o ≤ m
m⊓′n⊓′o≤m m n o = begin
  m ⊓′ n ⊓′ o ≡⟨ ⊓≡⊓′ (m ⊓′ n) o ⟨
  m ⊓′ n ⊓ o  ≤⟨ m⊓n≤m (m ⊓′ n) o ⟩
  m ⊓′ n      ≡⟨ ⊓≡⊓′ m n ⟨
  m ⊓ n       ≤⟨ m⊓n≤m m n ⟩
  m           ∎
  where open ≤-Reasoning

m⊓′n⊓′o≤n : ∀ m n o → m ⊓′ n ⊓′ o ≤ n
m⊓′n⊓′o≤n m n o = begin
  m ⊓′ n ⊓′ o ≡⟨ ⊓≡⊓′ (m ⊓′ n) o ⟨
  m ⊓′ n ⊓ o  ≤⟨ m⊓n≤m (m ⊓′ n) o ⟩
  m ⊓′ n      ≡⟨ ⊓≡⊓′ m n ⟨
  m ⊓ n       ≤⟨ m⊓n≤n m n ⟩
  n           ∎
  where open ≤-Reasoning

m⊓′n⊓′o≤o : ∀ m n o → m ⊓′ n ⊓′ o ≤ o
m⊓′n⊓′o≤o m n o = begin
  m ⊓′ n ⊓′ o ≡⟨ ⊓≡⊓′ (m ⊓′ n) o ⟨
  m ⊓′ n ⊓ o  ≤⟨ m⊓n≤n (m ⊓′ n) o ⟩
  o           ∎
  where open ≤-Reasoning


------------------------------------------------------------------------
-- Known distances

-- Our edits to the empty list were already minimal

dist-[]ˡ : Dist [] ys (length ys)
edit dist-[]ˡ = Edit.edit-[]ˡ
mini dist-[]ˡ cost' done        = z≤n
mini dist-[]ˡ cost' (delR edit) = s≤s (mini dist-[]ˡ _ edit)

dist-[]ʳ : Dist xs [] (length xs)
dist-[]ʳ = symmetric dist-[]ˡ

-- From Dist's minimality we can get lower bounds on bigger edits

delR-invert : ∀ {c} → Dist xs ys k → Edit xs (x ∷ ys) c → k ≤ suc c
delR-invert {xs = xs} {ys = ys} {k = k}  {x = x} {c = c} dxx ec =
  let e1 : Edit (x ∷ ys) ys 1
      e1 = delL Edit.reflexive in
  let (kc , ekc , kc≤c+1) = Edit.compose ec e1 in
  let open ≤-Reasoning in begin
  k     ≤⟨ mini dxx kc ekc ⟩
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

  costStep : (x≈?y : Dec (x ≈ y)) → ℕ
  costStep (yes _) = k
  costStep (no _) = 1 + (dist dxy ⊓′ dist dx ⊓′ dist dy)

  editStep : (x≈?y : Dec (x ≈ y)) → Edit (x ∷ xs) (y ∷ ys) (costStep x≈?y)
  editStep (yes x≈y) = skip x≈y (edit dxy)
  editStep (no _) with min3 (dist dxy) (dist dx) (dist dy)
  ... | first eq  = Edit.cast (cong suc (sym eq)) (swap (edit dxy))
  ... | second eq = Edit.cast (cong suc (sym eq)) (delL (edit dx))
  ... | third  eq = Edit.cast (cong suc (sym eq)) (delR (edit dy))

  open ≤-Reasoning

  miniStep : (x≈?y : Dec (x ≈ y)) → ∀ c → Edit (x ∷ xs) (y ∷ ys) c → costStep x≈?y ≤ c
  miniStep x≈?y@(yes x≈y) c (delL edit) = delR-invert dxy edit
  miniStep x≈?y@(yes x≈y) c (delR edit) = delL-invert dxy edit
  miniStep x≈?y@(yes x≈y) c (skip r edit) = mini dxy c edit
  miniStep x≈?y@(yes x≈y) (.suc c) (swap edit) = begin
    costStep x≈?y ≤⟨ mini dxy c edit ⟩
    c             ≤⟨ n≤1+n c ⟩
    suc c         ∎
  miniStep (no x≉y) c (skip x≈y x) = contradiction x≈y x≉y
  miniStep x≈?y@(no x≉y) c (delL edit) = begin
    costStep x≈?y ≤⟨ s≤s (m⊓′n⊓′o≤n k l m) ⟩
    1 + l         ≤⟨ s≤s (mini dx _ edit) ⟩
    c             ∎
  miniStep x≈?y@(no x≉y) c (delR edit) = begin
    costStep x≈?y ≤⟨ s≤s (m⊓′n⊓′o≤o k l m) ⟩
    1 + m         ≤⟨ s≤s (mini dy _ edit) ⟩
    c             ∎
  miniStep x≈?y@(no x≉y) c (swap edit) = begin
    costStep x≈?y ≤⟨ s≤s (m⊓′n⊓′o≤m k l m) ⟩
    suc k         ≤⟨ s≤s (mini dxy _ edit) ⟩
    c             ∎

  step : Dec (x ≈ y) → ∃ (Dist (x ∷ xs) (y ∷ ys))
  step x≈?y = costStep x≈?y , (editStep x≈?y , miniStep x≈?y)

open Step using (step) public
