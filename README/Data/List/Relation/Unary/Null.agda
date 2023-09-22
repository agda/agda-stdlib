------------------------------------------------------------------------
-- The Agda standard library
--
-- Illustration of the `NonNull predicate over `List`
------------------------------------------------------------------------

module README.Data.List.Relation.Unary.Null where

open import Data.List.Base using (List; []; _∷_; head)
open import Data.List.Relation.Unary.Null
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; ∃₂; _×_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary.Null
open import Relation.Unary.Refinement

private
  variable

    a b   : Level
    A     : Set a
    B     : Set b
    x     : A
    xs zs : List A

------------------------------------------------------------------------
-- Example deployment: a safe head function

safe-head : (xs  : List A) → .{{NonNull xs}} → A
safe-head (x ∷ _) = x

safe-head-≡ : (eq : x ∷ xs ≡ zs) →
              let instance _ = subst NonNull eq _ in x ≡ safe-head zs
safe-head-≡ refl = refl

------------------------------------------------------------------------
-- Example deployments: scans

-- ScanL

module ScanL (f : A → B → A) where

  scanl : A → List B → List A
  scanl e []       = e ∷ []
  scanl e (x ∷ xs) = e ∷ scanl (f e x) xs

  instance scanlNonNull : {e : A} {xs : List B} → NonNull (scanl e xs)
  scanlNonNull {xs = []}     = _
  scanlNonNull {xs = x ∷ xs} = _

  scanl⁺ : A → List B → [ List A ]⁺
  scanl⁺ e xs = refine⁺ (scanl e xs)


-- ScanR

module ScanRΣ (f : A → B → B) (e : B) where

-- design pattern: refinement types via Σ-types

  scanrΣ        : List A → Σ (List B) NonNull
  scanrΣ []                                       =     e ∷ [] , _
  scanrΣ (x ∷ xs) with ys@(y ∷ _) , _ ← scanrΣ xs = f x y ∷ ys , _

  scanr         : List A → List B
  scanr xs = proj₁ (scanrΣ xs)

  instance scanrNonNull : {xs : List A} → NonNull (scanr xs)
  scanrNonNull {xs = xs} = proj₂ (scanrΣ xs)

  unfold-scanr-∷ : ∀ xs →
                   let ys = scanr xs in
                   let instance _ = scanrNonNull {xs = xs} in
                   scanr (x ∷ xs) ≡ f x (safe-head ys) ∷ ys
  unfold-scanr-∷ xs with ys@(y ∷ _) , _ ← scanrΣ xs = refl

module ScanR (f : A → B → B) (e : B) where

-- design pattern: refinement types via mutual recursion

-- to simulate the refinement type { xs : List A | NonNull xs }
-- define two functions by mutual recursion:
-- `f`         : the bare, 'extracted' underlying function
-- `fNonNull` : the (irrelevant instance) witness to the refinement predicate

-- but for now, again we seem to have to go via a third function
-- essentially `scanrΣ` but with an irrelevant instance field instead

  scanr⁺ : List A → [ List B ]⁺
  scanr⁺ []                                                    =     e ∷⁺ []
  scanr⁺ (x ∷ xs) with refine⁺ ys ← scanr⁺ xs with y ∷ _  ← ys = f x y ∷⁺ ys

  scanr : List A → List B
  scanr xs = refine⁻ (scanr⁺ xs)

  instance scanrNonNull : {xs : List A} → NonNull (scanr xs)
  scanrNonNull {xs = xs} with refine⁺ ys ← scanr⁺ xs with y ∷ _  ← ys = _

  unfold-scanr-∷ : ∀ xs →
                   let ys = scanr xs in
                   let instance _ = scanrNonNull {xs = xs} in
                   scanr (x ∷ xs) ≡ f x (safe-head ys) ∷ ys
  unfold-scanr-∷ xs with refine⁺ ys ← scanr⁺ xs in eq with y ∷ _  ← ys = refl

  unfold-scanr-∷≡ : ∀ xs → let ys = scanr xs in
                    ∃₂ λ y ys′ → ys ≡ y ∷ ys′ × scanr (x ∷ xs) ≡ f x y ∷ ys
  unfold-scanr-∷≡ xs with refine⁺ ys ← scanr⁺ xs with y ∷ _ ← ys
    = y , _ , refl , refl

module ScanR′ (f : A → B → B) (e : B) where

-- design pattern: refinement types via mutual recursion, using `nonNull-≡`

-- to simulate the refinement type { xs : List A | NonNull xs }
-- define two functions by mutual recursion:
-- `f`         : the bare, 'extracted' underlying function
-- `fNonNull` : the (irrelevant instance) witness to the refinement predicate

-- but still using a `helper` function

  scanr : List A → List B
  instance scanrNonNull : {xs : List A} → NonNull (scanr xs)

  private
    helper : (xs : List A) → ∃₂ λ y ys → scanr xs ≡ y ∷ ys
    helper xs = nonNull-[ scanr xs ]⁻ {{scanrNonNull {xs = xs}}}

  scanr []       = e ∷ []
  scanr (x ∷ xs) with y , _ ← helper xs = f x y ∷ scanr xs

  scanrNonNull {xs = []}     = _
  scanrNonNull {xs = x ∷ xs} with _ ← helper xs = _

  unfold-scanr-∷ : ∀ xs →
                   let ys = scanr xs in
                   let instance _ = scanrNonNull {xs = xs} in
                   scanr (x ∷ xs) ≡ f x (safe-head ys) ∷ ys
  unfold-scanr-∷ xs with y , _ , eq ← helper xs
    = cong (λ y → f _ y ∷ scanr xs) (safe-head-≡ (sym eq))

  unfold-scanr-∷≡ : ∀ xs → let ys = scanr xs in
                    ∃₂ λ y ys′ → ys ≡ y ∷ ys′ × scanr (x ∷ xs) ≡ f x y ∷ ys
  unfold-scanr-∷≡ xs with y , _ , eq ← helper xs = y , _ , eq , refl

