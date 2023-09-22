------------------------------------------------------------------------
-- The Agda standard library
--
-- Illustration of the `NonNull predicate over `List`
------------------------------------------------------------------------

module README.Data.List.Relation.Unary.Null where

open import Data.List.Base using (List; []; _∷_; head)
open import Data.List.Relation.Unary.Null
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary.Null
open import Relation.Unary.Refinement

private
  variable

    a b : Level
    A   : Set a
    B   : Set b
    x   : A
    xs  : List A
    ys  : List B

------------------------------------------------------------------------
-- Example deployment: a safe head function

safe-head : (xs  : List A) → .{{NonNull xs}} → A
safe-head (x ∷ _) = x

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

  refine⁻ (scanr⁺ []) = e ∷ []
  refined (scanr⁺ []) = _
  
  scanr⁺ (x ∷ xs) with refine⁺ ys ← scanr⁺ xs with y ∷ _  ← ys
    = refine⁺ (f x y ∷ ys)

  scanr : List A → List B
  scanr xs = refine⁻ (scanr⁺ xs)

  instance scanrNonNull : {xs : List A} → NonNull (scanr xs)
  scanrNonNull {xs = xs} with refine⁺ ys ← scanr⁺ xs with y ∷ _  ← ys = _

  unfold-scanr-∷ : ∀ xs →
                   let ys = scanr xs in
                   let instance _ = scanrNonNull {xs = xs} in
                   scanr (x ∷ xs) ≡ f x (safe-head ys) ∷ ys
  unfold-scanr-∷ xs  with refine⁺ ys ← scanr⁺ xs with y ∷ _  ← ys = refl




