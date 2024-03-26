------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the `Homogeneous` definition of permutation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --warn=noUserWarning #-} -- for deprecated function `steps`

module Data.List.Relation.Binary.Permutation.Homogeneous.Properties where

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.List.Base as List using (List; []; _∷_; [_]; _++_; length)
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.Nat.Base using (ℕ; suc; _+_; _<_)
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (_,_; _×_; ∃)
open import Function.Base using (_∘_; flip)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel; _Preserves_⟶_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Definitions
  using ( Reflexive; Symmetric; Transitive; LeftTrans; RightTrans
        ; _Respects_; _Respects₂_; _Respectsˡ_; _Respectsʳ_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_ ; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; does)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; Decidable)

open import Data.List.Relation.Binary.Permutation.Homogeneous
import Data.List.Relation.Binary.Permutation.Homogeneous.Properties.Core as Properties

private
  variable
    a p r s : Level
    A B : Set a
    xs ys zs : List A
    x y z v w : A
    P : Pred A p
    R : Rel A r
    S : Rel A s

------------------------------------------------------------------------
-- Re-export `Core` properties
------------------------------------------------------------------------

open Properties public

------------------------------------------------------------------------
-- Inversion principles
------------------------------------------------------------------------


↭-[]-invˡ : Permutation R [] xs → xs ≡ []
↭-[]-invˡ (refl [])           = ≡.refl
↭-[]-invˡ (trans xs↭ys ys↭zs) with ≡.refl ← ↭-[]-invˡ xs↭ys = ↭-[]-invˡ ys↭zs

↭-[]-invʳ : Permutation R xs [] → xs ≡ []
↭-[]-invʳ (refl [])           = ≡.refl
↭-[]-invʳ (trans xs↭ys ys↭zs) with ≡.refl ← ↭-[]-invʳ ys↭zs = ↭-[]-invʳ xs↭ys

¬x∷xs↭[]ˡ : ¬ (Permutation R [] (x ∷ xs))
¬x∷xs↭[]ˡ (trans xs↭ys ys↭zs) with ≡.refl ← ↭-[]-invˡ xs↭ys = ¬x∷xs↭[]ˡ ys↭zs

¬x∷xs↭[]ʳ : ¬ (Permutation R (x ∷ xs) [])
¬x∷xs↭[]ʳ (trans xs↭ys ys↭zs) with ≡.refl ← ↭-[]-invʳ ys↭zs = ¬x∷xs↭[]ʳ xs↭ys

module _ (R-trans : Transitive R) where

  ↭-singleton-invˡ : Permutation R [ x ] xs → ∃ λ y → xs ≡ [ y ] × R x y
  ↭-singleton-invˡ (refl (xRy ∷ [])) = _ , ≡.refl , xRy
  ↭-singleton-invˡ (prep xRy p)
    with ≡.refl ← ↭-[]-invˡ p     = _ , ≡.refl , xRy
  ↭-singleton-invˡ (trans r s)
    with _ , ≡.refl , xRy ← ↭-singleton-invˡ r
    with _ , ≡.refl , yRz ← ↭-singleton-invˡ s
    = _ , ≡.refl , R-trans xRy yRz

  ↭-singleton-invʳ : Permutation R xs [ x ] → ∃ λ y → xs ≡ [ y ] × R y x
  ↭-singleton-invʳ (refl (yRx ∷ [])) = _ , ≡.refl , yRx
  ↭-singleton-invʳ (prep yRx p)
    with ≡.refl ← ↭-[]-invʳ p     = _ , ≡.refl , yRx
  ↭-singleton-invʳ (trans r s)
    with _ , ≡.refl , yRx ← ↭-singleton-invʳ s
    with _ , ≡.refl , zRy ← ↭-singleton-invʳ r
    = _ , ≡.refl , R-trans zRy yRx


------------------------------------------------------------------------
-- Properties of List functions, possibly depending on properties of R
------------------------------------------------------------------------

-- length

↭-length : Permutation R xs ys → length xs ≡ length ys
↭-length (refl xs≋ys)        = Pointwise.Pointwise-length xs≋ys
↭-length (prep _ xs↭ys)      = cong suc (↭-length xs↭ys)
↭-length (swap _ _ xs↭ys)    = cong (suc ∘ suc) (↭-length xs↭ys)
↭-length (trans xs↭ys ys↭zs) = ≡.trans (↭-length xs↭ys) (↭-length ys↭zs)

-- map

module _ {f} (pres : f Preserves R ⟶ S) where

  map⁺ : Permutation R xs ys → Permutation S (List.map f xs) (List.map f ys)

  map⁺ (refl xs≋ys)        = refl (Pointwise.map⁺ _ _ (Pointwise.map pres xs≋ys))
  map⁺ (prep x xs↭ys)      = prep (pres x) (map⁺ xs↭ys)
  map⁺ (swap x y xs↭ys)    = swap (pres x) (pres y) (map⁺ xs↭ys)
  map⁺ (trans xs↭ys ys↭zs) = trans (map⁺ xs↭ys) (map⁺ ys↭zs)


-- _++_

module _ (R-refl : Reflexive R) where

  ++⁺ʳ : ∀ zs → Permutation R xs ys →
         Permutation R (xs List.++ zs) (ys List.++ zs)
  ++⁺ʳ zs (refl xs≋ys)        = refl (Pointwise.++⁺ xs≋ys (Pointwise.refl R-refl))
  ++⁺ʳ zs (prep x xs↭ys)      = prep x (++⁺ʳ zs xs↭ys)
  ++⁺ʳ zs (swap x y xs↭ys)    = swap x y (++⁺ʳ zs xs↭ys)
  ++⁺ʳ zs (trans xs↭ys ys↭zs) = trans (++⁺ʳ zs xs↭ys) (++⁺ʳ zs ys↭zs)


-- filter

module _ (R-sym : Symmetric R)
         (P? : Decidable P) (P≈ : P Respects R) where

  filter⁺ : Permutation R xs ys →
            Permutation R (List.filter P? xs) (List.filter P? ys)
  filter⁺ (refl xs≋ys)        = refl (Pointwise.filter⁺ P? P? P≈ (P≈ ∘ R-sym) xs≋ys)
  filter⁺ (trans xs↭zs zs↭ys) = trans (filter⁺ xs↭zs) (filter⁺ zs↭ys)
  filter⁺ {x ∷ xs} {y ∷ ys} (prep x≈y xs↭ys) with P? x | P? y
  ... | yes _  | yes _  = prep x≈y (filter⁺ xs↭ys)
  ... | yes Px | no ¬Py = contradiction (P≈ x≈y Px) ¬Py
  ... | no ¬Px | yes Py = contradiction (P≈ (R-sym x≈y) Py) ¬Px
  ... | no  _  | no  _  = filter⁺ xs↭ys
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) with P? x | P? y
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) | no ¬Px | no ¬Py
    with P? z | P? w
  ... | _      | yes Pw = contradiction (P≈ w≈y Pw) ¬Py
  ... | yes Pz | _      = contradiction (P≈ (R-sym x≈z) Pz) ¬Px
  ... | no _   | no  _  = filter⁺ xs↭ys
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) | no ¬Px | yes Py
    with P? z | P? w
  ... | _      | no ¬Pw = contradiction (P≈ (R-sym w≈y) Py) ¬Pw
  ... | yes Pz | _      = contradiction (P≈ (R-sym x≈z) Pz) ¬Px
  ... | no _   | yes _  = prep w≈y (filter⁺ xs↭ys)
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys)  | yes Px | no ¬Py
    with P? z | P? w
  ... | no ¬Pz | _      = contradiction (P≈ x≈z Px) ¬Pz
  ... | _      | yes Pw = contradiction (P≈ w≈y Pw) ¬Py
  ... | yes _  | no _   = prep x≈z (filter⁺ xs↭ys)
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) | yes Px | yes Py
    with P? z | P? w
  ... | no ¬Pz | _      = contradiction (P≈ x≈z Px) ¬Pz
  ... | _      | no ¬Pw = contradiction (P≈ (R-sym w≈y) Py) ¬Pw
  ... | yes _  | yes _  = swap x≈z w≈y (filter⁺ xs↭ys)


------------------------------------------------------------------------
-- foldr over a Commutative Monoid

module _ (commutativeMonoid : CommutativeMonoid a r) where

  private
    foldr = List.foldr
    open module CM = CommutativeMonoid commutativeMonoid

  foldr-commMonoid : Permutation _≈_ xs ys → foldr _∙_ ε xs ≈ foldr _∙_ ε ys
  foldr-commMonoid (refl xs≋ys) = Pointwise.foldr⁺ ∙-cong CM.refl xs≋ys
  foldr-commMonoid (prep x≈y xs↭ys) = ∙-cong x≈y (foldr-commMonoid xs↭ys)
  foldr-commMonoid (swap {xs} {ys} {x} {y} {x′} {y′} x≈x′ y≈y′ xs↭ys) = begin
    x ∙ (y ∙ foldr _∙_ ε xs)   ≈⟨ ∙-congˡ (∙-congˡ (foldr-commMonoid xs↭ys)) ⟩
    x ∙ (y ∙ foldr _∙_ ε ys)   ≈⟨ assoc x y (foldr _∙_ ε ys) ⟨
    (x ∙ y) ∙ foldr _∙_ ε ys   ≈⟨ ∙-congʳ (comm x y) ⟩
    (y ∙ x) ∙ foldr _∙_ ε ys   ≈⟨ ∙-congʳ (∙-cong y≈y′ x≈x′) ⟩
    (y′ ∙ x′) ∙ foldr _∙_ ε ys ≈⟨ assoc y′ x′ (foldr _∙_ ε ys) ⟩
    y′ ∙ (x′ ∙ foldr _∙_ ε ys) ∎
    where open ≈-Reasoning CM.setoid
  foldr-commMonoid (trans xs↭ys ys↭zs) =
    CM.trans (foldr-commMonoid xs↭ys) (foldr-commMonoid ys↭zs)


------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

-- All and Any

module _ (resp : P Respects R) where

  All-resp-↭ : (All P) Respects (Permutation R)
  All-resp-↭ (refl xs≋ys)   pxs             = Pointwise.All-resp-Pointwise resp xs≋ys pxs
  All-resp-↭ (prep x≈y p)   (px ∷ pxs)      = resp x≈y px ∷ All-resp-↭ p pxs
  All-resp-↭ (swap ≈₁ ≈₂ p) (px ∷ py ∷ pxs) = resp ≈₂ py ∷ resp ≈₁ px ∷ All-resp-↭ p pxs
  All-resp-↭ (trans p₁ p₂)  pxs             = All-resp-↭ p₂ (All-resp-↭ p₁ pxs)

  Any-resp-↭ : (Any P) Respects (Permutation R)
  Any-resp-↭ (refl xs≋ys) pxs                   = Pointwise.Any-resp-Pointwise resp xs≋ys pxs
  Any-resp-↭ (prep x≈y p) (here px)             = here (resp x≈y px)
  Any-resp-↭ (prep x≈y p) (there pxs)           = there (Any-resp-↭ p pxs)
  Any-resp-↭ (swap ≈₁ ≈₂ p) (here px)           = there (here (resp ≈₁ px))
  Any-resp-↭ (swap ≈₁ ≈₂ p) (there (here px))   = here (resp ≈₂ px)
  Any-resp-↭ (swap ≈₁ ≈₂ p) (there (there pxs)) = there (there (Any-resp-↭ p pxs))
  Any-resp-↭ (trans p₁ p₂) pxs                  = Any-resp-↭ p₂ (Any-resp-↭ p₁ pxs)

-- Membership

module _ {_≈_ : Rel A r} (≈-trans : Transitive _≈_) where

  private
    ∈-resp : ∀ {x} → (x ≈_) Respects _≈_
    ∈-resp = flip ≈-trans

  ∈-resp-Pointwise : (Any (x ≈_)) Respects (Pointwise _≈_)
  ∈-resp-Pointwise = Pointwise.Any-resp-Pointwise ∈-resp

  ∈-resp-↭ : (Any (x ≈_)) Respects (Permutation _≈_)
  ∈-resp-↭ = Any-resp-↭ ∈-resp

-- AllPairs

module _ (sym : Symmetric S) (resp@(rʳ , rˡ) : S Respects₂ R) where

  AllPairs-resp-↭ : (AllPairs S) Respects (Permutation R)
  AllPairs-resp-↭ (refl xs≋ys)     pxs             =
    Pointwise.AllPairs-resp-Pointwise resp xs≋ys pxs
  AllPairs-resp-↭ (prep x≈y p)     (∼ ∷ pxs)       =
    All-resp-↭ rʳ p (All.map (rˡ x≈y) ∼) ∷ AllPairs-resp-↭ p pxs
  AllPairs-resp-↭ (swap eq₁ eq₂ p) ((∼₁ ∷ ∼₂) ∷ ∼₃ ∷ pxs) =
    (sym (rʳ eq₂ (rˡ eq₁ ∼₁)) ∷ All-resp-↭ rʳ p (All.map (rˡ eq₂) ∼₃)) ∷
    All-resp-↭ rʳ p (All.map (rˡ eq₁) ∼₂) ∷ AllPairs-resp-↭ p pxs
  AllPairs-resp-↭ (trans p₁ p₂)    pxs             =
    AllPairs-resp-↭ p₂ (AllPairs-resp-↭ p₁ pxs)


------------------------------------------------------------------------
-- Properties of steps, and related properties of Permutation
-- previously required for proofs by well-founded induction
-- rendered obsolete/deprecatable by ↭-transˡ-≋ , ↭-transʳ-≋
------------------------------------------------------------------------

module Steps {R : Rel A r} where

-- Basic property

  0<steps : (xs↭ys : Permutation R xs ys) → 0 < steps xs↭ys
  0<steps (refl _)             = ℕ.n<1+n 0
  0<steps (prep eq xs↭ys)      = ℕ.m<n⇒m<1+n (0<steps xs↭ys)
  0<steps (swap eq₁ eq₂ xs↭ys) = ℕ.m<n⇒m<1+n (0<steps xs↭ys)
  0<steps (trans xs↭ys ys↭zs) =
    ℕ.<-≤-trans (0<steps xs↭ys) (ℕ.m≤m+n (steps xs↭ys) (steps ys↭zs))

  module _ (R-trans : Transitive R) where

    private
      ≋-trans : Transitive (Pointwise R)
      ≋-trans = Pointwise.transitive R-trans

    ↭-respʳ-≋ : (Permutation R) Respectsʳ (Pointwise R)
    ↭-respʳ-≋ xs≋ys               (refl zs≋xs)         = refl (≋-trans zs≋xs xs≋ys)
    ↭-respʳ-≋ (x≈y ∷ xs≋ys)       (prep eq zs↭xs)      = prep (R-trans eq x≈y) (↭-respʳ-≋ xs≋ys zs↭xs)
    ↭-respʳ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ zs↭xs) = swap (R-trans eq₁ w≈z) (R-trans eq₂ x≈y) (↭-respʳ-≋ xs≋ys zs↭xs)
    ↭-respʳ-≋ xs≋ys               (trans ws↭zs zs↭xs)  = trans ws↭zs (↭-respʳ-≋ xs≋ys zs↭xs)

    steps-respʳ : (xs≋ys : Pointwise R xs ys) (zs↭xs : Permutation R zs xs) →
                  steps (↭-respʳ-≋ xs≋ys zs↭xs) ≡ steps zs↭xs
    steps-respʳ _               (refl _)            = ≡.refl
    steps-respʳ (_ ∷ ys≋xs)     (prep _ ys↭zs)      = cong suc (steps-respʳ ys≋xs ys↭zs)
    steps-respʳ (_ ∷ _ ∷ ys≋xs) (swap _ _ ys↭zs)    = cong suc (steps-respʳ ys≋xs ys↭zs)
    steps-respʳ ys≋xs           (trans ys↭ws ws↭zs) = cong (steps ys↭ws +_) (steps-respʳ ys≋xs ws↭zs)

    module _ (R-sym : Symmetric R) where

      private
        ≋-sym : Symmetric (Pointwise R)
        ≋-sym = Pointwise.symmetric R-sym

      ↭-respˡ-≋ : (Permutation R) Respectsˡ (Pointwise R)
      ↭-respˡ-≋ xs≋ys               (refl ys≋zs)         = refl (≋-trans (≋-sym xs≋ys) ys≋zs)
      ↭-respˡ-≋ (x≈y ∷ xs≋ys)       (prep eq zs↭xs)      = prep (R-trans (R-sym x≈y) eq) (↭-respˡ-≋ xs≋ys zs↭xs)
      ↭-respˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ zs↭xs) = swap (R-trans (R-sym x≈y) eq₁) (R-trans (R-sym w≈z) eq₂) (↭-respˡ-≋ xs≋ys zs↭xs)
      ↭-respˡ-≋ xs≋ys               (trans ws↭zs zs↭xs)  = trans (↭-respˡ-≋ xs≋ys ws↭zs) zs↭xs

      steps-respˡ : (ys≋xs : Pointwise R ys xs) (ys↭zs : Permutation R ys zs) →
                    steps (↭-respˡ-≋ ys≋xs ys↭zs) ≡ steps ys↭zs
      steps-respˡ _               (refl _)            = ≡.refl
      steps-respˡ (_ ∷ ys≋xs)     (prep _ ys↭zs)      = cong suc (steps-respˡ ys≋xs ys↭zs)
      steps-respˡ (_ ∷ _ ∷ ys≋xs) (swap _ _ ys↭zs)    = cong suc (steps-respˡ ys≋xs ys↭zs)
      steps-respˡ ys≋xs           (trans ys↭ws ws↭zs) = cong (_+ steps ws↭zs) (steps-respˡ ys≋xs ys↭ws)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

¬x∷xs↭[] = ¬x∷xs↭[]ʳ
{-# WARNING_ON_USAGE ¬x∷xs↭[]
"Warning: ¬x∷xs↭[] was deprecated in v2.1.
Please use ¬x∷xs↭[]ʳ instead."
#-}

↭-singleton⁻¹ : Transitive R →
                ∀ {xs x} → Permutation R xs [ x ] → ∃ λ y → xs ≡ [ y ] × R y x
↭-singleton⁻¹ = ↭-singleton-invʳ
{-# WARNING_ON_USAGE ↭-singleton⁻¹
"Warning: ↭-singleton⁻¹ was deprecated in v2.1.
Please use ↭-singleton-invʳ instead."
#-}

