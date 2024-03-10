------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Homogeneous where

open import Algebra using (IsCommutativeMonoid; Op₂)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Nat.Base using (ℕ; suc; _+_; _<_)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Product.Base using (_,_; _×_; ∃₂)
open import Function.Base using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel; _⇒_; _Preserves_⟶_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions
  using ( Reflexive; Symmetric; Transitive; LeftTrans; RightTrans
        ; _Respects_; _Respects₂_; _Respectsˡ_; _Respectsʳ_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_ ; cong)
open import Relation.Nullary.Decidable using (yes; no; does)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    a p r s : Level
    A B : Set a
    xs ys zs : List A

------------------------------------------------------------------------
-- Definition

module _ {A : Set a} (R : Rel A r) where

  data Permutation : Rel (List A) (a ⊔ r) where
    refl  : ∀ {xs ys} → Pointwise R xs ys → Permutation xs ys
    prep  : ∀ {xs ys x y} (eq : R x y) → Permutation xs ys → Permutation (x ∷ xs) (y ∷ ys)
    swap  : ∀ {xs ys x y x′ y′} (eq₁ : R x x′) (eq₂ : R y y′) →
            Permutation xs ys → Permutation (x ∷ y ∷ xs) (y′ ∷ x′ ∷ ys)
    trans : Transitive Permutation

------------------------------------------------------------------------
-- Functions over permutations

module _ {R : Rel A r}  where

  steps : Permutation R xs ys → ℕ
  steps (refl _)            = 1
  steps (prep _ xs↭ys)      = suc (steps xs↭ys)
  steps (swap _ _ xs↭ys)    = suc (steps xs↭ys)
  steps (trans xs↭ys ys↭zs) = steps xs↭ys + steps ys↭zs

-- Constructor alias

  ↭-pointwise : (Pointwise R) ⇒ Permutation R
  ↭-pointwise = refl


------------------------------------------------------------------------
-- The Permutation relation is an equivalence

module _ {R : Rel A r}  where

  ↭-refl′ : Reflexive R → Reflexive (Permutation R)
  ↭-refl′ R-refl = ↭-pointwise (Pointwise.refl R-refl)

  sym : Symmetric R → Symmetric (Permutation R)
  sym R-sym (refl xs∼ys)           = refl (Pointwise.symmetric R-sym xs∼ys)
  sym R-sym (prep x∼x′ xs↭ys)      = prep (R-sym x∼x′) (sym R-sym xs↭ys)
  sym R-sym (swap x∼x′ y∼y′ xs↭ys) = swap (R-sym y∼y′) (R-sym x∼x′) (sym R-sym xs↭ys)
  sym R-sym (trans xs↭ys ys↭zs)    = trans (sym R-sym ys↭zs) (sym R-sym xs↭ys)

  isEquivalence : Reflexive R → Symmetric R → IsEquivalence (Permutation R)
  isEquivalence R-refl R-sym = record
    { refl  = ↭-refl′ R-refl
    ; sym   = sym R-sym
    ; trans = trans
    }

  setoid : Reflexive R → Symmetric R → Setoid _ _
  setoid R-refl R-sym = record
    { isEquivalence = isEquivalence R-refl R-sym
    }

------------------------------------------------------------------------
-- Map

module _ {R : Rel A r} {S : Rel A s} where

  map : (R ⇒ S) → (Permutation R ⇒ Permutation S)
  map R⇒S (refl xs∼ys)         = refl (Pointwise.map R⇒S xs∼ys)
  map R⇒S (prep e xs∼ys)       = prep (R⇒S e) (map R⇒S xs∼ys)
  map R⇒S (swap e₁ e₂ xs∼ys)   = swap (R⇒S e₁) (R⇒S e₂) (map R⇒S xs∼ys)
  map R⇒S (trans xs∼ys ys∼zs)  = trans (map R⇒S xs∼ys) (map R⇒S ys∼zs)

------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

module _ {R : Rel A r} {P : Pred A p} (resp : P Respects R) where

  All-resp-↭ : (All P) Respects (Permutation R)
  All-resp-↭ (refl xs≋ys)   pxs             = Pointwise.All-resp-Pointwise resp xs≋ys pxs
  All-resp-↭ (prep x≈y p)   (px ∷ pxs)      = resp x≈y px ∷ All-resp-↭ p pxs
  All-resp-↭ (swap ≈₁ ≈₂ p) (px ∷ py ∷ pxs) = resp ≈₂ py ∷ resp ≈₁ px ∷ All-resp-↭ p pxs
  All-resp-↭ (trans p₁ p₂)  pxs             = All-resp-↭ p₂ (All-resp-↭ p₁ pxs)

  Any-resp-↭ : (Any P) Respects (Permutation R)
  Any-resp-↭ (refl xs≋ys) pxs                 = Pointwise.Any-resp-Pointwise resp xs≋ys pxs
  Any-resp-↭ (prep x≈y p) (here px)           = here (resp x≈y px)
  Any-resp-↭ (prep x≈y p) (there pxs)         = there (Any-resp-↭ p pxs)
  Any-resp-↭ (swap x y p) (here px)           = there (here (resp x px))
  Any-resp-↭ (swap x y p) (there (here px))   = here (resp y px)
  Any-resp-↭ (swap x y p) (there (there pxs)) = there (there (Any-resp-↭ p pxs))
  Any-resp-↭ (trans p₁ p₂) pxs                = Any-resp-↭ p₂ (Any-resp-↭ p₁ pxs)

module _ {R : Rel A r} {S : Rel A s}
         (sym : Symmetric S) (resp@(rʳ , rˡ) : S Respects₂ R) where
  
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
-- Properties of steps, and properties of Permutation,
-- which may depend on properties of the underlying relation
------------------------------------------------------------------------

module _ {R : Rel A r} where

  0<steps : (xs↭ys : Permutation R xs ys) → 0 < steps xs↭ys
  0<steps (refl _)             = n<1+n 0
  0<steps (prep eq xs↭ys)      = m<n⇒m<1+n (0<steps xs↭ys)
  0<steps (swap eq₁ eq₂ xs↭ys) = m<n⇒m<1+n (0<steps xs↭ys)
  0<steps (trans xs↭ys xs↭ys₁) =
    <-≤-trans (0<steps xs↭ys) (m≤m+n (steps xs↭ys) (steps xs↭ys₁))


module _ {R : Rel A r} (R-refl : Reflexive R) where

  ↭-prep : ∀ x {xs ys} → Permutation R xs ys → Permutation R (x ∷ xs) (x ∷ ys)
  ↭-prep _ xs↭ys = prep R-refl xs↭ys

  ↭-swap : ∀ x y {xs ys} → Permutation R xs ys → Permutation R (x ∷ y ∷ xs) (y ∷ x ∷ ys)
  ↭-swap _ _ xs↭ys = swap R-refl R-refl xs↭ys


module _ {R : Rel A r} (R-trans : Transitive R) where

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

  ↭-transˡ-≋ : LeftTrans (Pointwise R) (Permutation R)
  ↭-transˡ-≋ xs≋ys               (refl ys≋zs)         = refl (≋-trans xs≋ys ys≋zs)
  ↭-transˡ-≋ (x≈y ∷ xs≋ys)       (prep y≈z ys↭zs)     = prep (R-trans x≈y y≈z) (↭-transˡ-≋ xs≋ys ys↭zs)
  ↭-transˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ ys↭zs) = swap (R-trans x≈y eq₁) (R-trans w≈z eq₂) (↭-transˡ-≋ xs≋ys ys↭zs)
  ↭-transˡ-≋ xs≋ys               (trans ys↭ws ws↭zs)  = trans (↭-transˡ-≋ xs≋ys ys↭ws) ws↭zs

  ↭-transʳ-≋ : RightTrans (Permutation R) (Pointwise R)
  ↭-transʳ-≋ (refl xs≋ys) ys≋zs = refl (≋-trans xs≋ys ys≋zs)
  ↭-transʳ-≋ (prep x≈y xs↭ys) (y≈z ∷ ys≋zs) = prep (R-trans x≈y y≈z) (↭-transʳ-≋ xs↭ys ys≋zs)
  ↭-transʳ-≋ (swap eq₁ eq₂ xs↭ys) (x≈w ∷ y≈z ∷ ys≋zs) = swap (R-trans eq₁ y≈z) (R-trans eq₂ x≈w) (↭-transʳ-≋ xs↭ys ys≋zs)
  ↭-transʳ-≋ (trans xs↭ws ws↭ys) ys≋zs = trans xs↭ws (↭-transʳ-≋ ws↭ys ys≋zs)

-- A smart version of trans that pushes `refl`s to the leaves (see #1113).
  ↭-trans : Transitive (Permutation R)
  ↭-trans (refl xs≋ys) ys↭zs = ↭-transˡ-≋ xs≋ys ys↭zs
  ↭-trans xs↭ys (refl ys≋zs) = ↭-transʳ-≋ xs↭ys ys≋zs
  ↭-trans xs↭ys ys↭zs        = trans xs↭ys ys↭zs


module _ {R : Rel A r} (R-sym : Symmetric R) (R-trans : Transitive R) where

  private
    ≋-sym : Symmetric (Pointwise R)
    ≋-sym = Pointwise.symmetric R-sym
    ≋-trans : Transitive (Pointwise R)
    ≋-trans = Pointwise.transitive R-trans

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


module _ {R : Rel A r} (R-refl : Reflexive R) (R-trans : Transitive R) where

  private
    ≋-refl = Pointwise.refl {R = R} R-refl
    ↭-refl = ↭-refl′ {R = R} R-refl
    _++[_]++_ = λ (xs : List A) z ys → xs List.++ List.[ z ] List.++ ys

  split-↭ : ∀ v as bs {xs} → Permutation R xs (as ++[ v ]++ bs) →
            ∃₂ λ ps qs → Pointwise R xs (ps ++[ v ]++ qs)
                       × Permutation R (ps List.++ qs) (as List.++ bs)
  split-↭ v as bs p = helper as bs p (<-wellFounded (steps p))
    where
    helper : ∀ as bs {xs} (p : Permutation R xs (as ++[ v ]++ bs)) →
             Acc _<_ (steps p) →
             ∃₂ λ ps qs → Pointwise R xs (ps ++[ v ]++ qs)
                        × Permutation R (ps List.++ qs) (as List.++ bs)
    helper []           bs (refl eq)        _ = []         , bs , eq , ↭-refl
    helper (a ∷ [])     bs (refl eq)        _ = List.[ a ]      , bs , eq , ↭-refl
    helper (a ∷ b ∷ as) bs (refl eq)        _ = a ∷ b ∷ as , bs , eq , ↭-refl
    helper []           bs (prep v≈x xs↭bs) _ = [] , _ , v≈x ∷ ≋-refl , xs↭bs
    helper (a ∷ as)     bs (prep eq as↭xs) (acc rec)
      with ps , qs , eq₂ , ↭ ← helper as bs as↭xs (rec (n<1+n _))
      = a ∷ ps , qs , eq ∷ eq₂ , prep R-refl ↭
    helper [] (b ∷ bs)     (swap x≈b y≈v xs↭bs) _
      = List.[ b ] , _ , x≈b ∷ y≈v ∷ ≋-refl , prep R-refl xs↭bs
    helper (a ∷ [])     bs (swap x≈v y≈a xs↭bs) _
      = []     , a ∷ _ , x≈v ∷ y≈a ∷ ≋-refl , prep R-refl xs↭bs
    helper (a ∷ b ∷ as) bs (swap x≈b y≈a as↭xs) (acc rec)
      with ps , qs , eq , ↭ ← helper as bs as↭xs (rec (n<1+n _))
      = b ∷ a ∷ ps , qs , x≈b ∷ y≈a ∷ eq , swap R-refl R-refl ↭
    helper as           bs (trans xs↭ys ys↭zs) (acc rec)
      with ps , qs , eq , ↭ ← helper as bs ys↭zs (rec (m<n+m (steps ys↭zs) (0<steps xs↭ys)))
      with ps′ , qs′ , eq′ , ↭′ ← helper ps qs (↭-respʳ-≋ R-trans eq xs↭ys)
        (rec (≡.subst (_< _) (≡.sym (steps-respʳ R-trans eq xs↭ys))
             (m<m+n (steps xs↭ys) (0<steps ys↭zs))))
      = ps′ , qs′ , eq′ , ↭-trans R-trans ↭′ ↭

module _ {R : Rel A r}
         (R-refl : Reflexive R)
         (R-sym : Symmetric R)
         (R-trans : Transitive R) where

  private
    ≋-refl = Pointwise.refl {R = R} R-refl
    ≋-sym  = Pointwise.symmetric {R = R} R-sym
    ↭-refl = ↭-refl′ {R = R} R-refl
    ↭-sym  = sym {R = R} R-sym
    _++[_]++_ = λ (xs : List A) z ys → xs List.++ List.[ z ] List.++ ys

  shift : ∀ {v w} → R v w → ∀ xs {ys} →
          Permutation R (xs ++[ v ]++ ys) (w ∷ xs List.++ ys)
  shift {v} {w} v≈w []       = refl (v≈w ∷ ≋-refl)
  shift {v} {w} v≈w (x ∷ xs) = trans (↭-prep R-refl x (shift v≈w xs)) (↭-swap R-refl x w ↭-refl)

  dropMiddleElement-≋ : ∀ {x} ws xs {ys} {zs} →
                        Pointwise R (ws ++[ x ]++ ys) (xs ++[ x ]++ zs) →
                        Permutation R (ws List.++ ys) (xs List.++ zs)
  dropMiddleElement-≋ []       []       (_   ∷ eq) = refl eq
  dropMiddleElement-≋ []       (x ∷ xs) (w≈v ∷ eq) = ↭-transˡ-≋ R-trans eq (shift w≈v xs)
  dropMiddleElement-≋ (w ∷ ws) []       (w≈x ∷ eq) = ↭-transʳ-≋ R-trans (↭-sym (shift (R-sym w≈x) ws)) eq
  dropMiddleElement-≋ (w ∷ ws) (x ∷ xs) (w≈x ∷ eq) = prep w≈x (dropMiddleElement-≋ ws xs eq)

  dropMiddleElement : ∀ {v} ws xs {ys zs} →
                      Permutation R (ws ++[ v ]++ ys) (xs ++[ v ]++ zs) →
                      Permutation R (ws List.++ ys) (xs List.++ zs)
  dropMiddleElement {v} ws xs {ys} {zs} p
    with ps , qs , eq , ↭ ← split-↭ R-refl R-trans v xs zs p
    = ↭-trans R-trans (dropMiddleElement-≋ ws ps eq) ↭


------------------------------------------------------------------------
-- Properties of List functions
------------------------------------------------------------------------

-- map

module _ {R : Rel A r} {S : Rel B s} {f} (pres : f Preserves R ⟶ S) where

  map⁺ : Permutation R xs ys → Permutation S (List.map f xs) (List.map f ys)

  map⁺ (refl xs≋ys)        = refl (Pointwise.map⁺ _ _ (Pointwise.map pres xs≋ys))
  map⁺ (prep x xs↭ys)      = prep (pres x) (map⁺ xs↭ys)
  map⁺ (swap x y xs↭ys)    = swap (pres x) (pres y) (map⁺ xs↭ys)
  map⁺ (trans xs↭ys ys↭zs) = trans (map⁺ xs↭ys) (map⁺ ys↭zs)


------------------------------------------------------------------------
-- Properties of List functions which depend on
-- properties of the underlying relation

-- _++_

module _ {R : Rel A r} (R-refl : Reflexive R) where

  ++⁺ʳ : ∀ zs → Permutation R xs ys →
         Permutation R (xs List.++ zs) (ys List.++ zs)
  ++⁺ʳ zs (refl xs≋ys)        = refl (Pointwise.++⁺ xs≋ys (Pointwise.refl R-refl))
  ++⁺ʳ zs (prep x xs↭ys)      = prep x (++⁺ʳ zs xs↭ys)
  ++⁺ʳ zs (swap x y xs↭ys)    = swap x y (++⁺ʳ zs xs↭ys)
  ++⁺ʳ zs (trans xs↭ys ys↭zs) = trans (++⁺ʳ zs xs↭ys) (++⁺ʳ zs ys↭zs)


-- filter

module _ {R : Rel A r} (R-sym : Symmetric R)
         {p} {P : Pred A p} (P? : Decidable P) (P≈ : P Respects R) where

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


-- foldr of Commutative Monoid

module _ {_≈_ : Rel A r} {_∙_ : Op₂ A} {ε : A}
         (isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ ε) where
  open module CM = IsCommutativeMonoid isCommutativeMonoid

  private foldr = List.foldr

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
