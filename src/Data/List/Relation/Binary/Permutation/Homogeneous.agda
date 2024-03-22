------------------------------------------------------------------------
-- The Agda standard library
--
-- A definition for the permutation relation using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Homogeneous where

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.List.Base as List using (List; []; _∷_; [_])
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Nat.Base using (ℕ; suc; _+_; _<_)
open import Data.Nat.Properties
open import Data.Product.Base using (_,_; _×_; ∃; ∃₂)
open import Function.Base using (_∘_; flip)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel; _⇒_; _Preserves_⟶_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Binary.Structures using (IsEquivalence; IsPartialEquivalence)
open import Relation.Binary.Definitions
  using ( Reflexive; Symmetric; Transitive; LeftTrans; RightTrans
        ; _Respects_; _Respects₂_; _Respectsˡ_; _Respectsʳ_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_ ; cong)
open import Relation.Nullary.Decidable using (yes; no; does)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    a p r s : Level
    A B : Set a
    xs ys zs : List A
    x y z v w : A


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
-- Map

module _ {R : Rel A r} {S : Rel A s} where

  map : (R ⇒ S) → (Permutation R ⇒ Permutation S)
  map R⇒S (refl xs∼ys)         = refl (Pointwise.map R⇒S xs∼ys)
  map R⇒S (prep e xs∼ys)       = prep (R⇒S e) (map R⇒S xs∼ys)
  map R⇒S (swap e₁ e₂ xs∼ys)   = swap (R⇒S e₁) (R⇒S e₂) (map R⇒S xs∼ys)
  map R⇒S (trans xs∼ys ys∼zs)  = trans (map R⇒S xs∼ys) (map R⇒S ys∼zs)


------------------------------------------------------------------------
-- Smart inversions

module _ {R : Rel A r}  where

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
-- Properties of Permutation depending on suitable assumptions on R

module _ {R : Rel A r}  where

  private
    _≋_ _↭_ : Rel (List A) _
    _≋_ = Pointwise R
    _↭_ = Permutation R

-- Constructor alias

  ↭-pointwise : _≋_ ⇒ _↭_
  ↭-pointwise = refl

-- Steps: legacy definition

  steps : Permutation R xs ys → ℕ
  steps (refl _)            = 1
  steps (prep _ xs↭ys)      = suc (steps xs↭ys)
  steps (swap _ _ xs↭ys)    = suc (steps xs↭ys)
  steps (trans xs↭ys ys↭zs) = steps xs↭ys + steps ys↭zs

-- Reflexivity and its consequences

  module _ (R-refl : Reflexive R) where

    ↭-refl′ : Reflexive _↭_
    ↭-refl′ = ↭-pointwise (Pointwise.refl R-refl)

    ↭-prep : ∀ {x} {xs ys} → Permutation R xs ys → Permutation R (x ∷ xs) (x ∷ ys)
    ↭-prep xs↭ys = prep R-refl xs↭ys

    ↭-swap : ∀ x y {xs ys} → Permutation R xs ys → Permutation R (x ∷ y ∷ xs) (y ∷ x ∷ ys)
    ↭-swap _ _ xs↭ys = swap R-refl R-refl xs↭ys

    ↭-shift : ∀ {v w} → R v w → ∀ xs {ys zs} → Permutation R ys zs →
              Permutation R (xs List.++ v ∷ ys) (w ∷ xs List.++ zs)
    ↭-shift {v} {w} v≈w []       rel = prep v≈w rel
    ↭-shift {v} {w} v≈w (x ∷ xs) rel
      = trans (↭-prep (↭-shift v≈w xs rel)) (↭-swap x w ↭-refl′)

    shift : ∀ {v w} → R v w → ∀ xs {ys} →
          Permutation R (xs List.++  v ∷ ys) (w ∷ xs List.++ ys)
    shift v≈w xs = ↭-shift v≈w xs ↭-refl′

-- Symmetry and its consequences

  module _ (R-sym : Symmetric R) where

    ↭-sym′ : Symmetric _↭_
    ↭-sym′ (refl xs∼ys)           = refl (Pointwise.symmetric R-sym xs∼ys)
    ↭-sym′ (prep x∼x′ xs↭ys)      = prep (R-sym x∼x′) (↭-sym′ xs↭ys)
    ↭-sym′ (swap x∼x′ y∼y′ xs↭ys) = swap (R-sym y∼y′) (R-sym x∼x′) (↭-sym′ xs↭ys)
    ↭-sym′ (trans xs↭ys ys↭zs)    = trans (↭-sym′ ys↭zs) (↭-sym′ xs↭ys)

-- Transitivity and its consequences

-- A smart version of trans that pushes `refl`s to the leaves (see #1113).

  module _ (↭-transˡ-≋ : LeftTrans _≋_ _↭_) (↭-transʳ-≋ : RightTrans _↭_ _≋_)

    where

    ↭-trans′ : Transitive _↭_
    ↭-trans′ (refl xs≋ys) ys↭zs = ↭-transˡ-≋ xs≋ys ys↭zs
    ↭-trans′ xs↭ys (refl ys≋zs) = ↭-transʳ-≋ xs↭ys ys≋zs
    ↭-trans′ xs↭ys ys↭zs        = trans xs↭ys ys↭zs

-- But Left and Right Transitivity hold!

  module _ (R-trans : Transitive R) where

    private
      ≋-trans : Transitive _≋_
      ≋-trans = Pointwise.transitive R-trans

    ↭-transˡ-≋ : LeftTrans _≋_ _↭_
    ↭-transˡ-≋ xs≋ys               (refl ys≋zs)
      = refl (≋-trans xs≋ys ys≋zs)
    ↭-transˡ-≋ (x≈y ∷ xs≋ys)       (prep y≈z ys↭zs)
      = prep (R-trans x≈y y≈z) (↭-transˡ-≋ xs≋ys ys↭zs)
    ↭-transˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ ys↭zs)
      = swap (R-trans x≈y eq₁) (R-trans w≈z eq₂) (↭-transˡ-≋ xs≋ys ys↭zs)
    ↭-transˡ-≋ xs≋ys               (trans ys↭ws ws↭zs)
      = trans (↭-transˡ-≋ xs≋ys ys↭ws) ws↭zs

    ↭-transʳ-≋ : RightTrans _↭_ _≋_
    ↭-transʳ-≋ (refl xs≋ys)         ys≋zs
      = refl (≋-trans xs≋ys ys≋zs)
    ↭-transʳ-≋ (prep x≈y xs↭ys)     (y≈z ∷ ys≋zs)
      = prep (R-trans x≈y y≈z) (↭-transʳ-≋ xs↭ys ys≋zs)
    ↭-transʳ-≋ (swap eq₁ eq₂ xs↭ys) (x≈w ∷ y≈z ∷ ys≋zs)
      = swap (R-trans eq₁ y≈z) (R-trans eq₂ x≈w) (↭-transʳ-≋ xs↭ys ys≋zs)
    ↭-transʳ-≋ (trans xs↭ws ws↭ys)  ys≋zs
      = trans xs↭ws (↭-transʳ-≋ ws↭ys ys≋zs)

-- Transitivity proper

    ↭-trans : Transitive _↭_
    ↭-trans = ↭-trans′ ↭-transˡ-≋ ↭-transʳ-≋


------------------------------------------------------------------------
-- An important inversion property of Permutation R, which
-- no longer requires `steps` or  well-founded induction...
------------------------------------------------------------------------

module _ {R : Rel A r} (R-refl : Reflexive R) (R-trans : Transitive R)
  where

  private
    ≋-refl : Reflexive (Pointwise R)
    ≋-refl = Pointwise.refl R-refl
    ↭-refl : Reflexive (Permutation R)
    ↭-refl = ↭-refl′ R-refl
    ≋-trans : Transitive (Pointwise R)
    ≋-trans = Pointwise.transitive R-trans
    _++[_]++_ = λ xs (z : A) ys → xs List.++ List.[ z ] List.++ ys

  ↭-split : ∀ v as bs {xs} → Permutation R xs (as ++[ v ]++ bs) →
            ∃₂ λ ps qs → Pointwise R xs (ps ++[ v ]++ qs)
                       × Permutation R (ps List.++ qs) (as List.++ bs)
  ↭-split v as bs p = helper as bs p ≋-refl
    where
    helper : ∀ as bs {xs ys} (p : Permutation R xs ys) →
             Pointwise R ys (as ++[ v ]++ bs) →
             ∃₂ λ ps qs → Pointwise R xs (ps ++[ v ]++ qs)
                        × Permutation R (ps List.++ qs) (as List.++ bs)
    helper as           bs (trans xs↭ys ys↭zs) zs≋as++[v]++ys
      with ps , qs , eq , ↭ ← helper as bs ys↭zs zs≋as++[v]++ys
      with ps′ , qs′ , eq′ , ↭′ ← helper ps qs xs↭ys eq
      = ps′ , qs′ , eq′ , ↭-trans R-trans ↭′ ↭
    helper []           _  (refl (x≈v ∷ xs≋vs)) (v≈y ∷ vs≋ys)
      = [] , _ , R-trans x≈v v≈y ∷ ≋-refl , refl (≋-trans xs≋vs vs≋ys)
    helper (a ∷ as)     bs (refl (x≈v ∷ xs≋vs)) (v≈y ∷ vs≋ys)
      = _ ∷ as , bs , R-trans x≈v v≈y ∷ ≋-trans xs≋vs vs≋ys , ↭-refl′ R-refl
    helper []           bs (prep {xs = xs} x≈v xs↭vs) (v≈y ∷ vs≋ys)
      = [] , xs , R-trans x≈v v≈y ∷ ≋-refl , ↭-transʳ-≋ R-trans xs↭vs vs≋ys
    helper (a ∷ as)     bs (prep x≈v as↭vs) (v≈y ∷ vs≋ys)
      with ps , qs , eq , ↭ ← helper as bs as↭vs vs≋ys
      = a ∷ ps , qs , R-trans x≈v v≈y ∷ eq , prep R-refl ↭
    helper []           [] (swap _ _ _) (_ ∷ ())
    helper []     (b ∷ bs) (swap x≈v y≈w xs↭vs) (w≈z ∷ v≈y ∷ vs≋ys)
      = List.[ b ] , _ , R-trans x≈v v≈y ∷ R-trans y≈w w≈z ∷ ≋-refl
                       , ↭-prep R-refl (↭-transʳ-≋ R-trans xs↭vs vs≋ys)
    helper (a ∷ [])     bs (swap x≈v y≈w xs↭vs)  (w≈z ∷ v≈y ∷ vs≋ys)
      = []     , a ∷ _ , R-trans x≈v v≈y ∷ R-trans y≈w w≈z ∷ ≋-refl
                       , ↭-prep R-refl (↭-transʳ-≋ R-trans xs↭vs vs≋ys)
    helper (a ∷ b ∷ as) bs (swap x≈v y≈w as↭vs) (w≈a ∷ v≈b ∷ vs≋ys)
      with ps , qs , eq , ↭ ← helper as bs as↭vs vs≋ys
      = b ∷ a ∷ ps , qs , R-trans x≈v v≈b ∷ R-trans y≈w w≈a ∷ eq
                        , ↭-swap R-refl _ _ ↭


------------------------------------------------------------------------
-- Permutation is an equivalence satisfying another inversion property

module _ {R : Rel A r} (R-equiv : IsEquivalence R) where

  private module ≈ = IsEquivalence R-equiv

  isEquivalence : IsEquivalence (Permutation R)
  isEquivalence = record
    { refl  = ↭-refl′ ≈.refl
    ; sym   = ↭-sym′ ≈.sym
    ; trans = ↭-trans ≈.trans
    }

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }


  dropMiddleElement-≋ : ∀ {x} ws xs {ys} {zs} →
                        Pointwise R (ws List.++ x ∷ ys) (xs List.++ x ∷ zs) →
                        Permutation R (ws List.++ ys) (xs List.++ zs)
  dropMiddleElement-≋ []       []       (_   ∷ eq) = ↭-pointwise eq
  dropMiddleElement-≋ []       (x ∷ xs) (w≈v ∷ eq)
    = ↭-transˡ-≋ ≈.trans eq (shift ≈.refl w≈v xs)
  dropMiddleElement-≋ (w ∷ ws) []       (w≈x ∷ eq)
    = ↭-transʳ-≋ ≈.trans (↭-sym′ ≈.sym (shift ≈.refl (≈.sym w≈x) ws)) eq
  dropMiddleElement-≋ (w ∷ ws) (x ∷ xs) (w≈x ∷ eq) = prep w≈x (dropMiddleElement-≋ ws xs eq)

  dropMiddleElement : ∀ {v : A} ws xs {ys zs} →
                      Permutation R (ws List.++ x ∷ ys) (xs List.++ x ∷ zs) →
                      Permutation R (ws List.++ ys) (xs List.++ zs)
  dropMiddleElement {v} ws xs {ys} {zs} p
    with ps , qs , eq , ↭ ← ↭-split ≈.refl ≈.trans v xs zs p
    = ↭-trans ≈.trans (dropMiddleElement-≋ ws ps eq) ↭


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
  Any-resp-↭ (refl xs≋ys) pxs                   = Pointwise.Any-resp-Pointwise resp xs≋ys pxs
  Any-resp-↭ (prep x≈y p) (here px)             = here (resp x≈y px)
  Any-resp-↭ (prep x≈y p) (there pxs)           = there (Any-resp-↭ p pxs)
  Any-resp-↭ (swap ≈₁ ≈₂ p) (here px)           = there (here (resp ≈₁ px))
  Any-resp-↭ (swap ≈₁ ≈₂ p) (there (here px))   = here (resp ≈₂ px)
  Any-resp-↭ (swap ≈₁ ≈₂ p) (there (there pxs)) = there (there (Any-resp-↭ p pxs))
  Any-resp-↭ (trans p₁ p₂) pxs                  = Any-resp-↭ p₂ (Any-resp-↭ p₁ pxs)

------------------------------------------------------------------------
-- Two higher-dimensional properties useful in the `Propositional` case,
-- specifically in the equivalence proof between `Bag` equality and `_↭_`

module _ {_≈_ : Rel A r} (≈-trans : Transitive _≈_) where

  private
    ∈-resp : ∀ {x} → (_≈_ x) Respects _≈_
    ∈-resp = flip ≈-trans

  ∈-resp-Pointwise : (Any (x ≈_)) Respects (Pointwise _≈_)
  ∈-resp-Pointwise = Pointwise.Any-resp-Pointwise ∈-resp

  ∈-resp-↭ : (Any (x ≈_)) Respects (Permutation _≈_)
  ∈-resp-↭ = Any-resp-↭ ∈-resp

  module _ (≈-sym : Symmetric _≈_)
           (≈-sym-involutive : ∀ {x y} (p : x ≈ y) → ≈-sym (≈-sym p) ≡ p)
    where

    private
      ≋-sym : Symmetric (Pointwise _≈_)
      ≋-sym = Pointwise.symmetric ≈-sym
      ↭-sym : Symmetric (Permutation _≈_)
      ↭-sym = ↭-sym′ ≈-sym

    ↭-sym-involutive′ : (p : Permutation _≈_ xs ys) → ↭-sym (↭-sym p) ≡ p
    ↭-sym-involutive′ (refl xs≋ys) = ≡.cong refl (≋-sym-involutive′ xs≋ys)
      where
      ≋-sym-involutive′ : (p : Pointwise _≈_ xs ys) → ≋-sym (≋-sym p) ≡ p
      ≋-sym-involutive′ [] = ≡.refl
      ≋-sym-involutive′ (x≈y ∷ xs≋ys) rewrite ≈-sym-involutive x≈y
        = ≡.cong (_ ∷_) (≋-sym-involutive′ xs≋ys)
    ↭-sym-involutive′ (prep eq p) = ≡.cong₂ prep (≈-sym-involutive eq) (↭-sym-involutive′ p)
    ↭-sym-involutive′ (swap eq₁ eq₂ p) rewrite ≈-sym-involutive eq₁ | ≈-sym-involutive eq₂
      = ≡.cong (swap _ _) (↭-sym-involutive′ p)
    ↭-sym-involutive′ (trans p q) = ≡.cong₂ trans (↭-sym-involutive′ p) (↭-sym-involutive′ q)

    module _ (≈-trans-trans-sym : ∀ {x y z} (p : x ≈ y) (q : y ≈ z) →
                                  ≈-trans (≈-trans p q) (≈-sym q) ≡ p)
      where

      ∈-resp-Pointwise-sym : (p : Pointwise _≈_ xs ys) {ix : Any (x ≈_) xs} →
                             ∈-resp-Pointwise (≋-sym p) (∈-resp-Pointwise p ix) ≡ ix
      ∈-resp-Pointwise-sym (x≈y ∷ xs≋ys) {here ix} 
        = cong here (≈-trans-trans-sym ix x≈y)
      ∈-resp-Pointwise-sym (x≈y ∷ xs≋ys) {there ixs}
        = cong there (∈-resp-Pointwise-sym xs≋ys)

      ∈-resp-↭-sym′   : (p : Permutation _≈_ ys xs) {iy : Any (x ≈_) ys} {ix : Any (x ≈_) xs} →
                       ix ≡ ∈-resp-↭ p iy → ∈-resp-↭ (↭-sym p) ix ≡ iy
      ∈-resp-↭-sym′ (refl xs≋ys) ≡.refl = ∈-resp-Pointwise-sym xs≋ys
      ∈-resp-↭-sym′ (prep eq₁ p) {here iy} {here ix} eq
        with ≡.refl ← eq = cong here (≈-trans-trans-sym iy eq₁)
      ∈-resp-↭-sym′ (prep eq₁ p) {there iys} {there ixs} eq
        with ≡.refl ← eq = cong there (∈-resp-↭-sym′ p ≡.refl)
      ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {here ix} {here iy} ()
      ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {here ix} {there iys} eq
        with ≡.refl ← eq = cong here (≈-trans-trans-sym ix eq₁)
      ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {there (here ix)} {there (here iy)} ()
      ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {there (here ix)} {here iy} eq
        with ≡.refl ← eq = cong (there ∘ here) (≈-trans-trans-sym ix eq₂)
      ∈-resp-↭-sym′ (swap eq₁ eq₂ p) {there (there ixs)} {there (there iys)} eq
        with ≡.refl ← eq = cong (there ∘ there) (∈-resp-↭-sym′ p ≡.refl)
      ∈-resp-↭-sym′ (trans p₁ p₂) eq = ∈-resp-↭-sym′ p₁ (∈-resp-↭-sym′ p₂ eq)

      ∈-resp-↭-sym : (p : Permutation _≈_ xs ys) {ix : Any (x ≈_) xs} →
                     ∈-resp-↭ (↭-sym p) (∈-resp-↭ p ix) ≡ ix
      ∈-resp-↭-sym p = ∈-resp-↭-sym′ p ≡.refl

      ∈-resp-↭-sym⁻¹ : (p : Permutation _≈_ xs ys) {iy : Any (x ≈_) ys} →
                       ∈-resp-↭ p (∈-resp-↭ (↭-sym p) iy) ≡ iy
      ∈-resp-↭-sym⁻¹ p with eq′ ← ∈-resp-↭-sym′ (↭-sym p)
                       rewrite ↭-sym-involutive′ p = eq′ ≡.refl


------------------------------------------------------------------------
-- AllPairs

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
-- Properties of List functions, possibly depending on properties of R
------------------------------------------------------------------------

-- length

module _ {R : Rel A r} where

  ↭-length : Permutation R xs ys → List.length xs ≡ List.length ys
  ↭-length (refl xs≋ys)        = Pointwise.Pointwise-length xs≋ys
  ↭-length (prep _ xs↭ys)      = cong suc (↭-length xs↭ys)
  ↭-length (swap _ _ xs↭ys)    = cong (suc ∘ suc) (↭-length xs↭ys)
  ↭-length (trans xs↭ys ys↭zs) = ≡.trans (↭-length xs↭ys) (↭-length ys↭zs)

-- map

module _ {R : Rel A r} {S : Rel B s} {f} (pres : f Preserves R ⟶ S) where

  map⁺ : Permutation R xs ys → Permutation S (List.map f xs) (List.map f ys)

  map⁺ (refl xs≋ys)        = refl (Pointwise.map⁺ _ _ (Pointwise.map pres xs≋ys))
  map⁺ (prep x xs↭ys)      = prep (pres x) (map⁺ xs↭ys)
  map⁺ (swap x y xs↭ys)    = swap (pres x) (pres y) (map⁺ xs↭ys)
  map⁺ (trans xs↭ys ys↭zs) = trans (map⁺ xs↭ys) (map⁺ ys↭zs)
{-
  -- permutations preserve 'being a mapped list'
  ↭-map-inv : ∀ {zs : List B} → Permutation S (List.map f xs) zs →
              ∃ λ ys → zs ≡ List.map f ys × Permutation R xs ys
  ↭-map-inv p = {!p!}
-}

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


------------------------------------------------------------------------
-- foldr of Commutative Monoid

module _ (commutativeMonoid : CommutativeMonoid a r) where
  open module CM = CommutativeMonoid commutativeMonoid

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


------------------------------------------------------------------------
-- Properties of steps, and related properties of Permutation
-- previously required for proofs by well-founded induction
-- rendered obsolete/deprecatable by ↭-transˡ-≋ , ↭-transʳ-≋
------------------------------------------------------------------------

module Steps {R : Rel A r} where

-- Basic property

  0<steps : (xs↭ys : Permutation R xs ys) → 0 < steps xs↭ys
  0<steps (refl _)             = n<1+n 0
  0<steps (prep eq xs↭ys)      = m<n⇒m<1+n (0<steps xs↭ys)
  0<steps (swap eq₁ eq₂ xs↭ys) = m<n⇒m<1+n (0<steps xs↭ys)
  0<steps (trans xs↭ys ys↭zs) =
    <-≤-trans (0<steps xs↭ys) (m≤m+n (steps xs↭ys) (steps ys↭zs))

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

↭-singleton⁻¹ : {R : Rel A r} → Transitive R →
                ∀ {xs x} → Permutation R xs [ x ] → ∃ λ y → xs ≡ [ y ] × R y x
↭-singleton⁻¹ = ↭-singleton-invʳ

