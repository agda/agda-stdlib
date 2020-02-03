------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutations using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary hiding (Decidable)

module Data.List.Relation.Binary.Permutation.Setoid.Properties
  {a ℓ} (S : Setoid a ℓ)
  where

open import Algebra
open import Data.Fin.Base using (Fin)
open import Data.List.Base as List hiding (head; tail)
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; head; tail)
import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.Unique.Setoid as Unique
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties using (∈-∃++; ∈-insert)
open import Data.List.Relation.Binary.BagAndSetEquality
  using (bag; _∼[_]_; empty-unique; drop-cons; commutativeMonoid)
import Data.List.Properties as Lₚ
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Function using (_∘_; _⟨_⟩_; flip)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (inverse)
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.Properties.Setoid S using (≉-resp₂)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl; sym; cong; cong₂; subst; _≢_; inspect)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    b p r : Level

open Setoid S using (_≈_) renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open Permutation S
open Membership S
open Unique S using (Unique)
open module ≋ = Equality S
  using (_≋_; []; _∷_; ≋-refl; ≋-sym; ≋-trans; All-resp-≋; Any-resp-≋; AllPairs-resp-≋)
open PermutationReasoning

------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

All-resp-↭ : ∀ {P : Pred A p} → P Respects _≈_ → (All P) Respects _↭_
All-resp-↭ resp (refl xs≋ys)   pxs             = All-resp-≋ resp xs≋ys pxs
All-resp-↭ resp (prep x≈y p)   (px ∷ pxs)      = resp x≈y px ∷ All-resp-↭ resp p pxs
All-resp-↭ resp (swap ≈₁ ≈₂ p) (px ∷ py ∷ pxs) = resp ≈₂ py ∷ resp ≈₁ px ∷ All-resp-↭ resp p pxs
All-resp-↭ resp (trans p₁ p₂)  pxs             = All-resp-↭ resp p₂ (All-resp-↭ resp p₁ pxs)

Any-resp-↭ : ∀ {P : Pred A p} → P Respects _≈_ → (Any P) Respects _↭_
Any-resp-↭ resp (refl xs≋ys) pxs                 = Any-resp-≋ resp xs≋ys pxs
Any-resp-↭ resp (prep x≈y p) (here px)           = here (resp x≈y px)
Any-resp-↭ resp (prep x≈y p) (there pxs)         = there (Any-resp-↭ resp p pxs)
Any-resp-↭ resp (swap x y p) (here px)           = there (here (resp x px))
Any-resp-↭ resp (swap x y p) (there (here px))   = here (resp y px)
Any-resp-↭ resp (swap x y p) (there (there pxs)) = there (there (Any-resp-↭ resp p pxs))
Any-resp-↭ resp (trans p₁ p₂) pxs                = Any-resp-↭ resp p₂ (Any-resp-↭ resp p₁ pxs)

AllPairs-resp-↭ : ∀ {R : Rel A r} → Symmetric R → R Respects₂ _≈_ → (AllPairs R) Respects _↭_
AllPairs-resp-↭ sym resp (refl xs≋ys)     pxs             = AllPairs-resp-≋ resp xs≋ys pxs
AllPairs-resp-↭ sym resp (prep x≈y p)     (∼ ∷ pxs)       =
  All-resp-↭ (proj₁ resp) p (All.map (proj₂ resp x≈y) ∼) ∷
  AllPairs-resp-↭ sym resp p pxs
AllPairs-resp-↭ sym resp@(rʳ , rˡ) (swap eq₁ eq₂ p) ((∼₁ ∷ ∼₂) ∷ ∼₃ ∷ pxs) =
  (sym (rʳ eq₂ (rˡ eq₁ ∼₁)) ∷ All-resp-↭ rʳ p (All.map (rˡ eq₂) ∼₃)) ∷
  All-resp-↭ rʳ p (All.map (rˡ eq₁) ∼₂) ∷
  AllPairs-resp-↭ sym resp p pxs
AllPairs-resp-↭ sym resp (trans p₁ p₂)    pxs             =
  AllPairs-resp-↭ sym resp p₂ (AllPairs-resp-↭ sym resp p₁ pxs)

∈-resp-↭ : ∀ {x} → (x ∈_) Respects _↭_
∈-resp-↭ = Any-resp-↭ (flip ≈-trans)

Unique-resp-↭ : Unique Respects _↭_
Unique-resp-↭ = AllPairs-resp-↭ (_∘ ≈-sym) ≉-resp₂

------------------------------------------------------------------------
-- Relationships to other relations
------------------------------------------------------------------------

≋⇒↭ : _≋_ ⇒ _↭_
≋⇒↭ = refl

↭-respʳ-≋ : _↭_ Respectsʳ _≋_
↭-respʳ-≋ xs≋ys               (refl zs≋xs)         = refl (≋-trans zs≋xs xs≋ys)
↭-respʳ-≋ (x≈y ∷ xs≋ys)       (prep eq zs↭xs)      = prep (≈-trans eq x≈y) (↭-respʳ-≋ xs≋ys zs↭xs)
↭-respʳ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ zs↭xs) = swap (≈-trans eq₁ w≈z) (≈-trans eq₂ x≈y) (↭-respʳ-≋ xs≋ys zs↭xs)
↭-respʳ-≋ xs≋ys               (trans ws↭zs zs↭xs)  = trans ws↭zs (↭-respʳ-≋ xs≋ys zs↭xs)

↭-respˡ-≋ : _↭_ Respectsˡ _≋_
↭-respˡ-≋ xs≋ys               (refl ys≋zs)         = refl (≋-trans (≋-sym xs≋ys) ys≋zs)
↭-respˡ-≋ (x≈y ∷ xs≋ys)       (prep eq zs↭xs)      = prep (≈-trans (≈-sym x≈y) eq) (↭-respˡ-≋ xs≋ys zs↭xs)
↭-respˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ zs↭xs) = swap (≈-trans (≈-sym x≈y) eq₁) (≈-trans (≈-sym w≈z) eq₂) (↭-respˡ-≋ xs≋ys zs↭xs)
↭-respˡ-≋ xs≋ys               (trans ws↭zs zs↭xs)  = trans (↭-respˡ-≋ xs≋ys ws↭zs) zs↭xs

------------------------------------------------------------------------
-- Properties of steps
------------------------------------------------------------------------

0<steps : ∀ {xs ys} (xs↭ys : xs ↭ ys) → 0 < steps xs↭ys
0<steps (refl _)             = s≤s z≤n
0<steps (prep eq xs↭ys)      = ≤-step (0<steps xs↭ys)
0<steps (swap eq₁ eq₂ xs↭ys) = ≤-step (0<steps xs↭ys)
0<steps (trans xs↭ys xs↭ys₁) =
  <-transˡ (0<steps xs↭ys) (m≤m+n (steps xs↭ys) (steps xs↭ys₁))

steps-respˡ : ∀ {xs ys zs} (ys≋xs : ys ≋ xs) (ys↭zs : ys ↭ zs) →
              steps (↭-respˡ-≋ ys≋xs ys↭zs) ≡ steps ys↭zs
steps-respˡ _               (refl _)            = refl
steps-respˡ (_ ∷ ys≋xs)     (prep _ ys↭zs)      = cong suc (steps-respˡ ys≋xs ys↭zs)
steps-respˡ (_ ∷ _ ∷ ys≋xs) (swap _ _ ys↭zs)    = cong suc (steps-respˡ ys≋xs ys↭zs)
steps-respˡ ys≋xs           (trans ys↭ws ws↭zs) = cong (_+ steps ws↭zs) (steps-respˡ ys≋xs ys↭ws)

steps-respʳ : ∀ {xs ys zs} (xs≋ys : xs ≋ ys) (zs↭xs : zs ↭ xs) →
              steps (↭-respʳ-≋ xs≋ys zs↭xs) ≡ steps zs↭xs
steps-respʳ _               (refl _)            = refl
steps-respʳ (_ ∷ ys≋xs)     (prep _ ys↭zs)      = cong suc (steps-respʳ ys≋xs ys↭zs)
steps-respʳ (_ ∷ _ ∷ ys≋xs) (swap _ _ ys↭zs)    = cong suc (steps-respʳ ys≋xs ys↭zs)
steps-respʳ ys≋xs           (trans ys↭ws ws↭zs) = cong (steps ys↭ws +_) (steps-respʳ ys≋xs ws↭zs)

------------------------------------------------------------------------
-- Properties of list functions
------------------------------------------------------------------------

------------------------------------------------------------------------
-- map

module _ (T : Setoid b ℓ) where

  open Setoid T using () renaming (_≈_ to _≈′_)
  open Permutation T using () renaming (_↭_ to _↭′_)

  map⁺ : ∀ {f} → f Preserves _≈_ ⟶ _≈′_ →
         ∀ {xs ys} → xs ↭ ys → map f xs ↭′ map f ys
  map⁺ pres (refl xs≋ys)  = refl (Pointwise.map⁺ _ _ (Pointwise.map pres xs≋ys))
  map⁺ pres (prep x p)    = prep (pres x) (map⁺ pres p)
  map⁺ pres (swap x y p)  = swap (pres x) (pres y) (map⁺ pres p)
  map⁺ pres (trans p₁ p₂) = trans (map⁺ pres p₁) (map⁺ pres p₂)

------------------------------------------------------------------------
-- _++_

shift : ∀ {v w} → v ≈ w → (xs ys : List A) → xs ++ [ v ] ++ ys ↭ w ∷ xs ++ ys
shift {v} {w} v≈w []       ys = prep v≈w ↭-refl
shift {v} {w} v≈w (x ∷ xs) ys = begin
  x ∷ (xs ++ [ v ] ++ ys) <⟨ shift v≈w xs ys ⟩
  x ∷ w ∷ xs ++ ys        <<⟨ ↭-refl ⟩
  w ∷ x ∷ xs ++ ys        ∎

++⁺ˡ : ∀ xs {ys zs : List A} → ys ↭ zs → xs ++ ys ↭ xs ++ zs
++⁺ˡ []       ys↭zs = ys↭zs
++⁺ˡ (x ∷ xs) ys↭zs = ↭-prep _ (++⁺ˡ xs ys↭zs)

++⁺ʳ : ∀ {xs ys : List A} zs → xs ↭ ys → xs ++ zs ↭ ys ++ zs
++⁺ʳ zs (refl xs≋ys)  = refl (Pointwise.++⁺ xs≋ys ≋-refl)
++⁺ʳ zs (prep x ↭)    = prep x (++⁺ʳ zs ↭)
++⁺ʳ zs (swap x y ↭)  = swap x y (++⁺ʳ zs ↭)
++⁺ʳ zs (trans ↭₁ ↭₂) = trans (++⁺ʳ zs ↭₁) (++⁺ʳ zs ↭₂)

++⁺ : _++_ Preserves₂ _↭_ ⟶ _↭_ ⟶ _↭_
++⁺ ws↭xs ys↭zs = trans (++⁺ʳ _ ws↭xs) (++⁺ˡ _ ys↭zs)

-- Algebraic properties

++-identityˡ : LeftIdentity _↭_ [] _++_
++-identityˡ xs = ↭-refl

++-identityʳ : RightIdentity _↭_ [] _++_
++-identityʳ xs = ↭-reflexive (Lₚ.++-identityʳ xs)

++-identity : Identity _↭_ [] _++_
++-identity = ++-identityˡ , ++-identityʳ

++-assoc : Associative _↭_ _++_
++-assoc xs ys zs = ↭-reflexive (Lₚ.++-assoc xs ys zs)

++-comm : Commutative _↭_ _++_
++-comm []       ys = ↭-sym (++-identityʳ ys)
++-comm (x ∷ xs) ys = begin
  x ∷ xs ++ ys         <⟨ ++-comm xs ys ⟩
  x ∷ ys ++ xs         ≡⟨ cong (λ v → x ∷ v ++ xs) (≡.sym (Lₚ.++-identityʳ _)) ⟩
  (x ∷ ys ++ []) ++ xs ↭⟨ ++⁺ʳ xs (↭-sym (shift ≈-refl ys [])) ⟩
  (ys ++ [ x ]) ++ xs  ↭⟨ ++-assoc ys [ x ] xs ⟩
  ys ++ ([ x ] ++ xs)  ≡⟨⟩
  ys ++ (x ∷ xs)       ∎

-- Structures

++-isMagma : IsMagma _↭_ _++_
++-isMagma = record
  { isEquivalence = ↭-isEquivalence
  ; ∙-cong        = ++⁺
  }

++-isSemigroup : IsSemigroup _↭_ _++_
++-isSemigroup = record
  { isMagma = ++-isMagma
  ; assoc   = ++-assoc
  }

++-isMonoid : IsMonoid _↭_ _++_ []
++-isMonoid = record
  { isSemigroup = ++-isSemigroup
  ; identity    = ++-identity
  }

++-isCommutativeMonoid : IsCommutativeMonoid _↭_ _++_ []
++-isCommutativeMonoid = record
  { isMonoid = ++-isMonoid
  ; comm     = ++-comm
  }

-- Bundles

++-magma : Magma a (a ⊔ ℓ)
++-magma = record
  { isMagma = ++-isMagma
  }

++-semigroup : Semigroup a (a ⊔ ℓ)
++-semigroup = record
  { isSemigroup = ++-isSemigroup
  }

++-monoid : Monoid a (a ⊔ ℓ)
++-monoid = record
  { isMonoid = ++-isMonoid
  }

++-commutativeMonoid : CommutativeMonoid a (a ⊔ ℓ)
++-commutativeMonoid = record
  { isCommutativeMonoid = ++-isCommutativeMonoid
  }

-- Some other useful lemmas

zoom : ∀ h {t xs ys : List A} → xs ↭ ys → h ++ xs ++ t ↭ h ++ ys ++ t
zoom h {t} = ++⁺ˡ h ∘ ++⁺ʳ t

inject : ∀ (v : A) {ws xs ys zs} → ws ↭ ys → xs ↭ zs →
         ws ++ [ v ] ++ xs ↭ ys ++ [ v ] ++ zs
inject v ws↭ys xs↭zs = trans (++⁺ˡ _ (↭-prep _ xs↭zs)) (++⁺ʳ _ ws↭ys)

shifts : ∀ xs ys {zs : List A} → xs ++ ys ++ zs ↭ ys ++ xs ++ zs
shifts xs ys {zs} = begin
   xs ++ ys  ++ zs ↭˘⟨ ++-assoc xs ys zs ⟩
  (xs ++ ys) ++ zs ↭⟨ ++⁺ʳ zs (++-comm xs ys) ⟩
  (ys ++ xs) ++ zs ↭⟨ ++-assoc ys xs zs ⟩
   ys ++ xs  ++ zs ∎

dropMiddleElement-≋ : ∀ {x} ws xs {ys} {zs} →
           ws ++ [ x ] ++ ys ≋ xs ++ [ x ] ++ zs →
           ws ++ ys ↭ xs ++ zs
dropMiddleElement-≋ []       []       (_   ∷ eq) = ≋⇒↭ eq
dropMiddleElement-≋ []       (x ∷ xs) (w≈v ∷ eq) = ↭-respˡ-≋ (≋-sym eq) (shift w≈v xs _)
dropMiddleElement-≋ (w ∷ ws) []       (w≈x ∷ eq) = ↭-respʳ-≋ eq (↭-sym (shift (≈-sym w≈x) ws _))
dropMiddleElement-≋ (w ∷ ws) (x ∷ xs) (w≈x ∷ eq) = prep w≈x (dropMiddleElement-≋ ws xs eq)

dropMiddleElement : ∀ {v} ws xs {ys zs} →
                    ws ++ [ v ] ++ ys ↭ xs ++ [ v ] ++ zs →
                    ws ++ ys ↭ xs ++ zs
dropMiddleElement {v} ws xs {ys} {zs} p = helper p ws xs ≋-refl ≋-refl
  where
  lemma : ∀ {w x y z} → w ≈ x → x ≈ y → z ≈ y → w ≈ z
  lemma w≈x x≈y z≈y = ≈-trans (≈-trans w≈x x≈y) (≈-sym z≈y)

  open PermutationReasoning

  -- The l′ & l″ could be eliminated at the cost of making the `trans` case
  -- much more difficult to prove. At the very least would require using `Acc`.
  helper : ∀ {l′ l″ : List A} → l′ ↭ l″ →
           ∀ ws xs {ys zs : List A} →
           ws ++ [ v ] ++ ys ≋ l′ →
           xs ++ [ v ] ++ zs ≋ l″ →
           ws ++ ys ↭ xs ++ zs
  helper {as}     {bs}     (refl eq3) ws xs {ys} {zs} eq1 eq2 =
    dropMiddleElement-≋ ws xs (≋-trans (≋-trans eq1 eq3) (≋-sym eq2))
  helper {_ ∷ as} {_ ∷ bs} (prep _ as↭bs) [] [] {ys} {zs} (_ ∷ ys≋as) (_ ∷ zs≋bs) = begin
    ys               ≋⟨  ys≋as ⟩
    as               ↭⟨  as↭bs ⟩
    bs               ≋˘⟨ zs≋bs ⟩
    zs               ∎
  helper {_ ∷ as} {_ ∷ bs} (prep a≈b as↭bs) [] (x ∷ xs) {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    ys               ≋⟨  ≋₁ ⟩
    as               ↭⟨  as↭bs ⟩
    bs               ≋˘⟨ ≋₂ ⟩
    xs ++ v ∷ zs     ↭⟨  shift (lemma ≈₁ a≈b ≈₂) xs zs ⟩
    x ∷ xs ++ zs     ∎
  helper {_ ∷ as} {_ ∷ bs} (prep v≈w p) (w ∷ ws) [] {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    w ∷ ws ++ ys     ↭⟨  ↭-sym (shift (lemma ≈₂ (≈-sym v≈w) ≈₁) ws ys) ⟩
    ws ++ v ∷ ys     ≋⟨  ≋₁ ⟩
    as               ↭⟨  p ⟩
    bs               ≋˘⟨ ≋₂ ⟩
    zs               ∎
  helper {_ ∷ as} {_ ∷ bs} (prep w≈x p) (w ∷ ws) (x ∷ xs) {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    w ∷ ws ++ ys     ↭⟨ prep (lemma ≈₁ w≈x ≈₂) (helper p ws xs ≋₁ ≋₂) ⟩
    x ∷ xs ++ zs     ∎
  helper {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap v≈x y≈v p) [] [] {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    ys               ≋⟨  ≋₁ ⟩
    a ∷ as           ↭⟨  prep (≈-trans (≈-trans (≈-trans y≈v (≈-sym ≈₂)) ≈₁) v≈x) p ⟩
    b ∷ bs           ≋˘⟨ ≋₂ ⟩
    zs               ∎
  helper {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap v≈w y≈w p) [] (x ∷ []) {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    ys               ≋⟨  ≋₁ ⟩
    a ∷ as           ↭⟨  prep y≈w p ⟩
    _ ∷ bs           ≋˘⟨ ≈₂ ∷ tail ≋₂ ⟩
    x ∷ zs           ∎
  helper {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap v≈w y≈x p) [] (x ∷ w ∷ xs) {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    ys               ≋⟨ ≋₁ ⟩
    a ∷ as           ↭⟨ prep y≈x p ⟩
    _ ∷ bs           ≋⟨ ≋-sym (≈₂ ∷ tail ≋₂) ⟩
    x ∷ xs ++ v ∷ zs ↭⟨ prep ≈-refl (shift (lemma ≈₁ v≈w (head ≋₂)) xs zs) ⟩
    x ∷ w ∷ xs ++ zs ∎
  helper {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap w≈x _ p) (w ∷ []) [] {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    w ∷ ys           ≋⟨ ≈₁ ∷ tail (≋₁) ⟩
    _ ∷ as           ↭⟨ prep w≈x p ⟩
    b ∷ bs           ≋⟨ ≋-sym ≋₂ ⟩
    zs               ∎
  helper {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap w≈y x≈v p) (w ∷ x ∷ ws) [] {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    w ∷ x ∷ ws ++ ys ↭⟨ prep ≈-refl (↭-sym (shift (lemma ≈₂ (≈-sym x≈v) (head ≋₁)) ws ys)) ⟩
    w ∷ ws ++ v ∷ ys ≋⟨ ≈₁ ∷ tail ≋₁ ⟩
    _ ∷ as           ↭⟨ prep w≈y p ⟩
    b ∷ bs           ≋⟨ ≋-sym ≋₂ ⟩
    zs               ∎
  helper {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap x≈v v≈y p) (x ∷ []) (y ∷ []) {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    x ∷ ys           ≋⟨ ≈₁ ∷ tail ≋₁ ⟩
    _ ∷ as           ↭⟨ prep (≈-trans x≈v (≈-trans (≈-sym (head ≋₂)) (≈-trans (head ≋₁) v≈y))) p ⟩
    _ ∷ bs           ≋⟨ ≋-sym (≈₂ ∷ tail ≋₂) ⟩
    y ∷ zs           ∎
  helper {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap y≈w v≈z p) (y ∷ []) (z ∷ w ∷ xs) {ys} {zs} (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    y ∷ ys           ≋⟨ ≈₁ ∷ tail ≋₁ ⟩
    _ ∷ as           ↭⟨ prep y≈w p ⟩
    _ ∷ bs           ≋⟨ ≋-sym ≋₂ ⟩
    w ∷ xs ++ v ∷ zs ↭⟨ ↭-prep w (shift ≈-refl xs zs) ⟩
    w ∷ v ∷ xs ++ zs ↭⟨ swap ≈-refl (lemma (head ≋₁) v≈z ≈₂) ↭-refl ⟩
    z ∷ w ∷ xs ++ zs ∎
  helper {_ ∷ a ∷ as} {_ ∷ b ∷ bs} (swap y≈v w≈z p) (y ∷ w ∷ ws) (z ∷ []) {ys} {zs}    (≈₁ ∷ ≋₁) (≈₂ ∷ ≋₂) = begin
    y ∷ w ∷ ws ++ ys ↭⟨ swap (lemma ≈₁ y≈v (head ≋₂)) ≈-refl ↭-refl ⟩
    w ∷ v ∷ ws ++ ys ↭⟨ ↭-prep w (↭-sym (shift ≈-refl ws ys)) ⟩
    w ∷ ws ++ v ∷ ys ≋⟨ ≋₁ ⟩
    _ ∷ as           ↭⟨ prep w≈z p ⟩
    _ ∷ bs           ≋⟨ ≋-sym (≈₂ ∷ tail ≋₂) ⟩
    z ∷ zs           ∎
  helper (swap x≈z y≈w p) (x ∷ y ∷ ws) (w ∷ z ∷ xs) {ys} {zs} (≈₁ ∷ ≈₃ ∷ ≋₁) (≈₂ ∷ ≈₄ ∷ ≋₂) = begin
    x ∷ y ∷ ws ++ ys ↭⟨ swap (lemma ≈₁ x≈z ≈₄) (lemma ≈₃ y≈w ≈₂) (helper p ws xs ≋₁ ≋₂) ⟩
    w ∷ z ∷ xs ++ zs ∎
  helper {as} {bs} (trans p₁ p₂) ws xs eq1 eq2
    with ∈-∃++ S (∈-resp-↭ (↭-respˡ-≋ (≋-sym eq1) p₁) (∈-insert S ws ≈-refl))
  ... | (h , t , w , v≈w , eq) = trans
    (helper p₁ ws h eq1 (≋-trans (≋.++⁺ ≋-refl (v≈w ∷ ≋-refl)) (≋-sym eq)))
    (helper p₂ h xs (≋-trans (≋.++⁺ ≋-refl (v≈w ∷ ≋-refl)) (≋-sym eq)) eq2)

dropMiddle : ∀ {vs} ws xs {ys zs} →
             ws ++ vs ++ ys ↭ xs ++ vs ++ zs →
             ws ++ ys ↭ xs ++ zs
dropMiddle {[]}     ws xs p = p
dropMiddle {v ∷ vs} ws xs p = dropMiddle ws xs (dropMiddleElement ws xs p)

split : ∀ (v : A) as bs {xs} → xs ↭ as ++ [ v ] ++ bs → ∃₂ λ ps qs → xs ≋ ps ++ [ v ] ++ qs
split v as bs p = helper as bs p (<-wellFounded (steps p))
  where
  helper : ∀ as bs {xs} (p : xs ↭ as ++ [ v ] ++ bs) → Acc _<_ (steps p) →
           ∃₂ λ ps qs → xs ≋ ps ++ [ v ] ++ qs
  helper []           bs (refl eq)    _ = []         , bs , eq
  helper (a ∷ [])     bs (refl eq)    _ = [ a ]      , bs , eq
  helper (a ∷ b ∷ as) bs (refl eq)    _ = a ∷ b ∷ as , bs , eq
  helper []           bs (prep v≈x _) _ = [] , _ , v≈x ∷ ≋-refl
  helper (a ∷ as)     bs (prep eq as↭xs) (acc rec) with helper as bs as↭xs (rec _ ≤-refl)
  ... | (ps , qs , eq₂) = a ∷ ps , qs , eq ∷ eq₂
  helper [] (b ∷ bs)     (swap x≈b y≈v _) _ = [ b ] , _     , x≈b ∷ y≈v ∷ ≋-refl
  helper (a ∷ [])     bs (swap x≈v y≈a ↭) _ = []    , a ∷ _ , x≈v ∷ y≈a ∷ ≋-refl
  helper (a ∷ b ∷ as) bs (swap x≈b y≈a as↭xs) (acc rec) with helper as bs as↭xs (rec _ ≤-refl)
  ... | (ps , qs , eq) = b ∷ a ∷ ps , qs , x≈b ∷ y≈a ∷ eq
  helper as           bs (trans ↭₁ ↭₂) (acc rec) with helper as bs ↭₂ (rec _ (m<n+m (steps ↭₂) (0<steps ↭₁)))
  ... | (ps , qs , eq) = helper ps qs (↭-respʳ-≋ eq ↭₁)
    (rec _ (subst (_< _) (sym (steps-respʳ eq ↭₁)) (m<m+n (steps ↭₁) (0<steps ↭₂))))

------------------------------------------------------------------------
-- filter

module _ {p} {P : Pred A p} (P? : Decidable P) (P≈ : P Respects _≈_) where

  filter⁺ : ∀ {xs ys : List A} → xs ↭ ys → filter P? xs ↭ filter P? ys
  filter⁺ (refl xs≋ys)        = refl (≋.filter⁺ P? P≈ xs≋ys)
  filter⁺ (trans xs↭zs zs↭ys) = trans (filter⁺ xs↭zs) (filter⁺ zs↭ys)
  filter⁺ {x ∷ xs} {y ∷ ys} (prep x≈y xs↭ys) with P? x | P? y
  ... | yes _  | yes _  = prep x≈y (filter⁺ xs↭ys)
  ... | yes Px | no ¬Py = contradiction (P≈ x≈y Px) ¬Py
  ... | no ¬Px | yes Py = contradiction (P≈ (≈-sym x≈y) Py) ¬Px
  ... | no  _  | no  _  = filter⁺ xs↭ys
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) with P? x | P? y
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) | no ¬Px | no ¬Py
    with P? z | P? w
  ... | _      | yes Pw = contradiction (P≈ w≈y Pw) ¬Py
  ... | yes Pz | _      = contradiction (P≈ (≈-sym x≈z) Pz) ¬Px
  ... | no _   | no  _  = filter⁺ xs↭ys
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) | no ¬Px | yes Py
    with P? z | P? w
  ... | _      | no ¬Pw = contradiction (P≈ (≈-sym w≈y) Py) ¬Pw
  ... | yes Pz | _      = contradiction (P≈ (≈-sym x≈z) Pz) ¬Px
  ... | no _   | yes _  = prep w≈y (filter⁺ xs↭ys)
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys)  | yes Px | no ¬Py
    with P? z | P? w
  ... | no ¬Pz | _      = contradiction (P≈ x≈z Px) ¬Pz
  ... | _      | yes Pw = contradiction (P≈ w≈y Pw) ¬Py
  ... | yes _  | no _   = prep x≈z (filter⁺ xs↭ys)
  filter⁺ {x ∷ w ∷ xs} {y ∷ z ∷ ys} (swap x≈z w≈y xs↭ys) | yes Px | yes Py
    with P? z | P? w
  ... | no ¬Pz | _      = contradiction (P≈ x≈z Px) ¬Pz
  ... | _      | no ¬Pw = contradiction (P≈ (≈-sym w≈y) Py) ¬Pw
  ... | yes _  | yes _  = swap x≈z w≈y (filter⁺ xs↭ys)

------------------------------------------------------------------------
-- _∷ʳ_

∷↭∷ʳ : ∀ (x : A) xs → x ∷ xs ↭ xs ∷ʳ x
∷↭∷ʳ x xs = ↭-sym (begin
  xs ++ [ x ]   ↭⟨ shift ≈-refl xs [] ⟩
  x ∷ xs ++ []  ≡⟨ Lₚ.++-identityʳ _ ⟩
  x ∷ xs        ∎)
  where open PermutationReasoning
