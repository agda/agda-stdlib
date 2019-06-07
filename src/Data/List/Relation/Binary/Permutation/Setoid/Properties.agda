------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutations using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Permutation.Setoid.Properties
  {a ℓ} (S : Setoid a ℓ)
  where

open import Algebra
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.List.Base as List
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
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
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Function using (_∘_; _⟨_⟩_; flip)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (inverse)
open import Level
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl ; cong; cong₂; subst; _≢_; inspect)

private
  variable
    b p r : Level

open Setoid S using (_≈_) renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open Permutation S
open Membership S
open Unique S using (Unique)
open Equality S using (_≋_; []; _∷_; ≋-refl; ≋-sym; ≋-trans)
open PermutationReasoning

------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

All-resp-↭ : ∀ {P : Pred A p} → P Respects _≈_ → (All P) Respects _↭_
All-resp-↭ resp refl           pxs             = pxs
All-resp-↭ resp (prep x≈y p)   (px ∷ pxs)      = resp x≈y px ∷ All-resp-↭ resp p pxs
All-resp-↭ resp (swap ≈₁ ≈₂ p) (px ∷ py ∷ pxs) = resp ≈₂ py ∷ resp ≈₁ px ∷ All-resp-↭ resp p pxs
All-resp-↭ resp (trans p₁ p₂)  pxs             = All-resp-↭ resp p₂ (All-resp-↭ resp p₁ pxs)

Any-resp-↭ : ∀ {P : Pred A p} → P Respects _≈_ → (Any P) Respects _↭_
Any-resp-↭ resp refl         pxs                 = pxs
Any-resp-↭ resp (prep x≈y p) (here px)           = here (resp x≈y px)
Any-resp-↭ resp (prep x≈y p) (there pxs)         = there (Any-resp-↭ resp p pxs)
Any-resp-↭ resp (swap x y p) (here px)           = there (here (resp x px))
Any-resp-↭ resp (swap x y p) (there (here px))   = here (resp y px)
Any-resp-↭ resp (swap x y p) (there (there pxs)) = there (there (Any-resp-↭ resp p pxs))
Any-resp-↭ resp (trans p₁ p₂) pxs                = Any-resp-↭ resp p₂ (Any-resp-↭ resp p₁ pxs)

AllPairs-resp-↭ : ∀ {R : Rel A r} → Symmetric R → R Respects₂ _≈_ → (AllPairs R) Respects _↭_
AllPairs-resp-↭ sym _    refl             pxs             = pxs
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

-- Note should be possible to simplify once ≉-respˡ from #783 is
-- merged in
Unique-resp-↭ : Unique Respects _↭_
Unique-resp-↭ = AllPairs-resp-↭ (_∘ ≈-sym)
  ((λ z≈y x≉z x≈y → x≉z (≈-trans x≈y (≈-sym z≈y))) ,
  λ x≈z x≉y z≈y → x≉y (≈-trans x≈z z≈y))

------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

≋⇒↭ : _≋_ ⇒ _↭_
≋⇒↭ []            = refl
≋⇒↭ (x≈y ∷ xs≋ys) = prep x≈y (≋⇒↭ xs≋ys)

↭-respʳ-≋ : _↭_ Respectsʳ _≋_
↭-respʳ-≋ xs≋ys               refl                 = ≋⇒↭ xs≋ys
↭-respʳ-≋ (x≈y ∷ xs≋ys)       (prep eq zs↭xs)      = prep (≈-trans eq x≈y) (↭-respʳ-≋ xs≋ys zs↭xs)
↭-respʳ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ zs↭xs) = swap (≈-trans eq₁ w≈z) (≈-trans eq₂ x≈y) (↭-respʳ-≋ xs≋ys zs↭xs)
↭-respʳ-≋ xs≋ys               (trans ws↭zs zs↭xs)  = trans ws↭zs (↭-respʳ-≋ xs≋ys zs↭xs)

↭-respˡ-≋ : _↭_ Respectsˡ _≋_
↭-respˡ-≋ xs≋ys               refl                 = ≋⇒↭ (≋-sym xs≋ys)
↭-respˡ-≋ (x≈y ∷ xs≋ys)       (prep eq zs↭xs)      = prep (≈-trans (≈-sym x≈y) eq) (↭-respˡ-≋ xs≋ys zs↭xs)
↭-respˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ zs↭xs) = swap (≈-trans (≈-sym x≈y) eq₁) (≈-trans (≈-sym w≈z) eq₂) (↭-respˡ-≋ xs≋ys zs↭xs)
↭-respˡ-≋ xs≋ys               (trans ws↭zs zs↭xs)  = trans (↭-respˡ-≋ xs≋ys ws↭zs) zs↭xs

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
  map⁺ pres refl          = refl
  map⁺ pres (prep x p)    = prep (pres x) (map⁺ pres p)
  map⁺ pres (swap x y p)  = swap (pres x) (pres y) (map⁺ pres p)
  map⁺ pres (trans p₁ p₂) = trans (map⁺ pres p₁) (map⁺ pres p₂)

------------------------------------------------------------------------
-- _++_

shift : ∀ {v w} → v ≈ w → (xs ys : List A) → xs ++ [ v ] ++ ys ↭ w ∷ xs ++ ys
shift {v} {w} v≈w []       ys = prep v≈w refl
shift {v} {w} v≈w (x ∷ xs) ys = begin
  x ∷ (xs ++ [ v ] ++ ys) <⟨ shift v≈w xs ys ⟩
  x ∷ w ∷ xs ++ ys        <<⟨ refl ⟩
  w ∷ x ∷ xs ++ ys        ∎

++⁺ˡ : ∀ xs {ys zs : List A} → ys ↭ zs → xs ++ ys ↭ xs ++ zs
++⁺ˡ []       ys↭zs = ys↭zs
++⁺ˡ (x ∷ xs) ys↭zs = prep ≈-refl (++⁺ˡ xs ys↭zs)

++⁺ʳ : ∀ {xs ys : List A} zs → xs ↭ ys → xs ++ zs ↭ ys ++ zs
++⁺ʳ zs refl          = refl
++⁺ʳ zs (prep x ↭)    = prep x (++⁺ʳ zs ↭)
++⁺ʳ zs (swap x y ↭)  = swap x y (++⁺ʳ zs ↭)
++⁺ʳ zs (trans ↭₁ ↭₂) = trans (++⁺ʳ zs ↭₁) (++⁺ʳ zs ↭₂)

++⁺ : _++_ Preserves₂ _↭_ ⟶ _↭_ ⟶ _↭_
++⁺ ws↭xs ys↭zs = trans (++⁺ʳ _ ws↭xs) (++⁺ˡ _ ys↭zs)

-- Algebraic properties

++-identityˡ : LeftIdentity _↭_ [] _++_
++-identityˡ xs = refl

++-identityʳ : RightIdentity _↭_ [] _++_
++-identityʳ xs = ↭-reflexive (Lₚ.++-identityʳ xs)

++-identity : Identity _↭_ [] _++_
++-identity = ++-identityˡ , ++-identityʳ

++-assoc : Associative _↭_ _++_
++-assoc xs ys zs = ↭-reflexive (Lₚ.++-assoc xs ys zs)

++-comm : Commutative _↭_ _++_
++-comm []       ys = ↭-sym (++-identityʳ ys)
++-comm (x ∷ xs) ys = begin
  x ∷ xs ++ ys         ↭⟨ prep ≈-refl (++-comm xs ys) ⟩
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
  { isSemigroup = ++-isSemigroup
  ; identityˡ   = ++-identityˡ
  ; comm        = ++-comm
  }

-- Packages

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

inject : ∀  (v : A) {ws xs ys zs} → ws ↭ ys → xs ↭ zs →
         ws ++ [ v ] ++ xs ↭ ys ++ [ v ] ++ zs
inject v ws↭ys xs↭zs = trans (++⁺ˡ _ (prep ≈-refl xs↭zs)) (++⁺ʳ _ ws↭ys)

shifts : ∀ xs ys {zs : List A} → xs ++ ys ++ zs ↭ ys ++ xs ++ zs
shifts xs ys {zs} = begin
   xs ++ ys  ++ zs ↭˘⟨ ++-assoc xs ys zs ⟩
  (xs ++ ys) ++ zs ↭⟨ ++⁺ʳ zs (++-comm xs ys) ⟩
  (ys ++ xs) ++ zs ↭⟨ ++-assoc ys xs zs ⟩
   ys ++ xs  ++ zs ∎

------------------------------------------------------------------------
-- _∷ʳ_

∷↭∷ʳ : ∀ (x : A) xs → x ∷ xs ↭ xs ∷ʳ x
∷↭∷ʳ x xs = ↭-sym (begin
  xs ++ [ x ]   ↭⟨ shift ≈-refl xs [] ⟩
  x ∷ xs ++ []  ≡⟨ Lₚ.++-identityʳ _ ⟩
  x ∷ xs        ∎)
  where open PermutationReasoning
