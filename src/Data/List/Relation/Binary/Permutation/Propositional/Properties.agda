------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional.Properties where

open import Algebra.Bundles
open import Algebra.Definitions
open import Algebra.Structures
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (-,_)
open import Data.List.Base as List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
import Data.List.Properties as List
open import Data.Product.Base using (_,_; _×_; ∃; ∃₂)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Function.Base using (_∘_; _⟨_⟩_; _$_)
open import Level using (Level)
open import Relation.Unary using (Pred)
open import Relation.Binary.Core using (Rel; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Definitions using (_Respects_; Decidable)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_ ; refl ; cong; cong₂; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary

import Data.List.Relation.Binary.Permutation.Setoid.Properties as Permutation

private
  variable
    a b p : Level
    A : Set a
    B : Set b
    xs ys : List A

------------------------------------------------------------------------
-- Permutations of empty and singleton lists

↭-empty-inv : ∀ {xs : List A} → xs ↭ [] → xs ≡ []
↭-empty-inv refl = refl
↭-empty-inv (trans p q) with refl ← ↭-empty-inv q = ↭-empty-inv p

¬x∷xs↭[] : ∀ {x} {xs : List A} → ¬ ((x ∷ xs) ↭ [])
¬x∷xs↭[] (trans s₁ s₂) with ↭-empty-inv s₂
... | refl = ¬x∷xs↭[] s₁

↭-singleton-inv : ∀ {x} {xs : List A} → xs ↭ [ x ] → xs ≡ [ x ]
↭-singleton-inv refl                                             = refl
↭-singleton-inv (prep _ ρ) with refl ← ↭-empty-inv ρ             = refl
↭-singleton-inv (trans ρ₁ ρ₂) with refl ← ↭-singleton-inv ρ₂ = ↭-singleton-inv ρ₁

------------------------------------------------------------------------
-- sym

↭-sym-involutive : ∀ {xs ys : List A} (p : xs ↭ ys) → ↭-sym (↭-sym p) ≡ p
↭-sym-involutive refl          = refl
↭-sym-involutive (prep x ↭)    = cong (prep x) (↭-sym-involutive ↭)
↭-sym-involutive (swap x y ↭)  = cong (swap x y) (↭-sym-involutive ↭)
↭-sym-involutive (trans ↭₁ ↭₂) =
  cong₂ trans (↭-sym-involutive ↭₁) (↭-sym-involutive ↭₂)

------------------------------------------------------------------------
-- Relationships to other predicates

module _ {P : Pred A p} where

  All-resp-↭ : (All P) Respects _↭_
  All-resp-↭ refl wit                     = wit
  All-resp-↭ (prep x p) (px ∷ wit)        = px ∷ All-resp-↭ p wit
  All-resp-↭ (swap x y p) (px ∷ py ∷ wit) = py ∷ px ∷ All-resp-↭ p wit
  All-resp-↭ (trans p₁ p₂) wit            = All-resp-↭ p₂ (All-resp-↭ p₁ wit)

  Any-resp-↭ : (Any P) Respects _↭_
  Any-resp-↭ refl         wit                 = wit
  Any-resp-↭ (prep x p)   (here px)           = here px
  Any-resp-↭ (prep x p)   (there wit)         = there (Any-resp-↭ p wit)
  Any-resp-↭ (swap x y p) (here px)           = there (here px)
  Any-resp-↭ (swap x y p) (there (here px))   = here px
  Any-resp-↭ (swap x y p) (there (there wit)) = there (there (Any-resp-↭ p wit))
  Any-resp-↭ (trans p p₁) wit                 = Any-resp-↭ p₁ (Any-resp-↭ p wit)

  Any-resp-[σ⁻¹∘σ] : ∀ {xs ys} (σ : xs ↭ ys) (ix : Any P xs) →
                     Any-resp-↭ (trans σ (↭-sym σ)) ix ≡ ix
  Any-resp-[σ⁻¹∘σ] refl          ix               = refl
  Any-resp-[σ⁻¹∘σ] (prep _ _)    (here _)         = refl
  Any-resp-[σ⁻¹∘σ] (swap _ _ _)  (here _)         = refl
  Any-resp-[σ⁻¹∘σ] (swap _ _ _)  (there (here _)) = refl
  Any-resp-[σ⁻¹∘σ] (trans σ₁ σ₂) ix
    rewrite Any-resp-[σ⁻¹∘σ] σ₂ (Any-resp-↭ σ₁ ix)
    rewrite Any-resp-[σ⁻¹∘σ] σ₁ ix
    = refl
  Any-resp-[σ⁻¹∘σ] (prep _ σ)    (there ix)
    rewrite Any-resp-[σ⁻¹∘σ] σ ix
    = refl
  Any-resp-[σ⁻¹∘σ] (swap _ _ σ)  (there (there ix))
    rewrite Any-resp-[σ⁻¹∘σ] σ ix
    = refl

  Any-resp-[σ∘σ⁻¹] : ∀ {xs ys} (σ : xs ↭ ys) (iy : Any P ys) →
                     Any-resp-↭ (trans (↭-sym σ) σ) iy ≡ iy
  Any-resp-[σ∘σ⁻¹] p
    with res ← Any-resp-[σ⁻¹∘σ] (↭-sym p)
    rewrite ↭-sym-involutive p
    = res

∈-resp-↭ : ∀ {x : A} → (x ∈_) Respects _↭_
∈-resp-↭ = Any-resp-↭

∈-resp-[σ⁻¹∘σ] : ∀ {xs ys} {x : A} (σ : xs ↭ ys) (ix : x ∈ xs) →
                 ∈-resp-↭ (trans σ (↭-sym σ)) ix ≡ ix
∈-resp-[σ⁻¹∘σ] = Any-resp-[σ⁻¹∘σ]

∈-resp-[σ∘σ⁻¹] : ∀ {xs ys} {y : A} (σ : xs ↭ ys) (iy : y ∈ ys) →
                 ∈-resp-↭ (trans (↭-sym σ) σ) iy ≡ iy
∈-resp-[σ∘σ⁻¹] = Any-resp-[σ∘σ⁻¹]

------------------------------------------------------------------------
-- map

module _ (f : A → B) where

  map⁺ : ∀ {xs ys} → xs ↭ ys → map f xs ↭ map f ys
  map⁺ refl          = refl
  map⁺ (prep x p)    = prep _ (map⁺ p)
  map⁺ (swap x y p)  = swap _ _ (map⁺ p)
  map⁺ (trans p₁ p₂) = trans (map⁺ p₁) (map⁺ p₂)

  -- permutations preserve 'being a mapped list'
  ↭-map-inv : ∀ {xs ys} → map f xs ↭ ys → ∃ λ ys′ → ys ≡ map f ys′ × xs ↭ ys′
  ↭-map-inv {[]}     ρ                                                  = -, ↭-empty-inv (↭-sym ρ) , ↭-refl
  ↭-map-inv {x ∷ []} ρ                                                  = -, ↭-singleton-inv (↭-sym ρ) , ↭-refl
  ↭-map-inv {_ ∷ _ ∷ _} refl                                            = -, refl , ↭-refl
  ↭-map-inv {_ ∷ _ ∷ _} (prep _ ρ)    with _ , refl , ρ′ ← ↭-map-inv ρ  = -, refl , prep _ ρ′
  ↭-map-inv {_ ∷ _ ∷ _} (swap _ _ ρ)  with _ , refl , ρ′ ← ↭-map-inv ρ  = -, refl , swap _ _ ρ′
  ↭-map-inv {_ ∷ _ ∷ _} (trans ρ₁ ρ₂) with _ , refl , ρ₃ ← ↭-map-inv ρ₁
                                      with _ , refl , ρ₄ ← ↭-map-inv ρ₂ = -, refl , trans ρ₃ ρ₄

------------------------------------------------------------------------
-- length

↭-length : ∀ {xs ys : List A} → xs ↭ ys → length xs ≡ length ys
↭-length refl            = refl
↭-length (prep x lr)     = cong suc (↭-length lr)
↭-length (swap x y lr)   = cong (suc ∘ suc) (↭-length lr)
↭-length (trans lr₁ lr₂) = ≡.trans (↭-length lr₁) (↭-length lr₂)

------------------------------------------------------------------------
-- _++_

++⁺ˡ : ∀ xs {ys zs : List A} → ys ↭ zs → xs ++ ys ↭ xs ++ zs
++⁺ˡ []       ys↭zs = ys↭zs
++⁺ˡ (x ∷ xs) ys↭zs = prep x (++⁺ˡ xs ys↭zs)

++⁺ʳ : ∀ {xs ys : List A} zs → xs ↭ ys → xs ++ zs ↭ ys ++ zs
++⁺ʳ zs refl          = refl
++⁺ʳ zs (prep x ↭)    = prep x (++⁺ʳ zs ↭)
++⁺ʳ zs (swap x y ↭)  = swap x y (++⁺ʳ zs ↭)
++⁺ʳ zs (trans ↭₁ ↭₂) = trans (++⁺ʳ zs ↭₁) (++⁺ʳ zs ↭₂)

++⁺ : _++_ {A = A} Preserves₂ _↭_ ⟶ _↭_ ⟶ _↭_
++⁺ ws↭xs ys↭zs = trans (++⁺ʳ _ ws↭xs) (++⁺ˡ _ ys↭zs)

-- Some useful lemmas

zoom : ∀ h {t xs ys : List A} → xs ↭ ys → h ++ xs ++ t ↭ h ++ ys ++ t
zoom h {t} = ++⁺ˡ h ∘ ++⁺ʳ t

inject : ∀  (v : A) {ws xs ys zs} → ws ↭ ys → xs ↭ zs →
        ws ++ [ v ] ++ xs ↭ ys ++ [ v ] ++ zs
inject v ws↭ys xs↭zs = trans (++⁺ˡ _ (prep v xs↭zs)) (++⁺ʳ _ ws↭ys)

shift : ∀ v (xs ys : List A) → xs ++ [ v ] ++ ys ↭ v ∷ xs ++ ys
shift v []       ys = refl
shift v (x ∷ xs) ys = begin
  x ∷ (xs ++ [ v ] ++ ys) ↭⟨ prep _ (shift v xs ys) ⟩
  x ∷ v ∷ xs ++ ys        ↭⟨ swap _ _ refl ⟩
  v ∷ x ∷ xs ++ ys        ∎
  where open PermutationReasoning

drop-mid-≡ : ∀ {x : A} ws xs {ys} {zs} →
             ws ++ [ x ] ++ ys ≡ xs ++ [ x ] ++ zs →
             ws ++ ys ↭ xs ++ zs
drop-mid-≡ []       []       eq
  with refl ← List.∷-injectiveʳ eq = refl
drop-mid-≡ []       (x ∷ xs) refl = shift _ xs _
drop-mid-≡ (w ∷ ws) []       refl = ↭-sym (shift _ ws _)
drop-mid-≡ (w ∷ ws) (x ∷ xs) eq
  with refl , eq′ ← List.∷-injective eq = prep w (drop-mid-≡ ws xs eq′)

drop-mid : ∀ {x : A} ws xs {ys zs} →
           ws ++ [ x ] ++ ys ↭ xs ++ [ x ] ++ zs →
           ws ++ ys ↭ xs ++ zs
drop-mid ws xs p = drop-mid′ p ws xs refl refl
  where
  drop-mid′ : ∀ {as bs} → as ↭ bs →
              ∀ {x : A} ws xs {ys zs} →
              as ≡ ws ++ [ x ] ++ ys →
              bs ≡ xs ++ [ x ] ++ zs →
              ws ++ ys ↭ xs ++ zs
  drop-mid′ refl ws xs refl eq = drop-mid-≡ ws xs eq
  drop-mid′ (trans p q) ws  xs refl refl
    with h , t , refl ← ∈-∃++ (∈-resp-↭ p (∈-insert ws))
    = trans (drop-mid ws h p) (drop-mid h xs q)
  drop-mid′ (prep x p)   []           []           refl eq
    with refl ← List.∷-injectiveʳ eq  = p
  drop-mid′ (prep x p)   []           (x ∷ xs)     refl refl = trans p (shift _ _ _)
  drop-mid′ (prep x p)   (w ∷ ws)     []           refl refl = trans (↭-sym (shift _ _ _)) p
  drop-mid′ (prep x p)   (w ∷ ws)     (x ∷ xs)     refl refl = prep _ (drop-mid ws xs p)
  drop-mid′ (swap y z p) []           []           refl refl = prep _ p
  drop-mid′ (swap y z p) []           (x ∷ [])     refl eq
    with refl , eq′ ← List.∷-injective eq
    with refl ← List.∷-injectiveʳ eq′ = prep _ p
  drop-mid′ (swap y z p) []           (x ∷ _ ∷ xs) refl refl = prep _ (trans p (shift _ _ _))
  drop-mid′ (swap y z p) (w ∷ [])     []           refl eq
    with refl ← List.∷-injectiveʳ eq  = prep _ p
  drop-mid′ (swap y z p) (w ∷ x ∷ ws) []           refl refl = prep _ (trans (↭-sym (shift _ _ _)) p)
  drop-mid′ (swap y y p) (y ∷ [])     (y ∷ [])     refl refl = prep _ p
  drop-mid′ (swap y z p) (y ∷ [])     (z ∷ y ∷ xs) refl refl = begin
      _ ∷ _             ↭⟨ prep _ p ⟩
      _ ∷ (xs ++ _ ∷ _) ↭⟨ prep _ (shift _ _ _) ⟩
      _ ∷ _ ∷ xs ++ _   ↭⟨ swap _ _ refl ⟩
      _ ∷ _ ∷ xs ++ _   ∎
      where open PermutationReasoning
  drop-mid′ (swap y z p) (y ∷ z ∷ ws) (z ∷ [])     refl refl = begin
      _ ∷ _ ∷ ws ++ _   ↭⟨ swap _ _ refl ⟩
      _ ∷ (_ ∷ ws ++ _) ↭⟨ prep _ (shift _ _ _) ⟨
      _ ∷ (ws ++ _ ∷ _) ↭⟨ prep _ p ⟩
      _ ∷ _             ∎
      where open PermutationReasoning
  drop-mid′ (swap y z p) (y ∷ z ∷ ws) (z ∷ y ∷ xs) refl refl = swap y z (drop-mid _ _ p)


-- Algebraic properties

++-identityˡ : LeftIdentity {A = List A} _↭_ [] _++_
++-identityˡ xs = refl

++-identityʳ : RightIdentity {A = List A} _↭_ [] _++_
++-identityʳ xs = ↭-reflexive (List.++-identityʳ xs)

++-identity : Identity {A = List A} _↭_ [] _++_
++-identity = ++-identityˡ , ++-identityʳ

++-assoc : Associative {A = List A} _↭_ _++_
++-assoc xs ys zs = ↭-reflexive (List.++-assoc xs ys zs)

++-comm : Commutative {A = List A} _↭_ _++_
++-comm []       ys = ↭-sym (++-identityʳ ys)
++-comm (x ∷ xs) ys = begin
  x ∷ xs ++ ys   ↭⟨ prep _ (++-comm xs ys) ⟩
  x ∷ ys ++ xs   ↭⟨ shift x ys xs ⟨
  ys ++ (x ∷ xs) ∎
  where open PermutationReasoning

++-isMagma : IsMagma {A = List A} _↭_ _++_
++-isMagma = record
  { isEquivalence = ↭-isEquivalence
  ; ∙-cong        = ++⁺
  }

++-isSemigroup : IsSemigroup {A = List A} _↭_ _++_
++-isSemigroup = record
  { isMagma = ++-isMagma
  ; assoc   = ++-assoc
  }

++-isMonoid : IsMonoid {A = List A} _↭_ _++_ []
++-isMonoid = record
  { isSemigroup = ++-isSemigroup
  ; identity    = ++-identity
  }

++-isCommutativeMonoid : IsCommutativeMonoid {A = List A} _↭_ _++_ []
++-isCommutativeMonoid = record
  { isMonoid = ++-isMonoid
  ; comm     = ++-comm
  }

module _ {a} {A : Set a} where

  ++-magma : Magma _ _
  ++-magma = record
    { isMagma = ++-isMagma {A = A}
    }

  ++-semigroup : Semigroup a _
  ++-semigroup = record
    { isSemigroup = ++-isSemigroup {A = A}
    }

  ++-monoid : Monoid a _
  ++-monoid = record
    { isMonoid = ++-isMonoid {A = A}
    }

  ++-commutativeMonoid : CommutativeMonoid _ _
  ++-commutativeMonoid = record
    { isCommutativeMonoid = ++-isCommutativeMonoid {A = A}
    }

-- Another useful lemma

shifts : ∀ xs ys {zs : List A} → xs ++ ys ++ zs ↭ ys ++ xs ++ zs
shifts xs ys {zs} = begin
   xs ++ ys  ++ zs ↭⟨ ++-assoc xs ys zs ⟨
  (xs ++ ys) ++ zs ↭⟨ ++⁺ʳ zs (++-comm xs ys) ⟩
  (ys ++ xs) ++ zs ↭⟨ ++-assoc ys xs zs ⟩
   ys ++ xs  ++ zs ∎
   where open PermutationReasoning

------------------------------------------------------------------------
-- _∷_

drop-∷ : ∀ {x : A} {xs ys} → x ∷ xs ↭ x ∷ ys → xs ↭ ys
drop-∷ = drop-mid [] []

------------------------------------------------------------------------
-- _∷ʳ_

∷↭∷ʳ : ∀ (x : A) xs → x ∷ xs ↭ xs ∷ʳ x
∷↭∷ʳ x xs = ↭-sym (begin
  xs ++ [ x ]   ↭⟨ shift x xs [] ⟩
  x ∷ xs ++ []  ≡⟨ List.++-identityʳ _ ⟩
  x ∷ xs        ∎)
  where open PermutationReasoning

------------------------------------------------------------------------
-- ʳ++

++↭ʳ++ : ∀ (xs ys : List A) → xs ++ ys ↭ xs ʳ++ ys
++↭ʳ++ []       ys = ↭-refl
++↭ʳ++ (x ∷ xs) ys = ↭-trans (↭-sym (shift x xs ys)) (++↭ʳ++ xs (x ∷ ys))

------------------------------------------------------------------------
-- reverse

↭-reverse : (xs : List A) → reverse xs ↭ xs
↭-reverse [] = ↭-refl
↭-reverse (x ∷ xs) = begin
  reverse (x ∷ xs) ≡⟨ List.unfold-reverse x xs ⟩
  reverse xs ∷ʳ x ↭⟨ ∷↭∷ʳ x (reverse xs) ⟨
  x ∷ reverse xs   ↭⟨ prep x (↭-reverse xs) ⟩
  x ∷ xs ∎
  where open PermutationReasoning

------------------------------------------------------------------------
-- merge

module _ {ℓ} {R : Rel A ℓ} (R? : Decidable R) where

  merge-↭ : ∀ xs ys → merge R? xs ys ↭ xs ++ ys
  merge-↭ []       []       = ↭-refl
  merge-↭ []       (y ∷ ys) = ↭-refl
  merge-↭ (x ∷ xs) []       = ↭-sym (++-identityʳ (x ∷ xs))
  merge-↭ (x ∷ xs) (y ∷ ys)
    with does (R? x y) | merge-↭ xs (y ∷ ys) | merge-↭ (x ∷ xs) ys
  ... | true  | rec | _   = prep x rec
  ... | false | _   | rec = begin
    y ∷ merge R? (x ∷ xs) ys ↭⟨ prep _ rec ⟩
    y ∷ x ∷ xs ++ ys         ↭⟨ shift y (x ∷ xs) ys ⟨
    (x ∷ xs) ++ y ∷ ys       ≡⟨ List.++-assoc [ x ] xs (y ∷ ys) ⟨
    x ∷ xs ++ y ∷ ys         ∎
    where open PermutationReasoning

------------------------------------------------------------------------
-- sum

sum-↭ : sum Preserves _↭_ ⟶ _≡_
sum-↭ p = foldr-commMonoid ℕ-+-0.isCommutativeMonoid (↭⇒↭ₛ p)
  where
  module ℕ-+-0 = CommutativeMonoid ℕ.+-0-commutativeMonoid
  open Permutation ℕ-+-0.setoid

------------------------------------------------------------------------
-- product

product-↭ : product Preserves _↭_ ⟶ _≡_
product-↭ p = foldr-commMonoid ℕ-*-1.isCommutativeMonoid (↭⇒↭ₛ p)
  where
  module ℕ-*-1 = CommutativeMonoid ℕ.*-1-commutativeMonoid
  open Permutation ℕ-*-1.setoid

------------------------------------------------------------------------
-- catMaybes

catMaybes-↭ : xs ↭ ys → catMaybes xs ↭ catMaybes ys
catMaybes-↭ refl                         = refl
catMaybes-↭ (trans xs↭ ↭ys)              = trans (catMaybes-↭ xs↭) (catMaybes-↭ ↭ys)
catMaybes-↭ (prep nothing  xs↭)          = catMaybes-↭ xs↭
catMaybes-↭ (prep (just x) xs↭)          = prep x $ catMaybes-↭ xs↭
catMaybes-↭ (swap nothing  nothing  xs↭) = catMaybes-↭ xs↭
catMaybes-↭ (swap nothing  (just y) xs↭) = prep y $ catMaybes-↭ xs↭
catMaybes-↭ (swap (just x) nothing  xs↭) = prep x $ catMaybes-↭ xs↭
catMaybes-↭ (swap (just x) (just y) xs↭) = swap x y $ catMaybes-↭ xs↭

------------------------------------------------------------------------
-- mapMaybe

mapMaybe-↭ : (f : A → Maybe B) → xs ↭ ys → mapMaybe f xs ↭ mapMaybe f ys
mapMaybe-↭ f = catMaybes-↭ ∘ map⁺ f
