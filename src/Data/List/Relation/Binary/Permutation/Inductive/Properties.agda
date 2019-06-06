------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Inductive.Properties where

open import Algebra
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.List.Base as List
open import Data.List.Relation.Binary.Permutation.Inductive
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.BagAndSetEquality
  using (bag; _∼[_]_; empty-unique; drop-cons; commutativeMonoid)
import Data.List.Properties as Lₚ
open import Data.Product using (_,_; _×_; ∃; ∃₂)
open import Function using (_∘_; _⟨_⟩_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (inverse)
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl ; cong; cong₂; _≢_; inspect)

open PermutationReasoning

------------------------------------------------------------------------
-- sym

module _ {a} {A : Set a} where

  ↭-sym-involutive : ∀ {xs ys : List A} (p : xs ↭ ys) → ↭-sym (↭-sym p) ≡ p
  ↭-sym-involutive refl          = refl
  ↭-sym-involutive (prep x ↭)    = cong (prep x) (↭-sym-involutive ↭)
  ↭-sym-involutive (swap x y ↭)  = cong (swap x y) (↭-sym-involutive ↭)
  ↭-sym-involutive (trans ↭₁ ↭₂) =
    cong₂ trans (↭-sym-involutive ↭₁) (↭-sym-involutive ↭₂)

------------------------------------------------------------------------
-- Relationships to other predicates

module _ {a} {A : Set a} where

  All-resp-↭ : ∀ {ℓ} {P : Pred A ℓ} → (All P) Respects _↭_
  All-resp-↭ refl wit                     = wit
  All-resp-↭ (prep x p) (px ∷ wit)        = px ∷ All-resp-↭ p wit
  All-resp-↭ (swap x y p) (px ∷ py ∷ wit) = py ∷ px ∷ All-resp-↭ p wit
  All-resp-↭ (trans p₁ p₂) wit            = All-resp-↭ p₂ (All-resp-↭ p₁ wit)

  Any-resp-↭ : ∀ {ℓ} {P : Pred A ℓ} → (Any P) Respects _↭_
  Any-resp-↭ refl         wit                 = wit
  Any-resp-↭ (prep x p)   (here px)           = here px
  Any-resp-↭ (prep x p)   (there wit)         = there (Any-resp-↭ p wit)
  Any-resp-↭ (swap x y p) (here px)           = there (here px)
  Any-resp-↭ (swap x y p) (there (here px))   = here px
  Any-resp-↭ (swap x y p) (there (there wit)) = there (there (Any-resp-↭ p wit))
  Any-resp-↭ (trans p p₁) wit                 = Any-resp-↭ p₁ (Any-resp-↭ p wit)

  ∈-resp-↭ : ∀ {x : A} → (x ∈_) Respects _↭_
  ∈-resp-↭ = Any-resp-↭

------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} (f : A → B) where

  map⁺ : ∀ {xs ys} → xs ↭ ys → map f xs ↭ map f ys
  map⁺ refl          = refl
  map⁺ (prep x p)    = prep _ (map⁺ p)
  map⁺ (swap x y p)  = swap _ _ (map⁺ p)
  map⁺ (trans p₁ p₂) = trans (map⁺ p₁) (map⁺ p₂)

------------------------------------------------------------------------
-- _++_

module _ {a} {A : Set a} where


  ++⁺ˡ : ∀ xs {ys zs : List A} → ys ↭ zs → xs ++ ys ↭ xs ++ zs
  ++⁺ˡ []       ys↭zs = ys↭zs
  ++⁺ˡ (x ∷ xs) ys↭zs = prep x (++⁺ˡ xs ys↭zs)

  ++⁺ʳ : ∀ {xs ys : List A} zs → xs ↭ ys → xs ++ zs ↭ ys ++ zs
  ++⁺ʳ zs refl          = refl
  ++⁺ʳ zs (prep x ↭)    = prep x (++⁺ʳ zs ↭)
  ++⁺ʳ zs (swap x y ↭)  = swap x y (++⁺ʳ zs ↭)
  ++⁺ʳ zs (trans ↭₁ ↭₂) = trans (++⁺ʳ zs ↭₁) (++⁺ʳ zs ↭₂)

  ++⁺ : _++_ Preserves₂ _↭_ ⟶ _↭_ ⟶ _↭_
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
    x ∷ (xs ++ [ v ] ++ ys) <⟨ shift v xs ys ⟩
    x ∷ v ∷ xs ++ ys        <<⟨ refl ⟩
    v ∷ x ∷ xs ++ ys        ∎

  drop-mid-≡ : ∀ {x} ws xs {ys} {zs} →
               ws ++ [ x ] ++ ys ≡ xs ++ [ x ] ++ zs →
               ws ++ ys ↭ xs ++ zs
  drop-mid-≡ []       []       eq   with cong tail eq
  drop-mid-≡ []       []       eq   | refl = refl
  drop-mid-≡ []       (x ∷ xs) refl = shift _ xs _
  drop-mid-≡ (w ∷ ws) []       refl = ↭-sym (shift _ ws _)
  drop-mid-≡ (w ∷ ws) (x ∷ xs) eq with Lₚ.∷-injective eq
  ... | refl , eq′ = prep w (drop-mid-≡ ws xs eq′)

  drop-mid : ∀ {x} ws xs {ys zs} →
             ws ++ [ x ] ++ ys ↭ xs ++ [ x ] ++ zs →
             ws ++ ys ↭ xs ++ zs
  drop-mid {x} ws xs p = drop-mid′ p ws xs refl refl
    where
    drop-mid′ : ∀ {l′ l″ : List A} → l′ ↭ l″ →
                ∀ ws xs {ys zs : List A} →
                ws ++ [ x ] ++ ys ≡ l′ →
                xs ++ [ x ] ++ zs ≡ l″ →
                ws ++ ys ↭ xs ++ zs
    drop-mid′ refl         ws           xs           refl eq   = drop-mid-≡ ws xs (≡.sym eq)
    drop-mid′ (prep x p)   []           []           refl eq   with cong tail eq
    drop-mid′ (prep x p)   []           []           refl eq   | refl = p
    drop-mid′ (prep x p)   []           (x ∷ xs)     refl refl = trans p (shift _ _ _)
    drop-mid′ (prep x p)   (w ∷ ws)     []           refl refl = trans (↭-sym (shift _ _ _)) p
    drop-mid′ (prep x p)   (w ∷ ws)     (x ∷ xs)     refl refl = prep _ (drop-mid′ p ws xs refl refl)
    drop-mid′ (swap y z p) []           []           refl refl = prep _ p
    drop-mid′ (swap y z p) []           (x ∷ [])     refl eq   with cong {B = List _}
                                                                         (λ { (x ∷ _ ∷ xs) → x ∷ xs
                                                                            ; _            → []
                                                                            })
                                                                         eq
    drop-mid′ (swap y z p) []           (x ∷ [])     refl eq   | refl = prep _ p
    drop-mid′ (swap y z p) []           (x ∷ _ ∷ xs) refl refl = prep _ (trans p (shift _ _ _))
    drop-mid′ (swap y z p) (w ∷ [])     []           refl eq   with cong tail eq
    drop-mid′ (swap y z p) (w ∷ [])     []           refl eq   | refl = prep _ p
    drop-mid′ (swap y z p) (w ∷ x ∷ ws) []           refl refl = prep _ (trans (↭-sym (shift _ _ _)) p)
    drop-mid′ (swap y y p) (y ∷ [])     (y ∷ [])     refl refl = prep _ p
    drop-mid′ (swap y z p) (y ∷ [])     (z ∷ y ∷ xs) refl refl = begin
        _ ∷ _             <⟨ p ⟩
        _ ∷ (xs ++ _ ∷ _) <⟨ shift _ _ _ ⟩
        _ ∷ _ ∷ xs ++ _   <<⟨ refl ⟩
        _ ∷ _ ∷ xs ++ _   ∎
    drop-mid′ (swap y z p) (y ∷ z ∷ ws) (z ∷ [])     refl refl = begin
        _ ∷ _ ∷ ws ++ _   <<⟨ refl ⟩
        _ ∷ (_ ∷ ws ++ _) <⟨ ↭-sym (shift _ _ _) ⟩
        _ ∷ (ws ++ _ ∷ _) <⟨ p ⟩
        _ ∷ _             ∎
    drop-mid′ (swap y z p) (y ∷ z ∷ ws) (z ∷ y ∷ xs) refl refl = swap y z (drop-mid′ p _ _ refl refl)
    drop-mid′ (trans p₁ p₂) ws  xs refl refl with ∈-∃++ (∈-resp-↭ p₁ (∈-insert ws))
    ... | (h , t , refl) = trans (drop-mid′ p₁ ws h refl refl) (drop-mid′ p₂ h xs refl refl)

  -- Algebraic properties

  ++-identityˡ : LeftIdentity {A = List A} _↭_ [] _++_
  ++-identityˡ xs = refl

  ++-identityʳ : RightIdentity {A = List A} _↭_ [] _++_
  ++-identityʳ xs = ↭-reflexive (Lₚ.++-identityʳ xs)

  ++-identity : Identity {A = List A} _↭_ [] _++_
  ++-identity = ++-identityˡ , ++-identityʳ

  ++-assoc : Associative {A = List A} _↭_ _++_
  ++-assoc xs ys zs = ↭-reflexive (Lₚ.++-assoc xs ys zs)

  ++-comm : Commutative _↭_ _++_
  ++-comm []       ys = ↭-sym (++-identityʳ ys)
  ++-comm (x ∷ xs) ys = begin
    x ∷ xs ++ ys         ↭⟨ prep x (++-comm xs ys) ⟩
    x ∷ ys ++ xs         ≡⟨ cong (λ v → x ∷ v ++ xs) (≡.sym (Lₚ.++-identityʳ _)) ⟩
    (x ∷ ys ++ []) ++ xs ↭⟨ ++⁺ʳ xs (↭-sym (shift x ys [])) ⟩
    (ys ++ [ x ]) ++ xs  ↭⟨ ++-assoc ys [ x ] xs ⟩
    ys ++ ([ x ] ++ xs)  ≡⟨⟩
    ys ++ (x ∷ xs)       ∎

  ++-isMagma : IsMagma _↭_ _++_
  ++-isMagma = record
    { isEquivalence = ↭-isEquivalence
    ; ∙-cong        = ++⁺
    }

  ++-magma : Magma _ _
  ++-magma = record
    { isMagma = ++-isMagma
    }

  ++-isSemigroup : IsSemigroup _↭_ _++_
  ++-isSemigroup = record
    { isMagma = ++-isMagma
    ; assoc   = ++-assoc
    }

  ++-semigroup : Semigroup a _
  ++-semigroup = record
    { isSemigroup = ++-isSemigroup
    }

  ++-isMonoid : IsMonoid _↭_ _++_ []
  ++-isMonoid = record
    { isSemigroup = ++-isSemigroup
    ; identity    = ++-identity
    }

  ++-monoid : Monoid a _
  ++-monoid = record
    { isMonoid = ++-isMonoid
    }

  ++-isCommutativeMonoid : IsCommutativeMonoid _↭_ _++_ []
  ++-isCommutativeMonoid = record
    { isSemigroup = ++-isSemigroup
    ; identityˡ   = ++-identityˡ
    ; comm        = ++-comm
    }

  ++-commutativeMonoid : CommutativeMonoid _ _
  ++-commutativeMonoid = record
    { isCommutativeMonoid = ++-isCommutativeMonoid
    }

  -- Another useful lemma

  shifts : ∀ xs ys {zs : List A} → xs ++ ys ++ zs ↭ ys ++ xs ++ zs
  shifts xs ys {zs} = begin
     xs ++ ys  ++ zs ↭˘⟨ ++-assoc xs ys zs ⟩
    (xs ++ ys) ++ zs ↭⟨ ++⁺ʳ zs (++-comm xs ys) ⟩
    (ys ++ xs) ++ zs ↭⟨ ++-assoc ys xs zs ⟩
     ys ++ xs  ++ zs ∎

------------------------------------------------------------------------
-- _∷_

module _ {a} {A : Set a} where

  drop-∷ : ∀ {x : A} {xs ys} → x ∷ xs ↭ x ∷ ys → xs ↭ ys
  drop-∷ = drop-mid [] []

------------------------------------------------------------------------
-- _∷ʳ_

module _ {a} {A : Set a} where

  ∷↭∷ʳ : ∀ (x : A) xs → x ∷ xs ↭ xs ∷ʳ x
  ∷↭∷ʳ x xs = ↭-sym (begin
    xs ++ [ x ]   ↭⟨ shift x xs [] ⟩
    x ∷ xs ++ []  ≡⟨ Lₚ.++-identityʳ _ ⟩
    x ∷ xs        ∎)

------------------------------------------------------------------------
-- Relationships to other relations

module _ {a} {A : Set a} where

  ↭⇒∼bag : _↭_ ⇒ _∼[ bag ]_
  ↭⇒∼bag xs↭ys {v} = inverse (to xs↭ys) (from xs↭ys) (from∘to xs↭ys) (to∘from xs↭ys)
    where
    to : ∀ {xs ys} → xs ↭ ys → v ∈ xs → v ∈ ys
    to xs↭ys = Any-resp-↭ {A = A} xs↭ys

    from : ∀ {xs ys} → xs ↭ ys → v ∈ ys → v ∈ xs
    from xs↭ys = Any-resp-↭ (↭-sym xs↭ys)

    from∘to : ∀ {xs ys} (p : xs ↭ ys) (q : v ∈ xs) → from p (to p q) ≡ q
    from∘to refl          v∈xs                 = refl
    from∘to (prep _ _)    (here refl)          = refl
    from∘to (prep _ p)    (there v∈xs)         = cong there (from∘to p v∈xs)
    from∘to (swap x y p)  (here refl)          = refl
    from∘to (swap x y p)  (there (here refl))  = refl
    from∘to (swap x y p)  (there (there v∈xs)) = cong (there ∘ there) (from∘to p v∈xs)
    from∘to (trans p₁ p₂) v∈xs
      rewrite from∘to p₂ (Any-resp-↭ p₁ v∈xs)
            | from∘to p₁ v∈xs                  = refl

    to∘from : ∀ {xs ys} (p : xs ↭ ys) (q : v ∈ ys) → to p (from p q) ≡ q
    to∘from p with from∘to (↭-sym p)
    ... | res rewrite ↭-sym-involutive p = res

  ∼bag⇒↭ : _∼[ bag ]_ ⇒ _↭_
  ∼bag⇒↭ {[]} eq with empty-unique (Inv.sym eq)
  ... | refl = refl
  ∼bag⇒↭ {x ∷ xs} eq with ∈-∃++ (to ⟨$⟩ (here ≡.refl))
    where open Inv.Inverse (eq {x})
  ... | zs₁ , zs₂ , p rewrite p = begin
    x ∷ xs           <⟨ ∼bag⇒↭ (drop-cons (Inv._∘_ (comm zs₁ (x ∷ zs₂)) eq)) ⟩
    x ∷ (zs₂ ++ zs₁) <⟨ ++-comm zs₂ zs₁ ⟩
    x ∷ (zs₁ ++ zs₂) ↭˘⟨ shift x zs₁ zs₂ ⟩
    zs₁ ++ x ∷ zs₂   ∎
    where open CommutativeMonoid (commutativeMonoid bag A)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

↭⇒~bag = ↭⇒∼bag
{-# WARNING_ON_USAGE ↭⇒~bag
"Warning: ↭⇒~bag was deprecated in v1.0.
Please use ? instead (now typed with '\\sim' rather than '~')."
#-}

~bag⇒↭ = ∼bag⇒↭
{-# WARNING_ON_USAGE ~bag⇒↭
"Warning: ~bag⇒↭ was deprecated in v1.0.
Please use ? instead (now typed with '\\sim' rather than '~')."
#-}
