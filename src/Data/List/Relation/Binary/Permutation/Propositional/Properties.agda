------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional.Properties where

open import Algebra.Bundles
open import Algebra.Definitions
open import Algebra.Structures
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat using (suc)
open import Data.Product using (-,_; proj₂)
open import Data.List.Base as List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
import Data.List.Properties as Lₚ
open import Data.Product using (_,_; _×_; ∃; ∃₂)
open import Function.Base using (_∘_; _⟨_⟩_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (inverse)
open import Level using (Level)
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl ; cong; cong₂; _≢_; inspect)
open import Relation.Nullary

open PermutationReasoning

private
  variable
    a b p : Level
    A : Set a
    B : Set b

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

All-resp-↭ : ∀ {P : Pred A p} → (All P) Respects _↭_
All-resp-↭ refl wit                     = wit
All-resp-↭ (prep x p) (px ∷ wit)        = px ∷ All-resp-↭ p wit
All-resp-↭ (swap x y p) (px ∷ py ∷ wit) = py ∷ px ∷ All-resp-↭ p wit
All-resp-↭ (trans p₁ p₂) wit            = All-resp-↭ p₂ (All-resp-↭ p₁ wit)

Any-resp-↭ : ∀ {P : Pred A p} → (Any P) Respects _↭_
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
  x ∷ (xs ++ [ v ] ++ ys) <⟨ shift v xs ys ⟩
  x ∷ v ∷ xs ++ ys        <<⟨ refl ⟩
  v ∷ x ∷ xs ++ ys        ∎

drop-mid-≡ : ∀ {x : A} ws xs {ys} {zs} →
             ws ++ [ x ] ++ ys ≡ xs ++ [ x ] ++ zs →
             ws ++ ys ↭ xs ++ zs
drop-mid-≡ []       []       eq   with cong tail eq
drop-mid-≡ []       []       eq   | refl = refl
drop-mid-≡ []       (x ∷ xs) refl = shift _ xs _
drop-mid-≡ (w ∷ ws) []       refl = ↭-sym (shift _ ws _)
drop-mid-≡ (w ∷ ws) (x ∷ xs) eq with Lₚ.∷-injective eq
... | refl , eq′ = prep w (drop-mid-≡ ws xs eq′)

drop-mid : ∀ {x : A} ws xs {ys zs} →
           ws ++ [ x ] ++ ys ↭ xs ++ [ x ] ++ zs →
           ws ++ ys ↭ xs ++ zs
drop-mid {A = A} {x} ws xs p = drop-mid′ p ws xs refl refl
  where
  drop-mid′ : ∀ {l′ l″ : List A} → l′ ↭ l″ →
              ∀ ws xs {ys zs} →
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

++-comm : Commutative {A = List A} _↭_ _++_
++-comm []       ys = ↭-sym (++-identityʳ ys)
++-comm (x ∷ xs) ys = begin
  x ∷ xs ++ ys         ↭⟨ prep x (++-comm xs ys) ⟩
  x ∷ ys ++ xs         ≡⟨ cong (λ v → x ∷ v ++ xs) (≡.sym (Lₚ.++-identityʳ _)) ⟩
  (x ∷ ys ++ []) ++ xs ↭⟨ ++⁺ʳ xs (↭-sym (shift x ys [])) ⟩
  (ys ++ [ x ]) ++ xs  ↭⟨ ++-assoc ys [ x ] xs ⟩
  ys ++ ([ x ] ++ xs)  ≡⟨⟩
  ys ++ (x ∷ xs)       ∎

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
   xs ++ ys  ++ zs ↭˘⟨ ++-assoc xs ys zs ⟩
  (xs ++ ys) ++ zs ↭⟨ ++⁺ʳ zs (++-comm xs ys) ⟩
  (ys ++ xs) ++ zs ↭⟨ ++-assoc ys xs zs ⟩
   ys ++ xs  ++ zs ∎

------------------------------------------------------------------------
-- _∷_

drop-∷ : ∀ {x : A} {xs ys} → x ∷ xs ↭ x ∷ ys → xs ↭ ys
drop-∷ = drop-mid [] []

------------------------------------------------------------------------
-- _∷ʳ_

∷↭∷ʳ : ∀ (x : A) xs → x ∷ xs ↭ xs ∷ʳ x
∷↭∷ʳ x xs = ↭-sym (begin
  xs ++ [ x ]   ↭⟨ shift x xs [] ⟩
  x ∷ xs ++ []  ≡⟨ Lₚ.++-identityʳ _ ⟩
  x ∷ xs        ∎)

------------------------------------------------------------------------
-- ʳ++

++↭ʳ++ : ∀ (xs ys : List A) → xs ++ ys ↭ xs ʳ++ ys
++↭ʳ++ []       ys = ↭-refl
++↭ʳ++ (x ∷ xs) ys = ↭-trans (↭-sym (shift x xs ys)) (++↭ʳ++ xs (x ∷ ys))

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
    y ∷ merge R? (x ∷ xs) ys <⟨ rec ⟩
    y ∷ x ∷ xs ++ ys         ↭˘⟨ shift y (x ∷ xs) ys ⟩
    (x ∷ xs) ++ y ∷ ys       ≡˘⟨ Lₚ.++-assoc [ x ] xs (y ∷ ys) ⟩
    x ∷ xs ++ y ∷ ys         ∎
    where open PermutationReasoning
