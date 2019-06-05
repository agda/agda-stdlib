------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutations using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Permutation.Setoid.Properties where

open import Algebra
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.List.Base as List
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
import Data.List.Relation.Binary.Equality.Setoid as Equality
import Data.List.Relation.Binary.Permutation.Setoid as Permutation
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
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
    a b ℓ p r : Level

------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

module _ (S : Setoid a ℓ) where

  open Setoid S using (_≈_) renaming (Carrier to A; trans to ≈-trans)
  open Permutation S
  open Membership S
  open Unique S using (Unique)

  All-resp-↭ : ∀ {P : Pred A p} → P Respects _≈_ → (All P) Respects _↭_
  All-resp-↭ resp (refl xs≋ys)    pxs            = {!!} --pxs
  All-resp-↭ resp (prep x≈y p)   (px ∷ pxs)      = resp x≈y px ∷ All-resp-↭ resp p pxs
  All-resp-↭ resp (swap ≈₁ ≈₂ p) (px ∷ py ∷ pxs) = resp ≈₂ py ∷ resp ≈₁ px ∷ All-resp-↭ resp p pxs
  All-resp-↭ resp (trans p₁ p₂)  pxs             = All-resp-↭ resp p₂ (All-resp-↭ resp p₁ pxs)

  Any-resp-↭ : ∀ {P : Pred A p} → P Respects _≈_ → (Any P) Respects _↭_
  Any-resp-↭ resp (refl xs≋ys) pxs                 = {!!} --pxs
  Any-resp-↭ resp (prep x≈y p) (here px)           = here (resp x≈y px)
  Any-resp-↭ resp (prep x≈y p) (there pxs)         = there (Any-resp-↭ resp p pxs)
  Any-resp-↭ resp (swap x y p) (here px)           = there (here (resp x px))
  Any-resp-↭ resp (swap x y p) (there (here px))   = here (resp y px)
  Any-resp-↭ resp (swap x y p) (there (there pxs)) = there (there (Any-resp-↭ resp p pxs))
  Any-resp-↭ resp (trans p₁ p₂) pxs                = Any-resp-↭ resp p₂ (Any-resp-↭ resp p₁ pxs)

  AllPairs-resp-↭ : ∀ {R : Rel A r} → R Respects₂ _≈_ → (AllPairs R) Respects _↭_
  AllPairs-resp-↭ _    (refl xs≋ys)     pxs             = {!!} --pxs
  AllPairs-resp-↭ resp (prep x≈y p)     (∼ ∷ pxs)       = All-resp-↭ (proj₁ resp) p {!!} ∷ AllPairs-resp-↭ resp p pxs
  AllPairs-resp-↭ resp (swap eq₁ eq₂ p) (∼₁ ∷ ~₂ ∷ pxs) = {!!} ∷ {!!} ∷ AllPairs-resp-↭ resp p pxs
  AllPairs-resp-↭ resp (trans p₁ p₂)    pxs             = AllPairs-resp-↭ resp p₂ (AllPairs-resp-↭ resp p₁ pxs)

  ∈-resp-↭ : ∀ {x} → (x ∈_) Respects _↭_
  ∈-resp-↭ = Any-resp-↭ (flip ≈-trans)

  Unique-resp-↭ : Unique Respects _↭_
  Unique-resp-↭ = AllPairs-resp-↭ ({!!} , {!!})

------------------------------------------------------------------------
-- Relationships to other predicates
------------------------------------------------------------------------

module _ (S : Setoid a ℓ) where

  open Setoid S using (_≈_) renaming (Carrier to A; sym to ≈-sym; trans to ≈-trans)
  open Permutation S
  open Equality S

  Pointwise-resp-↭ : ∀ {R : Rel A r} → (Pointwise R) Respectsʳ _↭_
  Pointwise-resp-↭ (refl x)           pw = {!!}
  Pointwise-resp-↭ (prep eq x↭y)      pw = {!!}
  Pointwise-resp-↭ (swap eq₁ eq₂ x↭y) pw = {!!}
  Pointwise-resp-↭ (trans x↭y x↭y₁)   pw = {!!}

  ↭-respʳ-≋ : _↭_ Respectsʳ _≋_
  ↭-respʳ-≋ xs≋ys               (refl zs≋xs)         = refl (≋-trans zs≋xs xs≋ys)
  ↭-respʳ-≋ (x≈y ∷ xs≋ys)       (prep eq zs↭xs)      = prep (≈-trans eq x≈y) (↭-respʳ-≋ xs≋ys zs↭xs)
  ↭-respʳ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ zs↭xs) = swap (≈-trans eq₁ w≈z) (≈-trans eq₂ x≈y) (↭-respʳ-≋ xs≋ys zs↭xs)
  ↭-respʳ-≋ xs≋ys               (trans ws↭zs zs↭xs)  = trans ws↭zs (↭-respʳ-≋ xs≋ys zs↭xs)

  ∀ {xs ys zs} → zs ≋ xs → ys ↭ xs → ys ↭ zs
  ↭-respˡ-≋ : {!_↭_ Respectsˡ _≋_!}
  ↭-respˡ-≋ xs≋ys               (refl zs≋xs)         = refl (≋-trans (≋-sym xs≋ys) zs≋xs)
  ↭-respˡ-≋ (x≈y ∷ xs≋ys)       (prep eq zs↭xs)      = prep (≈-trans (≈-sym x≈y) eq) (↭-respˡ-≋ xs≋ys zs↭xs)
  ↭-respˡ-≋ (x≈y ∷ w≈z ∷ xs≋ys) (swap eq₁ eq₂ zs↭xs) = swap (≈-trans (≈-sym x≈y) eq₁) (≈-trans (≈-sym w≈z) eq₂) (↭-respˡ-≋ xs≋ys zs↭xs)
  ↭-respˡ-≋ xs≋ys               (trans ws↭zs zs↭xs)  = trans (↭-respˡ-≋ xs≋ys ws↭zs) zs↭xs

------------------------------------------------------------------------
-- Properties of list functions
------------------------------------------------------------------------

------------------------------------------------------------------------
-- map

module _ (S : Setoid a ℓ) (T : Setoid b ℓ) where

  open Setoid S using () renaming (_≈_ to _≈₁_)
  open Setoid T using () renaming (_≈_ to _≈₂_)
  open Permutation S using () renaming (_↭_ to _↭₁_)
  open Permutation T renaming (_↭_ to _↭₂_)

  map⁺ : ∀ {f} → f Preserves _≈₁_ ⟶ _≈₂_ →
         ∀ {xs ys} → xs ↭₁ ys → map f xs ↭₂ map f ys
  map⁺ pres (refl xs≋ys)  = refl {!!}
  map⁺ pres (prep x p)    = prep (pres x) (map⁺ pres p)
  map⁺ pres (swap x y p)  = swap (pres x) (pres y) (map⁺ pres p)
  map⁺ pres (trans p₁ p₂) = trans (map⁺ pres p₁) (map⁺ pres p₂)

------------------------------------------------------------------------
-- _++_

module _ (S : Setoid a ℓ) where

  open Setoid S using (_≈_)
    renaming (Carrier to A; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
  open Equality S using (_≋_; []; _∷_; ≋-sym)
  open Permutation S
  open PermutationReasoning

  ++⁺ˡ : ∀ xs {ys zs : List A} → ys ↭ zs → xs ++ ys ↭ xs ++ zs
  ++⁺ˡ []       ys↭zs = ys↭zs
  ++⁺ˡ (x ∷ xs) ys↭zs = prep ≈-refl (++⁺ˡ xs ys↭zs)

  ++⁺ʳ : ∀ {xs ys : List A} zs → xs ↭ ys → xs ++ zs ↭ ys ++ zs
  ++⁺ʳ zs (refl ≋)      = refl {!!}
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
  inject v ws↭ys xs↭zs = trans (++⁺ˡ _ (prep ≈-refl xs↭zs)) (++⁺ʳ _ ws↭ys)

  shift : ∀ {v w} → v ≈ w → (xs ys : List A) → xs ++ [ v ] ++ ys ↭ w ∷ xs ++ ys
  shift {v} {w} v≈w []       ys = prep v≈w (refl {!!})
  shift {v} {w} v≈w (x ∷ xs) ys = begin
    x ∷ (xs ++ [ v ] ++ ys) <⟨ shift v≈w xs ys ⟩
    x ∷ w ∷ xs ++ ys        <<⟨ refl {!!} ⟩
    w ∷ x ∷ xs ++ ys        ∎

  drop-mid-≡ : ∀ {x} ws xs {ys} {zs} →
               ws ++ [ x ] ++ ys ≡ xs ++ [ x ] ++ zs →
               ws ++ ys ↭ xs ++ zs
  drop-mid-≡ []       []       eq with cong tail eq
  ... | refl = refl {!!}
  drop-mid-≡ []       (x ∷ xs) refl = shift ≈-refl xs _
  drop-mid-≡ (w ∷ ws) []       refl = ↭-sym (shift ≈-refl ws _)
  drop-mid-≡ (w ∷ ws) (x ∷ xs) eq with Lₚ.∷-injective eq
  ... | refl , eq′ = prep ≈-refl (drop-mid-≡ ws xs eq′)

  drop-mid : ∀ {x} ws xs {ys zs} →
             ws ++ [ x ] ++ ys ↭ xs ++ [ x ] ++ zs →
             ws ++ ys ↭ xs ++ zs
  drop-mid {x} ws xs p = {!!}
  {-
    drop-mid′ p ws xs refl refl
    where
    drop-mid′ : ∀ {l′ l″} → l′ ↭ l″ →
                ∀ ws xs {ys zs : List A} →
                ws ++ [ x ] ++ ys ≡ l′ →
                xs ++ [ x ] ++ zs ≡ l″ →
                ws ++ ys ↭ xs ++ zs
    drop-mid′ (refl xs≋ys)     ws           xs           refl eq   = drop-mid-≡ ws xs (≡.sym {!!})
    drop-mid′ (prep eq p)      []           []           refl refl = p
    drop-mid′ (prep eq p)      []           (x ∷ xs)     refl refl = trans p (shift eq _ _)
    drop-mid′ (prep eq p)      (w ∷ ws)     []           refl refl = trans (↭-sym (shift (≈-sym eq) _ _)) p
    drop-mid′ (prep eq p)      (w ∷ ws)     (x ∷ xs)     refl refl = prep eq (drop-mid′ p ws xs refl refl)
    drop-mid′ (swap eq₁ eq₂ p) []           []           refl refl = prep (≈-trans eq₂ eq₁) p
    drop-mid′ (swap eq₁ eq₂ p) []           (x ∷ [])     refl refl = prep eq₂ p
    drop-mid′ (swap eq₁ eq₂ p) []           (x ∷ _ ∷ xs) refl refl = prep eq₂ (trans p (shift eq₁ _ _))
    drop-mid′ (swap eq₁ eq₂ p) (w ∷ [])     []           refl refl = prep eq₁ p
    drop-mid′ (swap eq₁ eq₂ p) (w ∷ x ∷ ws) []           refl refl = prep eq₁ (trans (↭-sym (shift (≈-sym eq₂) _ _)) p)
    drop-mid′ (swap eq₁ eq₂ p) (w ∷ [])     (x ∷ [])     refl refl = prep (≈-trans eq₁ eq₂) p
    drop-mid′ (swap eq₁ eq₂ p) (w ∷ [])     (z ∷ y ∷ xs) refl refl =
      trans (prep eq₁ (trans p (shift eq₂ _ _))) (swap ≈-refl ≈-refl (refl {!!}))
    drop-mid′ (swap eq₁ eq₂ p) (y ∷ z ∷ ws) (x ∷ [])     refl refl =
      trans (trans (swap ≈-refl ≈-refl (refl {!!})) (prep ≈-refl (↭-sym (shift (≈-sym eq₁) _ _)))) (prep eq₂ p)
    drop-mid′ (swap eq₁ eq₂ p) (w ∷ y ∷ ws) (x ∷ z ∷ xs) refl refl = swap eq₁ eq₂ (drop-mid′ p _ _ refl refl)
    drop-mid′ (trans p₁ p₂) ws  xs refl refl with ∈-∃++ S (∈-resp-↭ S p₁ (∈-insert S ws ≈-refl))
    ... | (h , t , eq₃) = trans (drop-mid′ p₁ ws h refl {!!}) (drop-mid′ p₂ h xs {!!} refl)
  -}

  drop-mid′ : ∀ {u v} → u ≈ v →
              ∀ ws xs {ys zs : List A} →
              ws ++ [ u ] ++ ys ↭ xs ++ [ v ] ++ zs →
              ws ++ ys ↭ xs ++ zs
  drop-mid′ u≈v [] []            (refl (_ ∷ ys≋zs)) = refl ys≋zs
  drop-mid′ u≈v [] []            (prep eq p)        = p
  drop-mid′ u≈v [] []            (swap eq₁ eq₂ p)   = prep {!!} p --(≈-trans eq₂ eq₁) p
  drop-mid′ u≈v [] (x ∷ [])      (refl x₁)          = {!!}
  drop-mid′ u≈v [] (x ∷ x₁ ∷ xs) (refl x₂)          = {!!} -- Why is this extra case needed?
  drop-mid′ u≈v [] (x ∷ xs)      (prep eq p)        = trans p {!!} --(shift eq _ _)
  drop-mid′ u≈v [] (x ∷ [])      (swap eq₁ eq₂ p)   = prep eq₂ p
  drop-mid′ u≈v [] (x ∷ x₁ ∷ xs) (swap eq₁ eq₂ p)   = prep eq₂ (trans p {!!}) --(shift eq₁ _ _))
  drop-mid′ u≈v (x ∷ [])      [] (refl x₁)          = {!!}
  drop-mid′ u≈v (x ∷ x₁ ∷ ws) [] (refl x₂)          = {!!} -- Why is this extra case needed?
  drop-mid′ u≈v (x ∷ ws)      [] (prep eq p)        = trans {!!} p --(↭-sym (shift (≈-sym eq) _ _)) p
  drop-mid′ u≈v (x ∷ [])      [] (swap eq₁ eq₂ p)   = prep eq₁ p
  drop-mid′ u≈v (x ∷ x₁ ∷ ws) [] (swap eq₁ eq₂ p)   = prep eq₁ (trans {!!} p) --(↭-sym (shift (≈-sym eq₂) _ _)) p)
  drop-mid′ u≈v (x ∷ []) (x₁ ∷ []) p = {!!}
  drop-mid′ u≈v (x ∷ []) (x₁ ∷ x₂ ∷ xs) p = {!!}
  drop-mid′ u≈v (x ∷ x₂ ∷ ws) (x₁ ∷ []) p = {!!}
  drop-mid′ u≈v (x ∷ x₂ ∷ ws) (x₁ ∷ x₃ ∷ xs) p = {!!}
  drop-mid′ u≈v ws  xs (trans p₁ p₂) with ∈-∃++ S (∈-resp-↭ S p₁ (∈-insert S ws ≈-refl))
  ... | (h , t , w , u≈w , eq₃) = trans (drop-mid′ u≈w ws h {_} {t} {!!}) {!!} --trans (drop-mid′ ws _ {!!}) {!!} --trans (drop-mid′ ws h {!!}) (drop-mid′ h xs {!!})

{-
  drop-mid′ [] [] (refl x) = {!!}
  drop-mid′ [] (x ∷ xs) (refl z) = {!!}
  drop-mid′ (x ∷ ws) [] (refl z) = {!!}
  drop-mid′ (x ∷ ws) (x₁ ∷ xs) (refl z) = {!!} --drop-mid-≡ ws xs (≡.sym eq)
  drop-mid′ []           []           (prep eq p)      = p
  drop-mid′ []           (x ∷ xs)     (prep eq p)      = trans p (shift eq _ _)
  drop-mid′ (w ∷ ws)     []           (prep eq p)      = trans (↭-sym (shift (≈-sym eq) _ _)) p
  drop-mid′ (w ∷ ws)     (x ∷ xs)     (prep eq p)      = prep eq (drop-mid′ ws xs p)
  drop-mid′ []           []           (swap eq₁ eq₂ p) = prep (≈-trans eq₂ eq₁) p
  drop-mid′ []           (x ∷ [])     (swap eq₁ eq₂ p) = prep eq₂ p
  drop-mid′ []           (x ∷ _ ∷ xs) (swap eq₁ eq₂ p) = prep eq₂ (trans p (shift eq₁ _ _))
  drop-mid′ (w ∷ [])     []           (swap eq₁ eq₂ p) = prep eq₁ p
  drop-mid′ (w ∷ x ∷ ws) []           (swap eq₁ eq₂ p) = prep eq₁ (trans (↭-sym (shift (≈-sym eq₂) _ _)) p)
  drop-mid′ (w ∷ [])     (x ∷ [])     (swap eq₁ eq₂ p) = prep (≈-trans eq₁ eq₂) p
  drop-mid′ (w ∷ [])     (z ∷ y ∷ xs) (swap eq₁ eq₂ p) =
    trans (prep eq₁ (trans p (shift eq₂ _ _))) (swap ≈-refl ≈-refl (refl ?))
  drop-mid′ (y ∷ z ∷ ws) (x ∷ [])     (swap eq₁ eq₂ p) =
    trans (trans (swap ≈-refl ≈-refl (refl ?)) (prep ≈-refl (↭-sym (shift (≈-sym eq₁) _ _)))) (prep eq₂ p)
  drop-mid′ (w ∷ y ∷ ws) (x ∷ z ∷ xs) (swap eq₁ eq₂ p) = swap eq₁ eq₂ (drop-mid′ _ _ p)
  drop-mid′ ws  xs (trans p₁ p₂) with ∈-∃++ S (∈-resp-↭ S p₁ (∈-insert S ws ≈-refl))
  ... | (h , t , eq₃) = trans (drop-mid′ ws h {!!}) (drop-mid′ h xs {!!})
  -}
{-
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
-- sym

↭-sym-involutive : ∀ {xs ys : List A} (p : xs ↭ ys) → ↭-sym (↭-sym p) ≡ p
↭-sym-involutive refl          = refl
↭-sym-involutive (prep x ↭)    = cong (prep x) (↭-sym-involutive ↭)
↭-sym-involutive (swap x y ↭)  = cong (swap x y) (↭-sym-involutive ↭)
↭-sym-involutive (trans ↭₁ ↭₂) =
  cong₂ trans (↭-sym-involutive ↭₁) (↭-sym-involutive ↭₂)
-}
