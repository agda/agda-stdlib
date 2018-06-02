------------------------------------------------------------------------
-- The Agda standard library
--
-- Inductive Definition of Order Preserving Embeddings
------------------------------------------------------------------------

module Data.List.Relation.OrderPreservingEmbedding where

open import Data.Empty
open import Data.Nat.Base
open import Data.Nat.Properties
open ≤-Reasoning
open import Data.List.Base
open import Function
import Function.Injection as F
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


------------------------------------------------------------------------
-- Type and Basic combinators

module _ {a} {A : Set a} where

  infix 3 _↣_
  data _↣_ : Rel (List A) a where
    base : [] ↣ []
    weak : ∀ {xs y ys} → xs ↣ ys → xs ↣ (y ∷ ys)
    copy : ∀ {x xs ys} → xs ↣ ys → (x ∷ xs) ↣ (x ∷ ys)

  infix 4 []↣_
  []↣_ : ∀ xs → [] ↣ xs
  []↣ []     = base
  []↣ x ∷ xs = weak ([]↣ xs)

------------------------------------------------------------------------
-- Interaction with List operations

  length-↣-≤ : ∀ {xs ys} → xs ↣ ys → length xs ≤ length ys
  length-↣-≤ base     = ≤-refl
  length-↣-≤ (weak p) = ≤-step (length-↣-≤ p)
  length-↣-≤ (copy p) = s≤s (length-↣-≤ p)

  ++-↣ : ∀ {xs ys us vs} → xs ↣ ys → us ↣ vs → xs ++ us ↣ ys ++ vs
  ++-↣ base     q = q
  ++-↣ (weak p) q = weak (++-↣ p q)
  ++-↣ (copy p) q = copy (++-↣ p q)

module _ {a b} {A : Set a} {B : Set b} where

  map-↣ : ∀ {xs ys} (f : A → B) → xs ↣ ys → map f xs ↣ map f ys
  map-↣ f base     = base
  map-↣ f (weak p) = weak (map-↣ f p)
  map-↣ f (copy p) = copy (map-↣ f p)

  open F.Injection

  map⁻¹-↣ : ∀ {xs ys} (inj : A F.↣ B) →
            map (inj ⟨$⟩_) xs ↣ map (inj ⟨$⟩_) ys → xs ↣ ys
  map⁻¹-↣ {[]}     {ys}     inj p = []↣ ys
  map⁻¹-↣ {x ∷ xs} {[]}     inj ()
  map⁻¹-↣ {x ∷ xs} {y ∷ ys} inj p
    with inj ⟨$⟩ x | inspect (inj ⟨$⟩_) x
       | inj ⟨$⟩ y | inspect (inj ⟨$⟩_) y
       | injective inj {x} {y}
  map⁻¹-↣ {x ∷ xs} {y ∷ ys} inj (weak p)
    | fx | [ eq ] | fy | _ | _ = weak (map⁻¹-↣ inj (coerce p))
    where coerce = subst (λ fx → fx ∷ _ ↣ _) (sym eq)
  map⁻¹-↣ {x ∷ xs} {y ∷ ys} inj (copy p)
    | fx | _ | .fx | _ | eq
    rewrite eq refl = copy (map⁻¹-↣ inj p)


------------------------------------------------------------------------
-- _↣_ is a partial order on lists

module _ {a} {A : Set a} where

  ↣-reflexive : _≡_ ⇒ _↣_ {A = A}
  ↣-reflexive {[]}     refl = base
  ↣-reflexive {x ∷ xs} refl = copy (↣-reflexive refl)

  ↣-refl : Reflexive {A = List A} _↣_
  ↣-refl = ↣-reflexive refl

  ↣-trans : Transitive {A = List A} _↣_
  ↣-trans p        base     = p
  ↣-trans p        (weak q) = weak (↣-trans p q)
  ↣-trans (weak p) (copy q) = weak (↣-trans p q)
  ↣-trans (copy p) (copy q) = copy (↣-trans p q)

  ↣-antisym : Antisymmetric {A = List A} _≡_ _↣_
  -- Positive cases
  ↣-antisym base     base     = refl
  ↣-antisym (copy p) (copy q) = cong (_ ∷_) (↣-antisym p q)
  -- Dismissing the impossible cases
  ↣-antisym {x ∷ xs} {y ∷ ys} (weak p) (weak q) = ⊥-elim $ 1+n≰n $ begin
    length (y ∷ ys) ≤⟨ length-↣-≤ q ⟩
    length xs       ≤⟨ n≤1+n (length xs) ⟩
    length (x ∷ xs) ≤⟨ length-↣-≤ p ⟩
    length ys       ∎
  ↣-antisym {x ∷ xs} {y ∷ ys} (weak p) (copy q) = ⊥-elim $ 1+n≰n $ begin
    length (x ∷ xs) ≤⟨ length-↣-≤ p ⟩
    length ys       ≤⟨ length-↣-≤ q ⟩
    length xs       ∎
  ↣-antisym {x ∷ xs} {y ∷ ys} (copy p) (weak q) =  ⊥-elim $ 1+n≰n $ begin
    length (y ∷ ys) ≤⟨ length-↣-≤ q ⟩
    length xs       ≤⟨ length-↣-≤ p ⟩
    length ys       ∎

  ↣-isPreorder : IsPreorder _≡_ (_↣_ {A = A})
  ↣-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = ↣-reflexive
    ; trans         = ↣-trans
    }

  ↣-preorder : Preorder _ _ _
  ↣-preorder = record
    { isPreorder = ↣-isPreorder
    }

  ↣-isPartialOrder : IsPartialOrder _≡_ _↣_
  ↣-isPartialOrder = record
    { isPreorder = ↣-isPreorder
    ; antisym    = ↣-antisym
    }
