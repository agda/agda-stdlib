------------------------------------------------------------------------
-- The Agda standard library
--
-- Permutation with decidable equality
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_ ; refl ; setoid ; _≢_ ; isEquivalence)
  renaming (trans to ≡-trans)
open import Relation.Binary

module Data.List.Permutation.DecPropositional {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.List
open import Data.List.Any
open import Relation.Nullary
open import Data.Empty
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂ ; _×_ ; ∃ ; ∃₂)
open import Data.List.Permutation
open import Function

open import Data.Nat.Properties

open import Data.List.Membership.DecPropositional _≟_

cmap : ∀ {a} → Set a → Set _
cmap A = A → ℕ

empty : cmap A
empty _ = 0

singleton : A → cmap A
singleton a x with a ≟ x
... | yes _ = 1
... | no _  = 0

union : cmap A → cmap A → cmap A
union m₁ m₂ x = m₁ x + m₂ x

collect : List A → cmap A
collect []      = empty
collect (x ∷ l) = union (singleton x) (collect l)

union-comm : ∀ m₁ m₂ x → union m₁ m₂ x ≡ union m₂ m₁ x
union-comm m₁ m₂ x = +-comm (m₁ x) (m₂ x)

union-assoc : ∀ m₁ m₂ m₃ x → union (union m₁ m₂) m₃ x ≡ union m₁ (union m₂ m₃) x
union-assoc m₁ m₂ m₃ x = +-assoc (m₁ x) (m₂ x) (m₃ x)

collect-++-comm : ∀ l₁ l₂ x → collect (l₁ ++ l₂) x ≡ union (collect l₁) (collect l₂) x
collect-++-comm [] l₂ x           = refl
collect-++-comm (x₁ ∷ l₁) l₂ x
  rewrite collect-++-comm l₁ l₂ x = ≡.sym $ +-assoc (singleton x₁ x) (collect l₁ x) (collect l₂ x)

collect-swap : ∀ l₁ l₂ x → collect (l₁ ++ l₂) x ≡ collect (l₂ ++ l₁) x
collect-swap l₁ l₂ x
  rewrite collect-++-comm l₁ l₂ x
        | collect-++-comm l₂ l₁ x = +-comm (collect l₁ x) (collect l₂ x)

-- inversion lemmas to reveal the information of the input of `collect`

collect-[]-inv : ∀ l → (∀ x → collect l x ≡ 0) → l ≡ []
collect-[]-inv [] ev      = refl
collect-[]-inv (x ∷ l) ev with ev x
... | res with x ≟ x
collect-[]-inv (x ∷ l) ev | ()  | yes p
collect-[]-inv (x ∷ l) ev | res | no ¬p with ¬p refl
... | ()

collect-∷-inv : ∀ l x n → collect l x ≡ suc n →
  ∃₂ ( λ l₁ l₂ → l ≡ l₁ ++ x ∷ l₂
     × collect (l₁ ++ l₂) x ≡ n
     × ∀ x′ → x ≢ x′ → collect (l₁ ++ l₂) x′ ≡ collect l x′)
collect-∷-inv []       x n ()
collect-∷-inv (x₁ ∷ l) x n ev with x₁ ≟ x
... | yes refl with ev
... | refl = [] , l , refl , refl , helper
  where helper : ∀ x′ → x₁ ≢ x′ →
                   collect l x′ ≡ singleton x₁ x′ + collect l x′
        helper x′ x₁≢x′ with x₁ ≟ x′
        ... | yes refl = ⊥-elim $ x₁≢x′ refl
        ... | no _     = refl
collect-∷-inv (x₁ ∷ l) x n ev | no ¬p with collect-∷-inv l x n ev
... | l₁ , l₂ , refl , refl , h = x₁ ∷ l₁ , l₂ , refl , eqpf , helper
  where eqpf : singleton x₁ x + collect (l₁ ++ l₂) x ≡ collect (l₁ ++ l₂) x
        eqpf with x₁ ≟ x
        ... | yes refl              = ⊥-elim $ ¬p refl
        ... | no _                  = refl
        helper₁ : ∀ l₁ x′ → x ≢ x′ →
                    collect (l₁ ++ l₂) x′ ≡ collect (l₁ ++ x ∷ l₂) x′
        helper₁ [] x′ x≢x′ with x ≟ x′
        ... | yes refl              = ⊥-elim $ x≢x′ refl
        ... | no _                  = refl
        helper₁ (x ∷ l₁) x′ x≢x′
          rewrite helper₁ l₁ _ x≢x′ = refl
        helper : ∀ (x′ : A) → x ≢ x′ →
                   singleton x₁ x′ + collect (l₁ ++ l₂) x′ ≡ singleton x₁ x′ + collect (l₁ ++ x ∷ l₂) x′
        helper _ x≢x′
          rewrite helper₁ l₁ _ x≢x′ = refl

-- an extentional definition of permutation based on multiset/bag

mperm : Rel (List A) _
mperm l₁ l₂ = ∀ x → collect l₁ x ≡ collect l₂ x

mperm-refl : Reflexive mperm
mperm-refl x = refl

mperm-sym : Symmetric mperm
mperm-sym m y = ≡.sym (m y)

mperm-trans : Transitive mperm
mperm-trans m₁₂ m₂₃ x = ≡-trans (m₁₂ x) (m₂₃ x)

mperm-isEquivalence : IsEquivalence mperm
mperm-isEquivalence = record
  { refl  = λ {l} → mperm-refl {l}
  ; sym   = λ {l} {l′} → mperm-sym {l} {l′}
  ; trans = λ {l₁} {l₂} {l₃} → mperm-trans {l₁} {l₂} {l₃}
  }

mperm-setoid : Setoid _ _
mperm-setoid = record { isEquivalence = mperm-isEquivalence }


-- a proof showing they are the same

perm⇒mperm : ∀ {l₁ l₂} → perm l₁ l₂ → mperm l₁ l₂
perm⇒mperm unit x                      = refl
perm⇒mperm (prep x₁ p) x
  rewrite perm⇒mperm p x               = refl
perm⇒mperm (swap {l₂ = l₂} a b p) x
  rewrite perm⇒mperm p x with singleton a x | singleton b x
... | sa | sb
  rewrite ≡.sym $ +-assoc sa sb (collect l₂ x)
        | +-comm sa sb
        | +-assoc sb sa (collect l₂ x) = refl
perm⇒mperm (trans p p₁) x
  rewrite perm⇒mperm p x
        | perm⇒mperm p₁ x              = refl

mperm⇒perm : ∀ {l₁ l₂} → mperm l₁ l₂ → perm l₁ l₂
mperm⇒perm {[]}  {l₂} ev
  rewrite collect-[]-inv l₂ (≡.sym ∘ ev) = unit
mperm⇒perm {x ∷ l₁} {l₂} ev with ev x
... | res with x ≟ x
... | yes refl with collect-∷-inv l₂ x _ (≡.sym res)
... | lh , lt , refl , q , h             = begin
  x ∷ l₁       <⟨ mperm⇒perm helper ⟩
  x ∷ lh ++ lt p⟨ perm-sym $ perm-shift lh lt x ⟩
  lh ++ x ∷ lt ∎
  where open PReasoning
        helper : mperm l₁ (lh ++ lt)
        helper y with ev y
        ... | res with x ≟ y
        ... | yes refl = ≡.sym q
        ... | no x≢y   = ≡-trans res (≡.sym $ h _ x≢y)
mperm⇒perm {x ∷ l₁} {l₂} ev | _ | no ¬p = ⊥-elim $ ¬p refl
