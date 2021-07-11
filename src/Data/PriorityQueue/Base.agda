------------------------------------------------------------------------
-- The Agda standard library
--
-- Interface definition of priority queue
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (TotalOrder)

module Data.PriorityQueue.Base
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open import Data.Empty
open import Data.Maybe as Maybe
open import Data.Maybe.Properties
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties
open import Data.Product
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Unary.All using (All)
open import Function.Base
open import Level renaming (suc to ℓ-suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open import Relation.Unary hiding (Empty)
open import Relation.Nullary
open import Induction.WellFounded

open TotalOrder totalOrder renaming (Carrier to A)

record RawPriorityQueue b ℓ : Set (a ⊔ ℓ-suc (b ⊔ ℓ)) where
  field
    Queue  : Set b
    size   : Queue → ℕ
    empty  : Queue
    insert : A → Queue → Queue
    meld   : Queue → Queue → Queue
    popMin : Queue → Maybe (A × Queue)

  singleton : A → Queue
  singleton x = insert x empty

  findMin : Queue → Maybe A
  findMin = Maybe.map proj₁ ∘ popMin

  deleteMin : Queue → Maybe Queue
  deleteMin = Maybe.map proj₂ ∘ popMin

  Empty : Pred Queue (a ⊔ b)
  Empty q = popMin q ≡ nothing

  ¬Empty : Pred Queue (a ⊔ b)
  ¬Empty q = ¬ Empty q

  PopMin : Queue → A → Queue → Set (a ⊔ b)
  PopMin q x q' = popMin q ≡ just (x , q')

  FindMin : REL Queue A a
  FindMin q x = findMin q ≡ just x

  DeleteMin : Rel Queue b
  DeleteMin q q' = deleteMin q ≡ just q'

  _≺_ : Rel Queue b
  q' ≺ q = DeleteMin q q'

  _⊀_ : Rel Queue b
  q' ⊀ q = ¬ (q' ≺ q)

  Empty⇒⊀ : ∀ {q} → Empty q → (∀ q' → q' ⊀ q)
  Empty⇒⊀ {q} ≡nothing q' ≡just = just≢nothing $ begin
    just q'     ≡˘⟨ ≡just ⟩
    deleteMin q ≡⟨ P.cong (Maybe.map proj₂) ≡nothing ⟩
    nothing     ∎
    where open P.≡-Reasoning


record SizeLaws {b ℓ} (rawPriorityQueue : RawPriorityQueue b ℓ) : Set (a ⊔ b) where
  open RawPriorityQueue rawPriorityQueue

  field
    Empty⇒size≡0 : ∀ q → Empty q → size q ≡ 0
    ≺-size        : ∀ q q' → q' ≺ q → size q ≡ 1 + size q'
    size-empty    : size empty ≡ 0
    size-insert   : ∀ x q → size (insert x q) ≡ 1 + size q
    size-meld     : ∀ q₁ q₂ → size (meld q₁ q₂) ≡ size q₁ + size q₂

  size≡0⇒Empty : ∀ q → size q ≡ 0 → Empty q
  size≡0⇒Empty q #q≡0 with popMin q in eq
  ... | nothing = P.refl
  ... | just (x , q') = ⊥-elim ∘ 0≢1+n $ begin
    0           ≡˘⟨ #q≡0 ⟩
    size q      ≡⟨ ≺-size q q' (P.cong (Maybe.map proj₂) eq) ⟩
    1 + size q' ∎
    where open P.≡-Reasoning

  ≺-wellFounded : WellFounded _≺_
  ≺-wellFounded = λ q → Size⇒Acc _ q P.refl
    where
    Size⇒Acc : ∀ n q → size q ≡ n → Acc _≺_ q
    Size⇒Acc zero    q #q≡0 = acc λ q' q'≺q →
      ⊥-elim (Empty⇒⊀ (size≡0⇒Empty q #q≡0) q' q'≺q)
    Size⇒Acc (suc m) q #q≡n = acc λ q' q'≺q →
      Size⇒Acc m q' ∘ suc-injective $ begin
        1 + size q' ≡˘⟨ ≺-size q q' q'≺q ⟩
        size q      ≡⟨ #q≡n ⟩
        1 + m       ∎
      where open P.≡-Reasoning

  toListAux : ∀ q → @0 Acc _≺_ q → List A
  toListAux q (acc rs) with popMin q
  ... | nothing       = []
  ... | just (x , q') = x ∷ toListAux q' (rs q' P.refl)

  toList : Queue → List A
  toList q = toListAux q (≺-wellFounded q)


record ElementLaws
  {b ℓ}
  (rawPriorityQueue : RawPriorityQueue b ℓ)
  (sizeLaws : SizeLaws rawPriorityQueue)
  : Set (a ⊔ b ⊔ ℓ₂) where

  open RawPriorityQueue rawPriorityQueue
  open SizeLaws sizeLaws

  field
    toList-insert  : ∀ q x → toList (insert x q) ↭ x ∷ toList q
    toList-meld    : ∀ q₁ q₂ → toList (meld q₁ q₂) ↭ toList q₁ ++ toList q₂
    toList-FindMin : ∀ q x → FindMin q x → All (x ≤_) (toList q)


record PriorityQueue b ℓ : Set (a ⊔ ℓ-suc (b ⊔ ℓ) ⊔ ℓ₂) where
  field
    rawPriorityQueue : RawPriorityQueue b ℓ
    sizeLaws         : SizeLaws rawPriorityQueue
    elementLaws      : ElementLaws rawPriorityQueue sizeLaws

  open RawPriorityQueue rawPriorityQueue public
  open SizeLaws sizeLaws public
  open ElementLaws elementLaws public
