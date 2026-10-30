------------------------------------------------------------------------
-- The Agda standard library
--
-- Queue specification
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue.QueueSpec where

open import Data.Bool.Base using (Bool)
open import Data.List.Base as List using (List; []; length; _∷_)
open import Data.List.Relation.Unary.All using (Null)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Level
open import Relation.Binary.Core using (Rel; _=[_]⇒_)
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary.Decidable.Core using (yes; no; isYes; False; does)
open import Relation.Unary using (Pred; Decidable)

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- RawQueue defines the 'computations' available on Queues
-- without any of the associated proofs that determine its
-- correctness.
record RawQueue (Q : Set a → Set a) : Set (suc a) where

  field
    _≈_      : ∀ {A : Set a} → Rel (Q A) a
    Empty    : ∀ {A : Set a} → Pred (Q A) a
    empty?   : Decidable (Empty {A = A})
    fromList : List A → Q A
    toList   : Q A → List A
    enqueue  : A → Q A → Q A
    dequeue  : (q : Q A) → .{{False (empty? q)}} → Q A × A
    size     : Q A → ℕ

  empty : Q A
  empty = fromList []

  pure    : A → Q A
  pure = fromList ∘ List.[_]

  to𝔹 : Q A → Bool
  to𝔹 = isYes ∘ empty?

  dequeue′ : Q A → Maybe (Q A × A)
  dequeue′ q with empty? q in eq
  ... | yes _ = nothing
  ... | no _  = just (dequeue q)
    where instance
    _ : False (empty? q)
    _ rewrite eq = _

-- IsQueue bundles RawQueue with proofs of a Queues correctness,
-- such as enqueue adding 1 to the Queue's size
-- NOTE: not finished adding everything!
-- Should name be Queue or IsQueue?
record IsQueue (Q : Set a → Set a) : Set (suc a) where

  field
    rawQ            : RawQueue Q

  open RawQueue rawQ

  field
    isEquivalence   : IsEquivalence (_≈_ {A = A})
    ≈-resp-Empty    : Empty Respects (_≈_ {A = A})
    ≈-=[toList]⇒-≡  : (_≈_ {A = A}) =[ toList ]⇒ _≡_
    empty-toList    : ∀ {q : Q A} → Empty q → Null (toList q)
    empty-fromList  : ∀ {xs : List A} → Null {A = A} xs → Empty (fromList xs)
    toList-fromList : ∀ {q : Q A} {xs : List A} → q ≈ fromList xs → toList q ≡ xs
    fromList-toList : ∀ {q : Q A} {xs : List A} → xs ≡ toList q → fromList xs ≈ q
    toList-enqueue  : ∀ {q : Q A} {x : A} → toList (enqueue x q) ≡ x ∷ toList q
    -- for some reason, let x , r = ... doesn't bind x and r??
    toList-dequeue  : ∀ {q : Q A} → .{{i : False (empty? q)}} →
                      let xr = dequeue q {{i}} in toList q ≡  toList (proj₁ xr) List.∷ʳ proj₂ xr
