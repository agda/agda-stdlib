------------------------------------------------------------------------
-- The Agda standard library
--
-- Queue-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue.TwoList.Properties where

open import Level using (Level)
open import Data.Empty using (⊥-elim)
open import Data.List.Base
open import Data.List.Properties using (++-identityʳ; length-++; length-reverse)
open import Data.List.Relation.Unary.All using (All; Null; [])
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat.Base using (suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc; +-assoc)
open import Data.Queue.QueueSpec using (RawQueue; IsQueue)
open import Data.Queue.TwoList.Base
open import Data.SnocList.Base as SnocList using (List<; []; _<:_; toList>; fromList>)
open import Data.SnocList.Properties using (toList>-fromList>)
open import Data.SnocList.Relation.Unary.All using (All<; Null<; []; _<:_)
open import Function.Base using (_∘_)
open import Relation.Binary.Core using (_=[_]⇒_)
open import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Binary.Definitions using (Reflexive; _Respects_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

open ≡-Reasoning
open RawQueue {{...}} using (size)

private
  variable
    a b : Level
    A : Set a
    B : Set b

  ¬Null : {x : A} {xs : List A} → ¬ Null (x ∷ xs)
  ¬Null (() Data.List.Relation.Unary.All.∷ n)

  null-<: : ∀ {x} {xs : List< A} {ys : List A} → Null< (xs <: x) → Null ys
  null-<: (()<: _)

  queue-back[] : ∀ {xs : List< A} → (Queue.back (queue xs [])) ≡ []
  queue-back[] {xs = []} = refl
  queue-back[] {xs = xs <: x} = refl

  queue-front : ∀ {xs : List< A} → (Queue.front (queue xs [])) ≡ xs
  queue-front {xs = []} = refl
  queue-front {xs = xs <: x} = refl

  -- NOTE: *most* of these:
  --        A) Can be moved elsewhere (e.g. the null proofs that are repeated in TwoList.Base, etc...)
  --        B) Should be renamed
  -- Also, (note to self) more time shoud be spent thinking about whether arguments should be implicit or not!
  toList-Empty : ∀ {x : Queue A} → Empty x → toList x ≡ []
  toList-Empty {x = x@(mkQ [] back inv)} [] = begin
    toList (mkQ [] back inv)  ≡⟨⟩
    back ++ [] ≡⟨ ++-identityʳ back ⟩
    back ≡⟨ back[] ⟩
    [] ∎
    where
      null[] : Null back → back ≡ []
      null[] [] = refl

      back[] : back ≡ []
      back[] = null[] (inv [])

  ++-[] : ∀ {xs ys : List A} → (xs ++ ys) ≡ [] → ys ≡ []
  ++-[] {xs = []} {ys = []} xs++ys≡[] = xs++ys≡[]

  ¬null< : {a : A} {as : List< A} → ¬ (Null< (as <: a))
  ¬null< (() Data.SnocList.Relation.Unary.All.<: n)

  null[] : ∀ {xs : List< A} → xs ≡ [] → Null< xs
  null[] xs≡[] rewrite xs≡[] = []

  ¬<>>[] : ∀ {x} {xs : List< A} {ys : List A} → xs SnocList.<>> (x ∷ ys) ≢ []
  ¬<>>[] {xs = []} ()
  ¬<>>[] {xs = xs <: x} wrong = ¬<>>[] {xs = xs} wrong

  <>>[] : ∀ {xs : List< A} → xs SnocList.<>> [] ≡ [] → xs ≡ []
  <>>[] {xs = []} xs<>>[]≡[] = refl
  <>>[] {xs = (xs <: x)} xs<>>[]≡[] = ⊥-elim (¬<>>[] {xs = xs} {ys = []} xs<>>[]≡[])

  toList-front : ∀ {xs : Queue A} → toList xs ≡ [] → Queue.front xs ≡ []
  toList-front {xs = xs@(mkQ front [] inv)} xs≡[] = <>>[] xs≡[]

  empty[] : ∀ {xs : Queue A} → toList xs ≡ [] → Empty xs
  empty[] {xs = xs} xs≡[] = null[] (toList-front {xs = xs} xs≡[])

  All<>> : ∀ {x} {xs : List< A} {ys : List A} {p : Pred A a} → All p ys → All< p xs → p x → All p (xs SnocList.<>> (x ∷ ys))
  All<>> {xs = []} allys allxs px = px All.∷ allys
  All<>> {x = a} {xs = xs <: x} {ys = ys} allys (px <: allxs) pa = All<>> (pa All.∷ allys) allxs px

  All<> : ∀ {xs : List< A} {p : Pred A a} → All< p xs → All p (toList> xs)
  All<> {xs = []} all< = []
  All<> {xs = xs <: x} (px <: all<) = All<>> [] all< px

------------------------------------------------------------------------
-- Properties of toList and fromList

toList-fromList : ∀ {q : Queue A} {xs : List A} → q ≈ fromList xs → toList q ≡ xs
toList-fromList {q = q} {xs = xs} q≈xs = begin
  toList q             ≡⟨ q≈xs ⟩
  toList (fromList xs) ≡⟨ toList-fromList' xs ⟩
  xs                   ∎
  where
    -- TODO: can probably cleanup a little
    toList-fromList' : ∀ (xs : List A) → toList (fromList xs) ≡ xs
    toList-fromList' xs = begin
      toList (fromList xs)                                     ≡⟨⟩
      toList (queue (fromList> xs) [])                         ≡⟨ cong₂ _++_ (queue-back[] {xs = fromList> xs}) refl ⟩
      [] ++ (toList> (Queue.front (queue (fromList> xs) [])))  ≡⟨⟩
      toList> (Queue.front (queue (fromList> xs) []))          ≡⟨ cong toList> (queue-front {xs = fromList> xs}) ⟩
      toList> (fromList> xs)                                   ≡⟨ toList>-fromList> xs ⟩
      xs                                                       ∎

empty-toList : ∀ {q : Queue A} → Empty q → Null (toList q)
empty-toList {q = mkQ front back inv} emptyq = ++⁺ {xs = back} (inv emptyq) (All<> emptyq)

empty-fromList  : ∀ {xs : List A} → Null {A = A} xs → Empty (fromList xs)
empty-fromList nullxs = {!!}



------------------------------------------------------------------------
-- Properties relating to size

-- enqueue increases size by 1
-- rewrite could make it cleaner, but are we trying to use that less?
size-enqueue : (x : A) (q : Queue A) → size (enqueue {a} x q) ≡ suc (size q)
size-enqueue {a = a} {A = A} x q@(mkQ [] back inv) = begin
  size (queue ([] <: x) []) ≡⟨⟩
  length (x ∷ [])           ≡⟨⟩
  suc 0                     ≡⟨ cong suc (sym sizeq) ⟩
  suc (size q)              ∎
  where
    null→≡[] : Null back → back ≡ []
    null→≡[] [] = refl

    back[] : back ≡ []
    back[] = null→≡[] (inv [])

    -- why does length need {a} and {A} after back ↦ []?
    sizeq : size q ≡ 0
    sizeq = begin
      size q              ≡⟨⟩
      length (toList q)   ≡⟨⟩
      length (back ++ []) ≡⟨ cong length (++-identityʳ back) ⟩
      length back         ≡⟨ cong length back[] ⟩
      length {a} {A} []   ≡⟨⟩
      0 ∎

size-enqueue {A = A} x q@(mkQ front@(_ <: _) back inv) = begin
  size (queue front (x ∷ back))              ≡⟨⟩
  length (x ∷ back ++ toList> front)         ≡⟨ length-++ (x ∷ back) ⟩
  length (x ∷ back) + length (toList> front) ≡⟨⟩
  suc (length back) + length (toList> front) ≡⟨ +-comm (suc (length back)) (length (toList> front)) ⟩
  length (toList> front) + suc (length back) ≡⟨ +-suc (length (toList> front)) (length back)⟩
  suc (length (toList> front) + length back) ≡⟨ cong suc (+-comm (length (toList> front)) (length back)) ⟩
  suc (length back + length (toList> front)) ≡⟨ cong suc (sym (length-++ back {toList> front})) ⟩
  suc (length (back ++ (toList> front)))     ≡⟨⟩
  suc (length (toList q))                    ≡⟨⟩
  suc (size q)                               ∎

-- trivial, but ensures empty works correctly
size-empty : size (empty {a} {A}) ≡ 0
size-empty = refl

------------------------------------------------------------------------
-- Properties of _≈_

-- it becomes propositional equality on lists, so easy!
≈-isEquivalence : IsEquivalence (_≈_ {A = A})
≈-isEquivalence = record
  { refl = refl
  ; sym = sym
  ; trans = trans
  }

≈-resp-Empty : Empty Respects (_≈_ {A = A})
≈-resp-Empty {x = x} {y = y} x≈y empty-x = empty[] {xs = y} (begin
  toList y ≡⟨ sym x≈y ⟩
  toList x ≡⟨ toList-Empty {x = x} empty-x ⟩
  []       ∎
  )

-- _≈_ on TwoList is defined exactly as such
≈-=[toList]⇒-≡  : (_≈_ {A = A}) =[ toList ]⇒ _≡_
≈-=[toList]⇒-≡ x≈y = x≈y

-- For some reason, gives unresolved implicits of
--  _x.inv_750 : Null< (Queue.front x) → Null (Queue.back x)
--  _y.inv_753 : Null< (Queue.front y) → Null (Queue.back y)
-- But I'm too tired to trace it through and figure out why for today!
-- ≈-resp-Empty' : Empty Respects (_≈_ {A = A})
-- ≈-resp-Empty' = ≈-resp-Empty

------------------------------------------------------------------------
-- TwoList Queue is a Queue!

-- instance
--   TwoList-IsQueue : IsQueue {a} TwoList-RawQueue
--   TwoList-IsQueue = record
--     { isEquivalence = ≈-isEquivalence
--     ; ≈-resp-Empty = ≈-resp-Empty
--     ; ≈-=[toList]⇒-≡ = {!!}
--     ; empty-toList = {!!}
--     ; empty-fromList = {!!}
--     ; toList-fromList = {!!}
--     ; fromList-toList = {!!}
--     ; toList-enqueue = {!!}
--     ; toList-dequeue = {!!}
--     }
