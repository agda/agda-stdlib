------------------------------------------------------------------------
-- The Agda standard library
--
-- Queue-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Queue.TwoList.Properties where

open import Level using (Level)
open import Data.List.Base using (List; _∷_; [_]; _∷ʳ_; _++_; length)
open import Data.List.Properties using (++-identityʳ; length-++; length-reverse; ++-assoc)
open import Data.List.Relation.Unary.All using (All; Null; [])
open import Data.List.Relation.Unary.All.Properties using (++⁺; nullxs→xs≡[]; ¬Null-∷)
open import Data.Nat.Base using (suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc; +-assoc)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Data.Queue.QueueSpec using (RawQueue; IsQueue)
open import Data.Queue.TwoList.Base
open import Data.SnocList.Base as SnocList using (List<; []; _<:_; toList>; fromList>; _<><_; _<>>_)
  renaming (_++_ to _++<_)
open import Data.SnocList.Properties
  renaming (++-identityʳ to ++<-identityʳ; ++-identityˡ to ++<-identityˡ; ++-identity to ++<-identity)
  hiding (length-++)
open import Data.SnocList.Relation.Unary.All using (All<; Null<; []; _<:_)
open import Data.SnocList.Relation.Unary.All.Properties using (all<>>; all<>)
open import Function.Base using (_∘_)
open import Relation.Binary.Core using (_=[_]⇒_)
open import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Binary.Definitions using (Reflexive; _Respects_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary using (¬_; False; contradiction)
open import Relation.Unary using (Pred)
open import Tactic.Cong using (cong!)

open ≡-Reasoning

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Properties of toList and fromList

empty→toList≡[] : ∀ {x : Queue A} → Empty x → toList x ≡ []
empty→toList≡[] {x = x@(mkQ [] back inv)} [] = begin
  toList (mkQ [] back inv)  ≡⟨⟩
  back ++ []                ≡⟨ ++-identityʳ back ⟩
  back                      ≡⟨ nullxs→xs≡[] (inv []) ⟩
  []                        ∎

toList≡[]→front≡[] : ∀ {xs : Queue A} → toList xs ≡ [] → Queue.front xs ≡ []
toList≡[]→front≡[] {xs = xs@(mkQ front [] inv)} xs≡[] = xs<>>[]≡[] xs≡[]

toList≡[]→empty : ∀ {xs : Queue A} → toList xs ≡ [] → Empty xs
toList≡[]→empty {xs = xs} xs≡[] rewrite (toList≡[]→front≡[] {xs = xs} xs≡[]) = []

toList-fromList : ∀ {q : Queue A} {xs : List A} → q ≈ fromList xs → toList q ≡ xs
toList-fromList {q = q} {xs = xs} q≈xs = begin
  toList q             ≡⟨ q≈xs ⟩
  toList (fromList xs) ≡⟨ toList-fromList' xs ⟩
  xs                   ∎
  where
    queue[]xs→back≡[] : ∀ {xs : List A} → (Queue.back (queue [] xs)) ≡ []
    queue[]xs→back≡[] = refl

    toList-fromList' : ∀ (xs : List A) → toList (fromList xs) ≡ xs
    toList-fromList' xs = begin
      toList (fromList xs)                         ≡⟨⟩
      toList (queue [] xs)                         ≡⟨ cong₂ _++_ (queue[]xs→back≡[] {xs = xs}) refl ⟩
      [] ++ (toList> (Queue.front (queue [] xs)))  ≡⟨⟩
      toList> (Queue.front (queue [] xs))          ≡⟨⟩
      toList> (fromList> xs)                       ≡⟨ toList>-fromList> xs ⟩
      xs                                           ∎

fromList-toList : ∀ {q : Queue A} {xs : List A} → xs ≡ toList q → fromList xs ≈ q
fromList-toList {q = q} {xs} xs≈q = begin
  ([] <>< xs) <>> []                   ≡⟨ []<><xs<>>[]≡xs {xs = xs} ⟩
  xs                                   ≡⟨ xs≈q ⟩
  Queue.back q ++ Queue.front q <>> [] ∎

empty-toList : ∀ {q : Queue A} → Empty q → Null (toList q)
empty-toList {q = mkQ front back inv} emptyq = ++⁺ {xs = back} (inv emptyq) (all<> emptyq)

empty-fromList  : ∀ {xs : List A} → Null xs → Empty (fromList xs)
empty-fromList {xs = []} nullxs = []
empty-fromList {xs = x ∷ xs} nullxs = contradiction nullxs ¬Null-∷

toList-enqueue : ∀ {q : Queue A} {x : A} → toList (enqueue x q) ≡ x ∷ toList q
toList-enqueue {q = mkQ [] back inv} {x} = begin
  x ∷ []         ≡⟨⟩
  x ∷ [] ++ []   ≡⟨ sym (cong! (nullxs→xs≡[] (inv []))) ⟩
  x ∷ back ++ [] ∎
toList-enqueue {q = mkQ (front <: x) back inv} = refl

toList-dequeue  : ∀ {q : Queue A} → .{{i : False (empty? q)}} →
                      let xr = dequeue q {{i}} in toList q ≡ toList (proj₁ xr) ∷ʳ proj₂ xr
toList-dequeue {q = mkQ (xs <: x) [] inv} = begin
  xs <>> [ x ]                                          ≡⟨ cong! (sym (++<-identityˡ xs)) ⟩
  ([] ++< xs) <>> [ x ]                                 ≡⟨ <>>-toList>++ {xs = ([] ++< xs)} ⟩
  (toList> ([] ++< xs)) ++ [ x ]                        ≡⟨ cong! (toList>-distrib-++ {xs = []} {ys = xs}) ⟩
  ([] ++ (toList> xs)) ++ [ x ]                         ≡⟨ cong! (sym (queue-back[] {xs = xs})) ⟩
  ((Queue.back (queue xs [])) ++ (toList> xs)) ++ [ x ] ≡⟨⟩
  ((Queue.back (queue xs [])) ++ (xs <>> [])) ++ [ x ]  ≡⟨ cong! (sym (queue-front {xs = xs})) ⟩
  ((Queue.back (queue xs [])) ++ (Queue.front (queue xs []) <>> [])) ++ [ x ] ∎

  where
    queue-front : ∀ {xs : List< A} → (Queue.front (queue xs [])) ≡ xs
    queue-front {xs = []} = refl
    queue-front {xs = xs <: x} = refl

    queue-back[] : ∀ {xs : List< A} → (Queue.back (queue xs [])) ≡ []
    queue-back[] {xs = []} = refl
    queue-back[] {xs = xs <: x} = refl

-- either xs empty, so Queue.back ≡ [], or xs is not, so Queue.back ≡ y ∷ ys
toList-dequeue {q = mkQ ([] <: x) (y ∷ ys) inv} = sym (begin
   (([] <: y) <>< ys) <>> [] ++ [ x ]         ≡⟨ cong (λ z → z ++ x ∷ []) (fish-and-chips ys ([] <: y) []) ⟩
   ([] <: y) <>> ([] <>< ys) <>> [] ++ [ x ]  ≡⟨⟩
   [] <>> (y ∷ (([] <>< ys) <>> [] ++ [ x ])) ≡⟨⟩
   (y ∷ (([] <>< ys) <>> [] ++ [ x ]))        ≡⟨ cong! ([]<><xs<>>[]≡xs {xs = ys}) ⟩
   y ∷ ys ++ [ x ]                            ∎
   )

toList-dequeue {q = mkQ ((xs <: z) <: x) (y ∷ ys) inv} = begin
  y ∷ ys ++ xs <>> (z ∷ x ∷ [])           ≡⟨⟩
  y ∷ (ys ++ xs <>> (z ∷ x ∷ []))         ≡⟨ cong! (sym (++-identityʳ (xs <>> (z ∷ x ∷ [])))) ⟩
  y ∷ (ys ++ xs <>> (z ∷ x ∷ []) ++ [])   ≡⟨ cong (λ w → y ∷ (ys ++ w)) (++<>> {xs = xs} {ys = []})⟩
  y ∷ (ys ++ xs <>> (z ∷ []) ++ ([ x ]))  ≡⟨ cong (λ w → y ∷ w) (sym (Data.List.Properties.++-assoc ys (xs <>> (z ∷ [])) ([ x ]))) ⟩
  y ∷ (ys ++ xs <>> (z ∷ [])) ++ [ x ]    ∎

  where
    ++<>> : ∀ {x y} {xs : List< A} {ys : List A} → xs <>> (x ∷ y ∷ []) ++ ys ≡ (xs <>> (x ∷ [])) ++ (y ∷ ys)
    ++<>> {x = x} {y} {xs} {ys} = begin
      xs <>> (x ∷ y ∷ []) ++ ys     ≡⟨⟩
      xs <>> ([ x ] ++ [ y ]) ++ ys ≡⟨ sym (<>>++∷ {xs = xs} {ys = [ x ]}) ⟩
      xs <>> [ x ] ++ y ∷ ys        ∎

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
      0                   ∎

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
≈-resp-Empty {x = x} {y = y} x≈y empty-x = toList≡[]→empty {xs = y} (begin
  toList y ≡⟨ sym x≈y ⟩
  toList x ≡⟨ empty→toList≡[] {x = x} empty-x ⟩
  []       ∎
  )

-- _≈_ on TwoList is defined exactly as such
≈-=[toList]⇒-≡  : (_≈_ {A = A}) =[ toList ]⇒ _≡_
≈-=[toList]⇒-≡ x≈y = x≈y
