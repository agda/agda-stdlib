------------------------------------------------------------------------
-- The Agda standard library
--
-- An equational reasoning library for propositional equality over
-- vectors of different indices using cast.
--
-- To see example usages of this library, scroll to the `Combinators`
-- section.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module README.Data.Vec.Relation.Binary.Equality.Cast where

open import Agda.Primitive
open import Data.List.Base as List using (List)
import Data.List.Properties as List
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Vec.Base
open import Data.Vec.Properties
open import Data.Vec.Relation.Binary.Equality.Cast
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning)

private variable
  a : Level
  A : Set a
  l m n o : ℕ
  xs ys zs ws : Vec A n


------------------------------------------------------------------------
-- Motivation
--
-- The `cast` function is the computational variant of `subst` for
-- vectors. Since `cast` computes under vector constructors, it
-- enables reasoning about vectors with non-definitionally equal indices
-- by induction. See, e.g., Jacques Carette's comment in issue #1668.
-- <https://github.com/agda/agda-stdlib/pull/1668#issuecomment-1003449509>
--
-- Suppose we want to prove that ‘xs ++ [] ≡ xs’. Because `xs ++ []`
-- has type `Vec A (n + 0)` while `xs` has type `Vec A n`, they cannot
-- be directly related by homogeneous equality.
-- To resolve the issue, `++-right-identity` uses `cast` to recast
-- `xs ++ []` as a vector in `Vec A n`.
--
++-right-identity : ∀ .(eq : n + 0 ≡ n) (xs : Vec A n) → cast eq (xs ++ []) ≡ xs
++-right-identity eq []       = refl
++-right-identity eq (x ∷ xs) = cong (x ∷_) (++-right-identity (cong pred eq) xs)
--
-- When the input is `x ∷ xs`, because `cast eq (x ∷ _)` equals
-- `x ∷ cast (cong pred eq) _`, the proof obligation
--     cast eq (x ∷ xs ++ []) ≡ x ∷ xs
-- simplifies to
--     x :: cast (cong pred eq) (xs ++ []) ≡ x ∷ xs


-- Although `cast` makes it possible to prove vector identities by ind-
-- uction, the explicit type-casting nature poses a significant barrier
-- to code reuse in larger proofs. For example, consider the identity
-- ‘fromList (xs List.∷ʳ x) ≡ (fromList xs) ∷ʳ x’ where `List._∷ʳ_` is the
-- snoc function of lists. We have
--
--     fromList (xs List.∷ʳ x)            : Vec A (List.length (xs List.∷ʳ x))
--   =   {- by definition -}
--     fromList (xs List.++ List.[ x ])   : Vec A (List.length (xs List.++ List.[ x ]))
--   =   {- by fromList-++ -}
--     fromList xs ++ fromList List.[ x ] : Vec A (List.length xs + List.length [ x ])
--   =   {- by definition -}
--     fromList xs ++ [ x ]               : Vec A (List.length xs + 1)
--   =   {- by unfold-∷ʳ -}
--     fromList xs ∷ʳ x                   : Vec A (suc (List.length xs))
-- where
--     fromList-++ : cast _ (fromList (xs List.++ ys)) ≡ fromList xs ++ fromList ys
--     unfold-∷ʳ   : cast _ (xs ∷ʳ x) ≡ xs ++ [ x ]
--
-- Although the identity itself is simple, the reasoning process changes
-- the index in the type twice. Consequently, its Agda translation must
-- insert two `cast`s in the proof. Moreover, the proof first has to
-- rearrange (the Agda version of) the identity into one with two
-- `cast`s, resulting in lots of boilerplate code as demonstrated by
-- `example1a-fromList-∷ʳ`.
example1a-fromList-∷ʳ : ∀ (x : A) xs →
                        .(eq : List.length (xs List.∷ʳ x) ≡ suc (List.length xs)) →
                        cast eq (fromList (xs List.∷ʳ x)) ≡ fromList xs ∷ʳ x
example1a-fromList-∷ʳ x xs eq = begin
  cast eq (fromList (xs List.∷ʳ x))
    ≡⟨⟩
  cast eq (fromList (xs List.++ List.[ x ]))
    ≡⟨ cast-trans eq₁ eq₂ (fromList (xs List.++ List.[ x ])) ⟨
  cast eq₂ (cast eq₁ (fromList (xs List.++ List.[ x ])))
    ≡⟨ cong (cast eq₂) (fromList-++ xs) ⟩
  cast eq₂ (fromList xs ++ [ x ])
    ≡⟨ ≈-sym (unfold-∷ʳ (sym eq₂) x (fromList xs)) ⟩
  fromList xs ∷ʳ x
    ∎
  where
  open ≡-Reasoning
  eq₁ = List.length-++ xs {List.[ x ]}
  eq₂ = +-comm (List.length xs) 1

-- The `cast`s are irrelevant to core of the proof. At the same time,
-- they can be inferred from the lemmas used during the reasoning steps
-- (e.g. `fromList-++` and `unfold-∷ʳ`). To eliminate the boilerplate,
-- this library provides a set of equational reasoning combinators for
-- equality of the form `cast eq xs ≡ ys`.
example1b-fromList-∷ʳ : ∀ (x : A) xs →
                        .(eq : List.length (xs List.∷ʳ x) ≡ suc (List.length xs)) →
                        cast eq (fromList (xs List.∷ʳ x)) ≡ fromList xs ∷ʳ x
example1b-fromList-∷ʳ x xs eq = begin
  fromList (xs List.∷ʳ x)
    ≈⟨⟩
  fromList (xs List.++ List.[ x ])
    ≈⟨ fromList-++ xs ⟩
  fromList xs ++ [ x ]
    ≈⟨ unfold-∷ʳ (+-comm 1 (List.length xs)) x (fromList xs) ⟨
  fromList xs ∷ʳ x
    ∎
  where open CastReasoning


------------------------------------------------------------------------
-- Combinators
--
-- Let `xs ≈[ m≡n ] ys` denote `cast m≡n xs ≡ ys`. We have reflexivity,
-- symmetry and transitivity:
--     ≈-reflexive : xs ≈[ refl ] xs
--     ≈-sym       : xs ≈[ m≡n ] ys → ys ≈[ sym m≡n ] xs
--     ≈-trans     : xs ≈[ m≡n ] ys → ys ≈[ n≡o ] zs → xs ≈[ trans m≡n n≡o ] zs
-- Accordingly, `_≈[_]_` admits the standard set of equational reasoning
-- combinators. Suppose `≈-eqn : xs ≈[ m≡n ] ys`,
--     xs ≈⟨ ≈-eqn ⟩   -- `_≈⟨_⟩_` takes a `_≈[_]_` step, adjusting
--     ys              -- the index at the same time
--
--     ys ≈⟨ ≈-eqn ⟨   -- `_≈⟨_⟨_` takes a symmetric `_≈[_]_` step
--     xs
example2a : ∀ .(eq : suc m + n ≡ m + suc n) (xs : Vec A m) a ys →
            cast eq ((reverse xs ∷ʳ a) ++ ys) ≡ reverse xs ++ (a ∷ ys)
example2a eq xs a ys = begin
  (reverse xs ∷ʳ a) ++ ys ≈⟨ ∷ʳ-++ eq a (reverse xs) ⟩ -- index: suc m + n
  reverse xs ++ (a ∷ ys)  ∎                            -- index: m + suc n
  where open CastReasoning

-- To interoperate with `_≡_`, this library provides `_≂⟨_⟩_` (\-~) for
-- taking a `_≡_` step during equational reasoning.
-- Let `≡-eqn : xs ≡ ys`, then
--     xs ≂⟨ ≡-eqn  ⟩    -- Takes a `_≡_` step; no change to the index
--     ys
--
--     ys ≂⟨ ≡-eqn ⟨    -- Takes a symmetric `_≡_` step
--     xs
-- Equivalently, `≈-reflexive` injects `_≡_` into `_≈[_]_`. That is,
-- `xs ≂⟨ ≡-eqn ⟩ ys` is the same as `xs ≈⟨ ≈-reflexive ≡-eqn ⟩ ys`.
-- Extending `example2a`, we have:
example2b : ∀ .(eq : suc m + n ≡ m + suc n) (xs : Vec A m) a ys →
            cast eq ((a ∷ xs) ʳ++ ys) ≡ xs ʳ++ (a ∷ ys)
example2b eq xs a ys = begin
  (a ∷ xs) ʳ++ ys         ≂⟨ unfold-ʳ++ (a ∷ xs) ys ⟩          -- index: suc m + n
  reverse (a ∷ xs) ++ ys  ≂⟨ cong (_++ ys) (reverse-∷ a xs) ⟩  -- index: suc m + n
  (reverse xs ∷ʳ a) ++ ys ≈⟨ ∷ʳ-++ eq a (reverse xs) ⟩         -- index: suc m + n
  reverse xs ++ (a ∷ ys)  ≂⟨ unfold-ʳ++ xs (a ∷ ys) ⟨          -- index: m + suc n
  xs ʳ++ (a ∷ ys)         ∎                                    -- index: m + suc n
  where open CastReasoning

-- Oftentimes index-changing identities apply to only part of the proof
-- term. When reasoning about `_≡_`, `cong` shifts the focus to the
-- subterm of interest. In this library, `≈-cong` does a similar job.
-- Suppose `f : A → B`, `xs : B`, `ys zs : A`, `ys≈zs : ys ≈[ _ ] zs`
-- and `xs≈f⟨c·ys⟩ : xs ≈[ _ ] f (cast _ ys)`, we have
--     xs ≈⟨ ≈-cong f xs≈f⟨c·ys⟩ ys≈zs ⟩
--     f zs
-- The reason for having the extra argument `xs≈f⟨c·ys⟩` is to expose
-- `cast` in the subterm in order to apply the step `ys≈zs`. When using
-- ordinary `cong` the proof has to explicitly push `cast` inside:
--     xs            ≈⟨ xs≈f⟨c·ys⟩ ⟩
--     f (cast _ ys) ≂⟨ cong f ys≈zs ⟩
--     f zs
-- Note. Technically, `A` and `B` should be vectors of different length
-- and that `ys`, `zs` are vectors of non-definitionally equal index.
example3a-fromList-++-++ : {xs ys zs : List A} →
                           .(eq : List.length (xs List.++ ys List.++ zs) ≡
                                  List.length xs + (List.length ys + List.length zs)) →
                           cast eq (fromList (xs List.++ ys List.++ zs)) ≡
                                   fromList xs ++ fromList ys ++ fromList zs
example3a-fromList-++-++ {xs = xs} {ys} {zs} eq = begin
  fromList (xs List.++ ys List.++ zs)
    ≈⟨ fromList-++ xs ⟩
  fromList xs ++ fromList (ys List.++ zs)
    ≈⟨ ≈-cong (fromList xs ++_) (cast-++ʳ (List.length-++ ys) (fromList xs)) (fromList-++ ys) ⟩
  fromList xs ++ fromList ys ++ fromList zs
    ∎
  where open CastReasoning

-- As an alternative, one can manually apply `cast-++ʳ` to expose `cast`
-- in the subterm. However, this unavoidably duplicates the proof term.
example3b-fromList-++-++′ : {xs ys zs : List A} →
                            .(eq : List.length (xs List.++ ys List.++ zs) ≡
                                   List.length xs + (List.length ys + List.length zs)) →
                            cast eq (fromList (xs List.++ ys List.++ zs)) ≡
                                    fromList xs ++ fromList ys ++ fromList zs
example3b-fromList-++-++′ {xs = xs} {ys} {zs} eq = begin
  fromList (xs List.++ ys List.++ zs)
    ≈⟨ fromList-++ xs ⟩
  fromList xs ++ fromList (ys List.++ zs)
    ≈⟨ cast-++ʳ (List.length-++ ys) (fromList xs) ⟩
  fromList xs ++ cast _ (fromList (ys List.++ zs))
    ≂⟨ cong (fromList xs ++_) (fromList-++ ys) ⟩
  fromList xs ++ fromList ys ++ fromList zs
    ∎
  where open CastReasoning

-- `≈-cong` can be chained together much like how `cong` can be nested.
-- In this example, `unfold-∷ʳ` is applied to the term `xs ++ [ a ]`
-- in `(_++ ys)` inside of `reverse`. Thus the proof employs two
-- `≈-cong`.
example4-cong² : ∀ .(eq : (m + 1) + n ≡ n + suc m) a (xs : Vec A m) ys →
          cast eq (reverse ((xs ++ [ a ]) ++ ys)) ≡ ys ʳ++ reverse (xs ∷ʳ a)
example4-cong² {m = m} {n} eq a xs ys = begin
  reverse ((xs ++ [ a ]) ++ ys)
    ≈⟨ ≈-cong reverse (cast-reverse (cong (_+ n) (+-comm 1 m)) ((xs ∷ʳ a) ++ ys))
                                             (≈-cong (_++ ys) (cast-++ˡ (+-comm 1 m) (xs ∷ʳ a))
                                                     (unfold-∷ʳ _ a xs)) ⟨
  reverse ((xs ∷ʳ a) ++ ys)
    ≈⟨ reverse-++ (+-comm (suc m) n) (xs ∷ʳ a) ys ⟩
  reverse ys ++ reverse (xs ∷ʳ a)
    ≂⟨ unfold-ʳ++ ys (reverse (xs ∷ʳ a)) ⟨
  ys ʳ++ reverse (xs ∷ʳ a)
    ∎
  where open CastReasoning

------------------------------------------------------------------------
-- Interoperation between `_≈[_]_` and `_≡_`
--
-- This library is designed to interoperate with `_≡_`. Examples in the
-- combinators section showed how to apply `_≂⟨_⟩_` to take an `_≡_`
-- step during equational reasoning about `_≈[_]_`. Recall that
-- `xs ≈[ m≡n ] ys` is a shorthand for `cast m≡n xs ≡ ys`, the
-- combinator is essentially the composition of `_≡_` on the left-hand
-- side of `_≈[_]_`. Dually, the combinator `_≃⟨_⟩_` composes `_≡_` on
-- the right-hand side of `_≈[_]_`. Thus `_≃⟨_⟩_` intuitively ends the
-- reasoning system of `_≈[_]_` and switches back to the reasoning
-- system of `_≡_`.
example5-fromList-++-++′ : {xs ys zs : List A} →
                           .(eq : List.length (xs List.++ ys List.++ zs) ≡
                                  List.length xs + (List.length ys + List.length zs)) →
                           cast eq (fromList (xs List.++ ys List.++ zs)) ≡
                                   fromList xs ++ fromList ys ++ fromList zs
example5-fromList-++-++′ {xs = xs} {ys} {zs} eq = begin
  fromList (xs List.++ ys List.++ zs)
    ≈⟨ fromList-++ xs ⟩
  fromList xs ++ fromList (ys List.++ zs)
    ≃⟨ cast-++ʳ (List.length-++ ys) (fromList xs) ⟩
  fromList xs ++ cast _ (fromList (ys List.++ zs))
    ≡⟨ cong (fromList xs ++_) (fromList-++ ys) ⟩
  fromList xs ++ fromList ys ++ fromList zs
    ≡-∎
  where open CastReasoning

-- Of course, it is possible to start with the reasoning system of `_≡_`
-- and then switch to the reasoning system of `_≈[_]_`.
example6a-reverse-∷ʳ : ∀ x (xs : Vec A n) → reverse (xs ∷ʳ x) ≡ x ∷ reverse xs
example6a-reverse-∷ʳ {n = n} x xs = begin-≡
  reverse (xs ∷ʳ x)
    ≡⟨ ≈-reflexive refl ⟨
  reverse (xs ∷ʳ x)
    ≈⟨ ≈-cong reverse (cast-reverse _ _) (unfold-∷ʳ (+-comm 1 n) x xs) ⟩
  reverse (xs ++ [ x ])
    ≈⟨ reverse-++ (+-comm n 1) xs [ x ] ⟩
  x ∷ reverse xs
    ∎
  where open CastReasoning

example6b-reverse-∷ʳ-by-induction : ∀ x (xs : Vec A n) → reverse (xs ∷ʳ x) ≡ x ∷ reverse xs
example6b-reverse-∷ʳ-by-induction x []       = refl
example6b-reverse-∷ʳ-by-induction x (y ∷ xs) = begin
  reverse (y ∷ (xs ∷ʳ x)) ≡⟨ reverse-∷ y (xs ∷ʳ x) ⟩
  reverse (xs ∷ʳ x) ∷ʳ y  ≡⟨ cong (_∷ʳ y) (example6b-reverse-∷ʳ-by-induction x xs) ⟩
  (x ∷ reverse xs) ∷ʳ y   ≡⟨⟩
  x ∷ (reverse xs ∷ʳ y)   ≡⟨ cong (x ∷_) (reverse-∷ y xs) ⟨
  x ∷ reverse (y ∷ xs)    ∎
  where open ≡-Reasoning
