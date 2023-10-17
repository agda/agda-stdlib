------------------------------------------------------------------------
-- The Agda standard library
--
-- An equational reasoning library for propositional equality over
-- vectors of different indices using cast.
--
-- See README.Data.Vec.Relation.Binary.Equality.Cast for
-- documentation and examples.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Relation.Binary.Equality.Cast {a} {A : Set a} where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Vec.Base
open import Relation.Binary.Core using (REL; _⇒_)
open import Relation.Binary.Definitions using (Sym; Trans)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; trans; sym; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    l m n o : ℕ
    xs ys zs : Vec A n


cast-is-id : .(eq : m ≡ m) (xs : Vec A m) → cast eq xs ≡ xs
cast-is-id eq []       = refl
cast-is-id eq (x ∷ xs) = cong (x ∷_) (cast-is-id (suc-injective eq) xs)

cast-trans : .(eq₁ : m ≡ n) .(eq₂ : n ≡ o) (xs : Vec A m) →
             cast eq₂ (cast eq₁ xs) ≡ cast (trans eq₁ eq₂) xs
cast-trans {m = zero}  {n = zero}  {o = zero}  eq₁ eq₂ [] = refl
cast-trans {m = suc _} {n = suc _} {o = suc _} eq₁ eq₂ (x ∷ xs) =
  cong (x ∷_) (cast-trans (suc-injective eq₁) (suc-injective eq₂) xs)


infix 3 _≈[_]_

_≈[_]_ : ∀ {n m} → Vec A n → .(eq : n ≡ m) → Vec A m → Set a
xs ≈[ eq ] ys = cast eq xs ≡ ys

------------------------------------------------------------------------
-- _≈[_]_ is ‘reflexive’, ‘symmetric’ and ‘transitive’

≈-reflexive : ∀ {n} → _≡_ ⇒ (λ xs ys → _≈[_]_ {n} xs refl ys)
≈-reflexive {x = x} eq = trans (cast-is-id refl x) eq

≈-sym : .{m≡n : m ≡ n} → Sym _≈[ m≡n ]_ _≈[ sym m≡n ]_
≈-sym {m≡n = m≡n} {xs} {ys} xs≈ys = begin
  cast (sym m≡n) ys             ≡⟨ cong (cast (sym m≡n)) xs≈ys ⟨
  cast (sym m≡n) (cast m≡n xs)  ≡⟨ cast-trans m≡n (sym m≡n) xs ⟩
  cast (trans m≡n (sym m≡n)) xs ≡⟨ cast-is-id (trans m≡n (sym m≡n)) xs ⟩
  xs                            ∎
  where open ≡-Reasoning

≈-trans : ∀ .{m≡n : m ≡ n} .{n≡o : n ≡ o} → Trans _≈[ m≡n ]_ _≈[ n≡o ]_ _≈[ trans m≡n n≡o ]_
≈-trans {m≡n = m≡n} {n≡o} {xs} {ys} {zs} xs≈ys ys≈zs = begin
  cast (trans m≡n n≡o) xs ≡⟨ cast-trans m≡n n≡o xs ⟨
  cast n≡o (cast m≡n xs)  ≡⟨ cong (cast n≡o) xs≈ys ⟩
  cast n≡o ys             ≡⟨ ys≈zs ⟩
  zs                      ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Reasoning combinators

module CastReasoning where

  open ≡-Reasoning public
    renaming (begin_ to begin-≡_; _∎ to _≡-∎)

  begin_ : ∀ .{m≡n : m ≡ n} {xs : Vec A m} {ys} → xs ≈[ m≡n ] ys → cast m≡n xs ≡ ys
  begin xs≈ys = xs≈ys

  _∎ : (xs : Vec A n) → cast refl xs ≡ xs
  _∎ xs = ≈-reflexive refl

  _≈⟨⟩_ : ∀ .{m≡n : m ≡ n} (xs : Vec A m) {ys} → xs ≈[ m≡n ] ys → xs ≈[ m≡n ] ys
  xs ≈⟨⟩ xs≈ys = xs≈ys

  -- composition of _≈[_]_
  step-≈-⟩ : ∀ .{m≡n : m ≡ n}.{m≡o : m ≡ o} (xs : Vec A m) {ys : Vec A n} {zs : Vec A o} →
           ys ≈[ trans (sym m≡n) m≡o ] zs → xs ≈[ m≡n ] ys → xs ≈[ m≡o ] zs
  step-≈-⟩ xs ys≈zs xs≈ys = ≈-trans xs≈ys ys≈zs

  step-≈-⟨ : ∀ .{n≡m : n ≡ m}.{m≡o : m ≡ o} (xs : Vec A m) {ys : Vec A n} {zs : Vec A o} →
           ys ≈[ trans n≡m m≡o ] zs → ys ≈[ n≡m ] xs → xs ≈[ m≡o ] zs
  step-≈-⟨ xs ys≈zs ys≈xs = step-≈-⟩ xs ys≈zs (≈-sym ys≈xs)

  -- composition of the equality type on the right-hand side of _≈[_]_,
  -- or escaping to ordinary _≡_
  step-≃-⟩ : ∀ .{m≡n : m ≡ n} (xs : Vec A m) {ys zs} → ys ≡ zs → xs ≈[ m≡n ] ys → xs ≈[ m≡n ] zs
  step-≃-⟩ xs ys≡zs xs≈ys = ≈-trans xs≈ys (≈-reflexive ys≡zs)

  step-≃-⟨ : ∀ .{m≡n : m ≡ n} (xs : Vec A m) {ys zs} → ys ≡ zs → ys ≈[ sym m≡n ] xs → xs ≈[ m≡n ] zs
  step-≃-⟨ xs ys≡zs ys≈xs = step-≃-⟩ xs ys≡zs (≈-sym ys≈xs)

  -- composition of the equality type on the left-hand side of _≈[_]_
  step-≂-⟩ : ∀ .{m≡n : m ≡ n} (xs : Vec A m) {ys zs} → ys ≈[ m≡n ] zs → xs ≡ ys → xs ≈[ m≡n ] zs
  step-≂-⟩ xs ys≈zs xs≡ys = ≈-trans (≈-reflexive xs≡ys) ys≈zs

  step-≂-⟨ : ∀ .{m≡n : m ≡ n} (xs : Vec A m) {ys zs} → ys ≈[ m≡n ] zs → ys ≡ xs → xs ≈[ m≡n ] zs
  step-≂-⟨ xs ys≈zs ys≡xs = step-≂-⟩ xs ys≈zs (sym ys≡xs)

  -- `cong` after a `_≈[_]_` step that exposes the `cast` to the `cong`
  -- operation
  ≈-cong : ∀ .{l≡o : l ≡ o} .{m≡n : m ≡ n} {xs : Vec A m} {ys zs} (f : Vec A o → Vec A n) →
           xs ≈[ m≡n ] f (cast l≡o ys) → ys ≈[ l≡o ] zs → xs ≈[ m≡n ] f zs
  ≈-cong f xs≈fys ys≈zs = trans xs≈fys (cong f ys≈zs)

  ------------------------------------------------------------------------
  -- convenient syntax for ‘equational’ reasoning

  infix 1 begin_
  infixr 2 step-≃-⟩ step-≃-⟨ step-≂-⟩ step-≂-⟨ step-≈-⟩ step-≈-⟨ _≈⟨⟩_ ≈-cong
  infix 3 _∎

  syntax step-≃-⟩ xs ys≡zs xs≈ys  = xs ≃⟨ xs≈ys ⟩ ys≡zs
  syntax step-≃-⟨ xs ys≡zs xs≈ys  = xs ≃⟨ xs≈ys ⟨ ys≡zs
  syntax step-≂-⟩ xs ys≈zs xs≡ys  = xs ≂⟨ xs≡ys ⟩ ys≈zs
  syntax step-≂-⟨ xs ys≈zs ys≡xs  = xs ≂⟨ ys≡xs ⟨ ys≈zs
  syntax step-≈-⟩ xs ys≈zs xs≈ys  = xs ≈⟨ xs≈ys ⟩ ys≈zs
  syntax step-≈-⟨ xs ys≈zs ys≈xs  = xs ≈⟨ ys≈xs ⟨ ys≈zs
