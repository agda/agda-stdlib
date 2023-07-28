------------------------------------------------------------------------
-- The Agda standard library
--
-- Literals used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Literal where

open import Data.Bool.Base   using (Bool; true; false)
import Data.Char as Char     using (_≟_)
import Data.Float as Float   using (_≟_)
import Data.Nat as ℕ        using (_≟_)
import Data.String as String using (_≟_)
import Data.Word as Word     using (_≟_)
import Reflection.AST.Meta as Meta
import Reflection.AST.Name as Name
open import Relation.Nullary                           using (yes; no)
open import Relation.Nullary.Decidable                 using (map′; isYes)
open import Relation.Binary                            using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Re-exporting the builtin type and constructors

open import Agda.Builtin.Reflection public
  using ( Literal )
open Literal public

------------------------------------------------------------------------
-- Decidable equality

meta-injective : ∀ {x y} → meta x ≡ meta y → x ≡ y
meta-injective refl = refl

nat-injective : ∀ {x y} → nat x ≡ nat y → x ≡ y
nat-injective refl = refl

word64-injective : ∀ {x y} → word64 x ≡ word64 y → x ≡ y
word64-injective refl = refl

float-injective : ∀ {x y} → float x ≡ float y → x ≡ y
float-injective refl = refl

char-injective : ∀ {x y} → char x ≡ char y → x ≡ y
char-injective refl = refl

string-injective : ∀ {x y} → string x ≡ string y → x ≡ y
string-injective refl = refl

name-injective : ∀ {x y} → name x ≡ name y → x ≡ y
name-injective refl = refl

infix 4 _≟_
_≟_ : DecidableEquality Literal
nat x ≟ nat x₁ = map′ (cong nat) nat-injective (x ℕ.≟ x₁)
nat x ≟ word64 x₁ = no (λ ())
nat x ≟ float x₁ = no (λ ())
nat x ≟ char x₁ = no (λ ())
nat x ≟ string x₁ = no (λ ())
nat x ≟ name x₁ = no (λ ())
nat x ≟ meta x₁ = no (λ ())
word64 x ≟ word64 x₁ = map′ (cong word64) word64-injective (x Word.≟ x₁)
word64 x ≟ nat x₁ = no (λ ())
word64 x ≟ float x₁ = no (λ ())
word64 x ≟ char x₁ = no (λ ())
word64 x ≟ string x₁ = no (λ ())
word64 x ≟ name x₁ = no (λ ())
word64 x ≟ meta x₁ = no (λ ())
float x ≟ nat x₁ = no (λ ())
float x ≟ word64 x₁ = no (λ ())
float x ≟ float x₁ = map′ (cong float) float-injective (x Float.≟ x₁)
float x ≟ char x₁ = no (λ ())
float x ≟ string x₁ = no (λ ())
float x ≟ name x₁ = no (λ ())
float x ≟ meta x₁ = no (λ ())
char x ≟ nat x₁ = no (λ ())
char x ≟ word64 x₁ = no (λ ())
char x ≟ float x₁ = no (λ ())
char x ≟ char x₁ = map′ (cong char) char-injective (x Char.≟ x₁)
char x ≟ string x₁ = no (λ ())
char x ≟ name x₁ = no (λ ())
char x ≟ meta x₁ = no (λ ())
string x ≟ nat x₁ = no (λ ())
string x ≟ word64 x₁ = no (λ ())
string x ≟ float x₁ = no (λ ())
string x ≟ char x₁ = no (λ ())
string x ≟ string x₁ = map′ (cong string) string-injective (x String.≟ x₁)
string x ≟ name x₁ = no (λ ())
string x ≟ meta x₁ = no (λ ())
name x ≟ nat x₁ = no (λ ())
name x ≟ word64 x₁ = no (λ ())
name x ≟ float x₁ = no (λ ())
name x ≟ char x₁ = no (λ ())
name x ≟ string x₁ = no (λ ())
name x ≟ name x₁ = map′ (cong name) name-injective (x Name.≟ x₁)
name x ≟ meta x₁ = no (λ ())
meta x ≟ nat x₁ = no (λ ())
meta x ≟ word64 x₁ = no (λ ())
meta x ≟ float x₁ = no (λ ())
meta x ≟ char x₁ = no (λ ())
meta x ≟ string x₁ = no (λ ())
meta x ≟ name x₁ = no (λ ())
meta x ≟ meta x₁ = map′ (cong meta) meta-injective (x Meta.≟ x₁)

infix 4 _≡ᵇ_

_≡ᵇ_ : Literal → Literal → Bool
l ≡ᵇ l′ = isYes (l ≟ l′)
