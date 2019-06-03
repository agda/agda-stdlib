------------------------------------------------------------------------
-- The Agda standard library
--
-- Literals used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Literal where

import Data.Char as Char
import Data.Float as Float
import Data.Nat as ℕ
import Data.Nat.Show as ℕ
open import Data.String as String using (String)
import Data.Word as Word
import Reflection.Meta as Meta
import Reflection.Name as Name
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Re-exporting the builtin type and constructors

open import Agda.Builtin.Reflection public
  using ( Literal )
open Literal public

show : Literal → String
show (nat x)    = ℕ.show x
show (word64 x) = ℕ.show (Word.toℕ x)
show (float x)  = Float.show x
show (char x)   = Char.show x
show (string x) = String.show x
show (name x)   = Name.show x
show (meta x)   = Meta.show x

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
_≟_ : Decidable (_≡_ {A = Literal})
nat x ≟ nat x₁ = Dec.map′ (cong nat) nat-injective (x ℕ.≟ x₁)
nat x ≟ word64 x₁ = no (λ ())
nat x ≟ float x₁ = no (λ ())
nat x ≟ char x₁ = no (λ ())
nat x ≟ string x₁ = no (λ ())
nat x ≟ name x₁ = no (λ ())
nat x ≟ meta x₁ = no (λ ())
word64 x ≟ word64 x₁ = Dec.map′ (cong word64) word64-injective (x Word.≟ x₁)
word64 x ≟ nat x₁ = no (λ ())
word64 x ≟ float x₁ = no (λ ())
word64 x ≟ char x₁ = no (λ ())
word64 x ≟ string x₁ = no (λ ())
word64 x ≟ name x₁ = no (λ ())
word64 x ≟ meta x₁ = no (λ ())
float x ≟ nat x₁ = no (λ ())
float x ≟ word64 x₁ = no (λ ())
float x ≟ float x₁ = Dec.map′ (cong float) float-injective (x Float.≟ x₁)
float x ≟ char x₁ = no (λ ())
float x ≟ string x₁ = no (λ ())
float x ≟ name x₁ = no (λ ())
float x ≟ meta x₁ = no (λ ())
char x ≟ nat x₁ = no (λ ())
char x ≟ word64 x₁ = no (λ ())
char x ≟ float x₁ = no (λ ())
char x ≟ char x₁ = Dec.map′ (cong char) char-injective (x Char.≟ x₁)
char x ≟ string x₁ = no (λ ())
char x ≟ name x₁ = no (λ ())
char x ≟ meta x₁ = no (λ ())
string x ≟ nat x₁ = no (λ ())
string x ≟ word64 x₁ = no (λ ())
string x ≟ float x₁ = no (λ ())
string x ≟ char x₁ = no (λ ())
string x ≟ string x₁ = Dec.map′ (cong string) string-injective (x String.≟ x₁)
string x ≟ name x₁ = no (λ ())
string x ≟ meta x₁ = no (λ ())
name x ≟ nat x₁ = no (λ ())
name x ≟ word64 x₁ = no (λ ())
name x ≟ float x₁ = no (λ ())
name x ≟ char x₁ = no (λ ())
name x ≟ string x₁ = no (λ ())
name x ≟ name x₁ = Dec.map′ (cong name) name-injective (x Name.≟ x₁)
name x ≟ meta x₁ = no (λ ())
meta x ≟ nat x₁ = no (λ ())
meta x ≟ word64 x₁ = no (λ ())
meta x ≟ float x₁ = no (λ ())
meta x ≟ char x₁ = no (λ ())
meta x ≟ string x₁ = no (λ ())
meta x ≟ name x₁ = no (λ ())
meta x ≟ meta x₁ = Dec.map′ (cong meta) meta-injective (x Meta.≟ x₁)
