{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Apartness where

open import Relation.Binary
open import Level using (Level; _⊔_)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂; map)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)


module Props {a r1} {A : Set a} (_#_ : Rel A r1) where

  _¬#_ : A → A → Set r1
  x ¬# y = ¬ (x # y)


  sym⇒sym-¬ : Symmetric _#_ → Symmetric _¬#_
  sym⇒sym-¬ sym# x¬#y y#x = x¬#y (sym# y#x)


  Comparison : Set _
  Comparison = ∀ {x y z} → x # z → (x # y) ⊎ (y # z)


  comp⇒trans-¬ : Comparison → Transitive _¬#_
  comp⇒trans-¬ comp x¬#y y¬#z x#z = [ x¬#y , y¬#z ]′ (comp x#z)


module _ {a r1 r2} {A : Set a} (_≈_ : Rel A r1) (_#_ : Rel A r2) where

  open Props _#_

  irrefl⇒refl-¬ : Reflexive _≈_ → Irreflexive _≈_ _#_ → Reflexive _¬#_
  irrefl⇒refl-¬ re irr = irr re


  record IsApartness : Set (a ⊔ r1 ⊔ r2) where
    field
      irrefl : Irreflexive _≈_ _#_
      sym    : Symmetric _#_
      comp   : Comparison


  ¬#-equiv : Reflexive _≈_ → IsApartness → IsEquivalence _¬#_
  ¬#-equiv re apart =
    record { refl = irrefl⇒refl-¬ re irrefl ; sym = sym⇒sym-¬ sym ; trans = comp⇒trans-¬ comp }
    where open IsApartness apart


  Tight : Set _
  Tight = ∀ {x y} → (x ¬# y) × (y ¬# x) → x ≈ y


module Test where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  data _#_ : ℕ → ℕ → Set where
    z#s : ∀ {m : ℕ} → zero # suc m
    s#z : ∀ {m : ℕ} → suc m # zero
    s#s : ∀ {m n : ℕ} → m # n → suc m # suc n

  open Props _#_

  #-reduce : ∀ {m n : ℕ} → suc m # suc n → m # n
  #-reduce (s#s x) = x


  #-irrefl : Irreflexive _≡_ _#_
  #-irrefl {zero} {zero} refl ()
  #-irrefl refl (s#s x) = #-irrefl refl x


  #-sym : Symmetric _#_
  #-sym z#s = s#z
  #-sym s#z = z#s
  #-sym (s#s x) = s#s (#-sym x)


  #-comp : Comparison
  #-comp {y = zero} z#s = inj₂ z#s
  #-comp {y = suc _} z#s = inj₁ z#s
  #-comp {y = zero} s#z = inj₁ s#z
  #-comp {y = suc _} s#z = inj₂ s#z
  #-comp {y = zero} (s#s x#z) = inj₁ s#z
  #-comp {y = suc _} (s#s x#z) = map s#s s#s (#-comp x#z)


  #-apart : IsApartness _≡_ _#_
  #-apart = record { irrefl = #-irrefl ; sym = #-sym ; comp = #-comp }
  

  #-tight : Tight _≡_ _#_
  #-tight {zero} {zero} _ = refl
  #-tight {suc x} {zero} (¬x#y , _) with ¬x#y s#z
  ... | ()
  #-tight {zero} {suc y} (_ , ¬y#x) with ¬y#x s#z
  ... | ()
  #-tight {suc x} {suc y} (¬sx#sy , ¬sy#sx) =
    cong suc (#-tight (¬sx#sy ∘ s#s , ¬sy#sx ∘ s#s))