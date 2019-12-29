------------------------------------------------------------------------
-- The Agda standard library
--
-- Bisimilarity for Cowriter
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.Cowriter.Bisimilarity where

open import Level using (Level; _⊔_)
open import Size
open import Codata.Thunk
open import Codata.Cowriter
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

private
  variable
    a b c p q pq r s rs v w x : Level
    A : Set a
    B : Set b
    C : Set c
    V : Set v
    W : Set w
    X : Set x
    i : Size

data Bisim {V : Set v} {W : Set w} {A : Set a} {B : Set b}
           (R : REL V W r) (S : REL A B s) (i : Size) :
           REL (Cowriter V A ∞) (Cowriter W B ∞) (r ⊔ s ⊔ v ⊔ w ⊔ a ⊔ b) where
  [_] : ∀ {a b} → S a b → Bisim R S i [ a ] [ b ]
  _∷_ : ∀ {x y xs ys} → R x y → Thunk^R (Bisim R S) i xs ys →
        Bisim R S i (x ∷ xs) (y ∷ ys)

module _ {R : Rel W r} {S : Rel A s}
         (refl^R : Reflexive R) (refl^S : Reflexive S) where

 reflexive : Reflexive (Bisim R S i)
 reflexive {x = [ a ]}  = [ refl^S ]
 reflexive {x = w ∷ ws} = refl^R ∷ λ where .force → reflexive

module _ {R : REL V W r} {S : REL W V s} {P : REL A B p} {Q : REL B A q}
         (sym^RS : Sym R S) (sym^PQ : Sym P Q) where

 symmetric : Sym (Bisim R P i) (Bisim S Q i)
 symmetric [ a ]    = [ sym^PQ a ]
 symmetric (p ∷ ps) = sym^RS p ∷ λ where .force → symmetric (ps .force)


module _ {R : REL V W r} {S : REL W X s} {RS : REL V X rs}
         {P : REL A B p} {Q : REL B C q} {PQ : REL A C pq}
         (trans^RS : Trans R S RS) (trans^PQ : Trans P Q PQ) where

 transitive : Trans (Bisim R P i) (Bisim S Q i) (Bisim RS PQ i)
 transitive [ p ]    [ q ]    = [ trans^PQ p q ]
 transitive (p ∷ ps) (q ∷ qs) =
   trans^RS p q ∷ λ where .force → transitive (ps .force) (qs .force)

-- Pointwise Equality as a Bisimilarity
------------------------------------------------------------------------

module _ {W : Set w} {A : Set a} where

  infix 1 _⊢_≈_
  _⊢_≈_ : ∀ i → Cowriter W A ∞ → Cowriter W A ∞ → Set (a ⊔ w)
  _⊢_≈_ = Bisim _≡_ _≡_

  refl : Reflexive (i ⊢_≈_)
  refl = reflexive Eq.refl Eq.refl

  fromEq : ∀ {as bs} → as ≡ bs → i ⊢ as ≈ bs
  fromEq Eq.refl = refl

  sym : Symmetric (i ⊢_≈_)
  sym = symmetric Eq.sym Eq.sym

  trans : Transitive (i ⊢_≈_)
  trans = transitive Eq.trans Eq.trans

module _ {R : Rel W r} {S : Rel A s}
         (equiv^R : IsEquivalence R) (equiv^S : IsEquivalence S) where

  private
    module equiv^R = IsEquivalence equiv^R
    module equiv^S = IsEquivalence equiv^S

  isEquivalence : IsEquivalence (Bisim R S i)
  isEquivalence = record
    { refl  = reflexive equiv^R.refl equiv^S.refl
    ; sym   = symmetric equiv^R.sym equiv^S.sym
    ; trans = transitive equiv^R.trans equiv^S.trans
    }

setoid : Setoid w r → Setoid a s → Size → Setoid (w ⊔ a) (w ⊔ a ⊔ r ⊔ s)
setoid R S i = record
  { isEquivalence = isEquivalence (Setoid.isEquivalence R)
                                  (Setoid.isEquivalence S) {i = i}
  }

module ≈-Reasoning {W : Set w} {A : Set a} {i} where

  open import Relation.Binary.Reasoning.Setoid
              (setoid (Eq.setoid W) (Eq.setoid A) i) public
