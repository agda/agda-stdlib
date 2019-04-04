------------------------------------------------------------------------
-- The Agda standard library
--
-- Sorted lists (agnostic in whether the order is strict or not)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Sorted where

open import Level
open import Data.Maybe.Base
open import Data.Sum.Base
open import Function
open import Relation.Binary
open import Relation.Nullary.Construct.Add.Extrema as E

module _ {a r} {A : Set a} (_∼_ : Rel (A ±) r) where

  data Sorted (lb ub : A ±) : Set (a ⊔ r) where
    nil  : lb ∼ ub → Sorted lb ub
    cons : ∀ hd → lb ∼ [ hd ] → Sorted [ hd ] ub → Sorted lb ub

  module _ (∼-trans : Transitive _∼_) where

    downcast : ∀ {lb₁ lb₂ ub} → lb₁ ∼ lb₂ → Sorted lb₂ ub → Sorted lb₁ ub
    downcast lb₁∼lb₂ (nil lb₂∼ub)        = nil (∼-trans lb₁∼lb₂ lb₂∼ub)
    downcast lb₁∼lb₂ (cons hd lb₂∼hd xs) = cons hd (∼-trans lb₁∼lb₂ lb₂∼hd) xs

    _++_ : ∀ {lb mb ub} → Sorted lb mb → Sorted mb ub → Sorted lb ub
    nil lb∼mb        ++ ys = downcast lb∼mb ys
    cons hd lb∼hd xs ++ ys = cons hd lb∼hd (xs ++ ys)

  module _ (_∼?_ : ∀ a b → Maybe (a ∼ b ⊎ b ∼ a)) where

    insert : ∀ {lb ub} x → lb ∼ [ x ] → [ x ] ∼ ub → Sorted lb ub → Sorted lb ub
    insert x lb∼x x∼ub (nil lb~ub)        = cons x lb∼x (nil x∼ub)
    insert x lb∼x x∼ub xs@(cons hd lb∼hd tl) with [ x ] ∼? [ hd ]
    ... | just (inj₁ x∼hd) = cons x lb∼x (cons hd x∼hd tl)
    ... | nothing          = xs
    ... | just (inj₂ hd∼x) = cons hd lb∼hd (insert x hd∼x x∼ub tl)
