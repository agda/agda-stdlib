------------------------------------------------------------------------
-- The Agda standard library
--
-- Levenshtein distance: the Edit relation and its properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}


module Data.List.Relation.Binary.Distance.Levenshtein.Edit.Heterogeneous where

open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Nat.Base using (ℕ; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (0≢1+n; 1+n≰n; ≤-reflexive; ≤-trans; +-suc; n≤1+n; +-monoʳ-≤)
open import Data.Product.Base using (∃; _×_; _,_)

open import Level using (Level; _⊔_)

open import Relation.Binary using (REL; Reflexive; Sym; Trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary.Negation using (¬_)

private
  variable
    a b c r s t : Level
    A : Set a
    B : Set b
    C : Set c
    R : REL A B r
    S : REL B A s
    T : REL A C t
    x : A
    y : B
    xs : List A
    ys : List B
    zs : List C
    k l m : ℕ

------------------------------------------------------------------------
-- Inductive definition of the relation and basic property

data Edit (R : REL {a} {b} A B r) :
  (xs : List A) (ys : List B) → ℕ → Set (a ⊔ b ⊔ r) where
  done :                          Edit R []       []       0
  delL : Edit R xs ys k →         Edit R (x ∷ xs) ys       (1 + k)
  delR : Edit R xs ys k →         Edit R xs       (y ∷ ys) (1 + k)
  skip : R x y → Edit R xs ys k → Edit R (x ∷ xs) (y ∷ ys) k
  swap : Edit R xs ys k →         Edit R (x ∷ xs) (y ∷ ys) (1 + k)

cast : k ≡ l → Edit R xs ys k → Edit R xs ys l
cast refl edit = edit

------------------------------------------------------------------------
-- The relation is a pseudo-distance

-- There is a 0-valued edit from each point to itself
module _ (R-refl : Reflexive R) where

  reflexive : Edit R xs xs 0
  reflexive {xs = []}     = done
  reflexive {xs = x ∷ xs} = skip R-refl reflexive

-- Two lists of related values have a 0-valued edit
fromPointwise : Pointwise R xs ys → Edit R xs ys 0
fromPointwise []         = done
fromPointwise (x∼y ∷ pw) = skip x∼y (fromPointwise pw)

-- Conversely, a 0-valued edit means the lists are pointwise related
toPointwise : Edit R xs ys 0 → Pointwise R xs ys
toPointwise done            = []
toPointwise (skip x∼y edit) = x∼y ∷ toPointwise edit

-- The relation is symmetric
module _ (RS-sym : Sym R S) where

  symmetric : Edit R xs ys k → Edit S ys xs k
  symmetric done            = done
  symmetric (delL edit)     = delR (symmetric edit)
  symmetric (delR edit)     = delL (symmetric edit)
  symmetric (skip x∼y edit) = skip (RS-sym x∼y) (symmetric edit)
  symmetric (swap edit)     = swap (symmetric edit)

-- The relation is sub-additive
module _ (RST-trans : Trans R S T) where

  compose : Edit R xs ys k → Edit S ys zs l →
    ∃ λ m → Edit T xs zs m × m ≤ k + l
  compose done done = 0 , done , z≤n
  compose dlm (delR dmr) =
    let (m , dlr , m≤) = compose dlm dmr in
    1 + m , delR dlr , ≤-trans (s≤s m≤) (≤-reflexive (sym (+-suc _ _)))
  compose (delL dlm) dmr =
    let (m , dlr , m≤) = compose dlm dmr in
    1 + m , delL dlr , s≤s m≤
  compose (delR dlm) (delL dmr) =
    let (m , dlr , m≤) = compose dlm dmr in
    m , dlr , ≤-trans m≤ (≤-trans (n≤1+n _) (s≤s (+-monoʳ-≤ _ (n≤1+n _))))
  compose (delR dlm) (skip x∼y dmr) =
    let (m , dlr , m≤) = compose dlm dmr in
    1 + m , delR dlr , s≤s m≤
  compose (delR dlm) (swap dmr) =
    let (m , dlr , m≤ ) = compose dlm dmr in
    1 + m , delR dlr , s≤s (≤-trans m≤ (+-monoʳ-≤ _ (n≤1+n _)))
  compose (skip x∼y dlm) (delL dmr) =
    let (m , dlr , m≤) = compose dlm dmr in
    1 + m , delL dlr , ≤-trans (s≤s m≤) (≤-reflexive (sym (+-suc _ _)))
  compose (skip x∼y dlm) (skip y∼z dmr) =
    let (m , dlr , m≤) = compose dlm dmr in
    m , skip (RST-trans x∼y y∼z) dlr , m≤
  compose (skip x∼y dlm) (swap dmr) =
    let (m , dlr , m≤) = compose dlm dmr in
    1 + m , swap dlr , ≤-trans (s≤s m≤) (≤-reflexive (sym (+-suc _ _)))
  compose (swap dlm) (delL dmr) =
    let (m , dlr , m≤) = compose dlm dmr in
    1 + m , delL dlr , s≤s (≤-trans (≤-trans m≤ (n≤1+n _)) (≤-reflexive (sym (+-suc _ _))))
  compose (swap dlm) (skip x∼y dmr) =
    let (m , dlr , m≤) = compose dlm dmr in
    1 + m , swap dlr , s≤s m≤
  compose (swap {k = k₁} dlm) (swap dmr) =
    let (m , dlr , m≤) = compose dlm dmr in
    1 + m , swap dlr , s≤s (≤-trans m≤ (+-monoʳ-≤ k₁ (n≤1+n _)))

-- Edit to the empty list
edit-[]ˡ : Edit R [] ys (length ys)
edit-[]ˡ {ys = []}     = done
edit-[]ˡ {ys = x ∷ ys} = delR edit-[]ˡ

edit-[]ʳ : Edit R xs [] (length xs)
edit-[]ʳ {xs = []}     = done
edit-[]ʳ {xs = x ∷ xs} = delL edit-[]ʳ
