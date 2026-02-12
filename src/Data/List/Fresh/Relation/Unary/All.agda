------------------------------------------------------------------------
-- The Agda standard library
--
-- All predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Fresh.Relation.Unary.All where

open import Data.List.Fresh using (List#; []; cons; _∷#_; _#_)
open import Data.List.Fresh.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Product.Base using (_×_; _,_; proj₁; uncurry)
open import Data.Sum.Base as Sum using (inj₁; inj₂; [_,_]′)
open import Function.Base using (_∘_; _$_)
open import Level using (Level; _⊔_; Lift)
open import Relation.Nullary.Decidable.Core as Dec using (Dec; yes; no; _×?_)
open import Relation.Unary as Unary
  using (Pred; IUniversal; Universal; Decidable; _⇒_; _∪_; _∩_)
open import Relation.Binary.Core using (Rel)


private
  variable
    a p q r : Level
    A : Set a
    R : Rel A r
    P : Pred A p
    Q : Pred A q
    x : A
    xs : List# A R


module _ {A : Set a} {R : Rel A r} (P : Pred A p) where

  infixr 5 _∷_

  data All : List# A R → Set (p ⊔ a ⊔ r) where
    []  : All []
    _∷_ : ∀ {x xs pr} → P x → All xs → All (cons x xs pr)


uncons : ∀ {pr} → All P (cons x xs pr) → P x × All P xs
uncons (p ∷ ps) = p , ps

append   : (xs ys : List# A R) → All (_# ys) xs → List# A R
append-# : ∀ xs ys {ps} → x # xs → x # ys → x # append {R = R} xs ys ps

append []             ys _  = ys
append (cons x xs pr) ys ps =
  let (p , ps) = uncons ps in
  cons x (append xs ys ps) (append-# xs ys pr p)

append-# []             ys x#xs       x#ys = x#ys
append-# (cons x xs pr) ys (r , x#xs) x#ys = r , append-# xs ys x#xs x#ys

map : ∀[ P ⇒ Q ] → All P xs → All Q xs
map p⇒q []       = []
map p⇒q (p ∷ ps) = p⇒q p ∷ map p⇒q ps

lookup : All Q xs → (ps : Any P xs) → Q (proj₁ (Any.witness ps))
lookup (q ∷ _)  (here _)  = q
lookup (_ ∷ qs) (there k) = lookup qs k

module _ (P? : Decidable P) where

  all? : ∀ xs → Dec (All {R = R} P xs)
  all? []        = yes []
  all? (x ∷# xs) = Dec.map′ (uncurry _∷_) uncons (P? x ×? all? xs)

------------------------------------------------------------------------
-- Generalised decidability procedure

decide :  Π[ P ∪ Q ] → Π[ All {R = R} P ∪ Any Q ]
decide p∪q [] = inj₁ []
decide p∪q (x ∷# xs) =
  [ (λ px → Sum.map (px ∷_) there (decide p∪q xs))
  , inj₂ ∘ here
  ]′ $ p∪q x
