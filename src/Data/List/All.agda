------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where all elements satisfy a given property
------------------------------------------------------------------------

module Data.List.All where

open import Category.Applicative
open import Category.Monad
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Any as Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product as Prod using (_,_)
open import Function
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality as P

------------------------------------------------------------------------
-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {a p} {A : Set a} (P : Pred A p) : Pred (List A) p where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Operations on All

head : ∀ {a p} {A : Set a} {P : Pred A p} {x xs} →
       All P (x ∷ xs) → P x
head (px ∷ pxs) = px

tail : ∀ {a p} {A : Set a} {P : Pred A p} {x xs} →
       All P (x ∷ xs) → All P xs
tail (px ∷ pxs) = pxs

lookup : ∀ {a p} {A : Set a} {P : Pred A p} {xs : List A} →
         All P xs → (∀ {x} → x ∈ xs → P x)
lookup []         ()
lookup (px ∷ pxs) (here refl)  = px
lookup (px ∷ pxs) (there x∈xs) = lookup pxs x∈xs

tabulate : ∀ {a p} {A : Set a} {P : Pred A p} {xs} →
           (∀ {x} → x ∈ xs → P x) → All P xs
tabulate {xs = []}     hyp = []
tabulate {xs = x ∷ xs} hyp = hyp (here refl) ∷ tabulate (hyp ∘ there)

map : ∀ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} →
      P ⊆ Q → All P ⊆ All Q
map g []         = []
map g (px ∷ pxs) = g px ∷ map g pxs

------------------------------------------------------------------------
-- (un/)zip(With/)

module _ {a p q r} {A : Set a} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

  zipWith : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
  zipWith f ([] , [])             = []
  zipWith f (px ∷ pxs , qx ∷ qxs) = f (px , qx) ∷ zipWith f (pxs , qxs)

  unzipWith : R ⊆ P ∩ Q → All R ⊆ All P ∩ All Q
  unzipWith f []         = [] , []
  unzipWith f (rx ∷ rxs) = Prod.zip _∷_ _∷_ (f rx) (unzipWith f rxs)

module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where

  zip : All P ∩ All Q ⊆ All (P ∩ Q)
  zip = zipWith id

  unzip : All (P ∩ Q) ⊆ All P ∩ All Q
  unzip = unzipWith id

------------------------------------------------------------------------
-- Traversable-like functions

module _ {a p} {A : Set a} {P : Pred A p} {F} (App : RawApplicative {p} F) where

  open RawApplicative App

  sequenceA : All (F ∘′ P) ⊆ F ∘′ All P
  sequenceA []       = pure []
  sequenceA (x ∷ xs) = _∷_ <$> x ⊛ sequenceA xs

  mapA : ∀ {q} {Q : Pred A q} → (Q ⊆ F ∘′ P) → All Q ⊆ (F ∘′ All P)
  mapA f = sequenceA ∘′ map f

  forA : ∀ {q} {Q : Pred A q} {xs} → All Q xs → (Q ⊆ F ∘′ P) → F (All P xs)
  forA qxs f = mapA f qxs

module _ {a p} {A : Set a} {P : Pred A p} {M} (Mon : RawMonad {p} M) where

  private App = RawMonad.rawIApplicative Mon

  sequenceM : All (M ∘′ P) ⊆ M ∘′ All P
  sequenceM = sequenceA App

  mapM : ∀ {q} {Q : Pred A q} → (Q ⊆ M ∘′ P) → All Q ⊆ (M ∘′ All P)
  mapM = mapA App

  forM : ∀ {q} {Q : Pred A q} {xs} → All Q xs → (Q ⊆ M ∘′ P) → M (All P xs)
  forM = forA App

------------------------------------------------------------------------
-- Properties of predicates preserved by All

module _ {a p} {A : Set a} {P : Pred A p} where

  all : Decidable P → Decidable (All P)
  all p []       = yes []
  all p (x ∷ xs) with p x
  ... | yes px = Dec.map′ (px ∷_) tail (all p xs)
  ... | no ¬px = no (¬px ∘ head)

  universal : Universal P → Universal (All P)
  universal u []       = []
  universal u (x ∷ xs) = u x ∷ universal u xs

  irrelevant : Irrelevant P → Irrelevant (All P)
  irrelevant irr []           []           = P.refl
  irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
    P.cong₂ _∷_ (irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

  satisfiable : Satisfiable (All P)
  satisfiable = [] , []
