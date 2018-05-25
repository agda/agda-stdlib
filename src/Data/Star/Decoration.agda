------------------------------------------------------------------------
-- The Agda standard library
--
-- Decorated star-lists
------------------------------------------------------------------------

module Data.Star.Decoration where

open import Data.Unit
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.Closure.ReflexiveTransitive

-- A predicate on relation "edges" (think of the relation as a graph).

EdgePred : {ℓ r : Level} {I : Set ℓ} → Rel I r → Set (suc r ⊔ ℓ)
EdgePred {r = r} T = ∀ {i j} → T i j → Set r

data NonEmptyEdgePred {ℓ r : Level} {I : Set ℓ}
                      (T : Rel I r) (P : EdgePred T) : Set (ℓ ⊔ r) where
  nonEmptyEdgePred : ∀ {i j} {x : T i j}
                     (p : P x) → NonEmptyEdgePred T P

-- Decorating an edge with more information.

data DecoratedWith {ℓ r : Level} {I : Set ℓ} {T : Rel I r} (P : EdgePred T)
       : Rel (NonEmpty (Star T)) r where
  ↦ : ∀ {i j k} {x : T i j} {xs : Star T j k}
      (p : P x) → DecoratedWith P (nonEmpty (x ◅ xs)) (nonEmpty xs)

edge : ∀ {ℓ r} {I : Set ℓ} {T : Rel I r} {P : EdgePred T} {i j} →
       DecoratedWith {T = T} P i j → NonEmpty T
edge (↦ {x = x} p) = nonEmpty x

decoration : ∀ {ℓ r} {I : Set ℓ} {T : Rel I r} {P : EdgePred T} {i j} →
             (d : DecoratedWith {T = T} P i j) →
             P (NonEmpty.proof (edge d))
decoration (↦ p) = p

-- Star-lists decorated with extra information. All P xs means that
-- all edges in xs satisfy P.

All : ∀ {ℓ r} {I : Set ℓ} {T : Rel I r} → EdgePred T → EdgePred (Star T)
All P {j = j} xs =
  Star (DecoratedWith P) (nonEmpty xs) (nonEmpty {y = j} ε)

-- We can map over decorated vectors.

gmapAll : ∀ {ℓ ℓ′ r} {I : Set ℓ} {T : Rel I r} {P : EdgePred T}
                {J : Set ℓ′} {U : Rel J r} {Q : EdgePred U}
                {i j} {xs : Star T i j}
          (f : I → J) (g : T =[ f ]⇒ U) →
          (∀ {i j} {x : T i j} → P x → Q (g x)) →
          All P xs → All {T = U} Q (gmap f g xs)
gmapAll f g h ε          = ε
gmapAll f g h (↦ x ◅ xs) = ↦ (h x) ◅ gmapAll f g h xs

-- Since we don't automatically have gmap id id xs ≡ xs it is easier
-- to implement mapAll in terms of map than in terms of gmapAll.

mapAll : ∀ {ℓ r} {I : Set ℓ} {T : Rel I r} {P Q : EdgePred T} {i j} {xs : Star T i j} →
         (∀ {i j} {x : T i j} → P x → Q x) →
         All P xs → All Q xs
mapAll {P = P} {Q} f ps = map F ps
  where
  F : DecoratedWith P ⇒ DecoratedWith Q
  F (↦ x) = ↦ (f x)

-- We can decorate star-lists with universally true predicates.

decorate : ∀ {ℓ r} {I : Set ℓ} {T : Rel I r} {P : EdgePred T} {i j} →
           (∀ {i j} (x : T i j) → P x) →
           (xs : Star T i j) → All P xs
decorate f ε        = ε
decorate f (x ◅ xs) = ↦ (f x) ◅ decorate f xs

-- We can append Alls. Unfortunately _◅◅_ does not quite work.

infixr 5 _◅◅◅_ _▻▻▻_

_◅◅◅_ : ∀ {ℓ r} {I : Set ℓ} {T : Rel I r} {P : EdgePred T}
              {i j k} {xs : Star T i j} {ys : Star T j k} →
        All P xs → All P ys → All P (xs ◅◅ ys)
ε          ◅◅◅ ys = ys
(↦ x ◅ xs) ◅◅◅ ys = ↦ x ◅ xs ◅◅◅ ys

_▻▻▻_ : ∀ {ℓ r} {I : Set ℓ} {T : Rel I r} {P : EdgePred T}
              {i j k} {xs : Star T j k} {ys : Star T i j} →
        All P xs → All P ys → All P (xs ▻▻ ys)
_▻▻▻_ = flip _◅◅◅_
