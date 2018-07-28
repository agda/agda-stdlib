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

EdgePred : {ℓ r : Level} (p : Level) {I : Set ℓ} → Rel I r → Set (suc p ⊔ ℓ ⊔ r)
EdgePred p T = ∀ {i j} → T i j → Set p

module _  where

data NonEmptyEdgePred {ℓ r p : Level} {I : Set ℓ} (T : Rel I r)
    (P : EdgePred p T) : Set (ℓ ⊔ r ⊔ p) where
  nonEmptyEdgePred : ∀ {i j} {x : T i j}
                     (p : P x) → NonEmptyEdgePred T P

-- Decorating an edge with more information.

data DecoratedWith {ℓ r p : Level} {I : Set ℓ} {T : Rel I r} (P : EdgePred p T)
       : Rel (NonEmpty (Star T)) p where
  ↦ : ∀ {i j k} {x : T i j} {xs : Star T j k}
      (p : P x) → DecoratedWith P (nonEmpty (x ◅ xs)) (nonEmpty xs)

module _ {ℓ r p : Level} {I : Set ℓ} {T : Rel I r} {P : EdgePred p T} where

  edge : ∀ {i j} → DecoratedWith {T = T} P i j → NonEmpty T
  edge (↦ {x = x} p) = nonEmpty x

  decoration : ∀ {i j} → (d : DecoratedWith {T = T} P i j) →
               P (NonEmpty.proof (edge d))
  decoration (↦ p) = p

-- Star-lists decorated with extra information. All P xs means that
-- all edges in xs satisfy P.

All : ∀ {ℓ r p} {I : Set ℓ} {T : Rel I r} → EdgePred p T → EdgePred (ℓ ⊔ (r ⊔ p)) (Star T)
All P {j = j} xs =
  Star (DecoratedWith P) (nonEmpty xs) (nonEmpty {y = j} ε)

-- We can map over decorated vectors.

gmapAll : ∀ {ℓ ℓ′ r p q} {I : Set ℓ} {T : Rel I r} {P : EdgePred p T}
                {J : Set ℓ′} {U : Rel J r} {Q : EdgePred q U}
                {i j} {xs : Star T i j}
          (f : I → J) (g : T =[ f ]⇒ U) →
          (∀ {i j} {x : T i j} → P x → Q (g x)) →
          All P xs → All {T = U} Q (gmap f g xs)
gmapAll f g h ε          = ε
gmapAll f g h (↦ x ◅ xs) = ↦ (h x) ◅ gmapAll f g h xs

-- Since we don't automatically have gmap id id xs ≡ xs it is easier
-- to implement mapAll in terms of map than in terms of gmapAll.

mapAll : ∀ {ℓ r p q} {I : Set ℓ} {T : Rel I r}
         {P : EdgePred p T} {Q : EdgePred q T} {i j} {xs : Star T i j} →
         (∀ {i j} {x : T i j} → P x → Q x) →
         All P xs → All Q xs
mapAll {P = P} {Q} f ps = map F ps
  where
  F : DecoratedWith P ⇒ DecoratedWith Q
  F (↦ x) = ↦ (f x)

-- We can decorate star-lists with universally true predicates.

decorate : ∀ {ℓ r p} {I : Set ℓ} {T : Rel I r} {P : EdgePred p T} {i j} →
           (∀ {i j} (x : T i j) → P x) →
           (xs : Star T i j) → All P xs
decorate f ε        = ε
decorate f (x ◅ xs) = ↦ (f x) ◅ decorate f xs

-- We can append Alls. Unfortunately _◅◅_ does not quite work.

infixr 5 _◅◅◅_ _▻▻▻_

_◅◅◅_ : ∀ {ℓ r p} {I : Set ℓ} {T : Rel I r} {P : EdgePred p T}
              {i j k} {xs : Star T i j} {ys : Star T j k} →
        All P xs → All P ys → All P (xs ◅◅ ys)
ε          ◅◅◅ ys = ys
(↦ x ◅ xs) ◅◅◅ ys = ↦ x ◅ xs ◅◅◅ ys

_▻▻▻_ : ∀ {ℓ r p} {I : Set ℓ} {T : Rel I r} {P : EdgePred p T}
              {i j k} {xs : Star T j k} {ys : Star T i j} →
        All P xs → All P ys → All P (xs ▻▻ ys)
_▻▻▻_ = flip _◅◅◅_
