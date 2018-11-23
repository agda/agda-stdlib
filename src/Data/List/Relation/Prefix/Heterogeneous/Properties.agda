------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the heterogeneous prefix relation
------------------------------------------------------------------------

module Data.List.Relation.Prefix.Heterogeneous.Properties where

open import Data.Empty
open import Data.List.All as All using (All; []; _∷_)
import Data.List.All.Properties as All
open import Data.List.Base as List hiding (map; uncons)
open import Data.List.Membership.Propositional.Properties using ([]∈inits)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_; isEquivalence)
open import Data.List.Relation.Prefix.Heterogeneous as Prefix hiding (PrefixView; _++_)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂; uncurry)
open import Function

open import Relation.Nullary using (yes; no; ¬_)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary as U using (Pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

------------------------------------------------------------------------
-- First as a decidable partial order (once made homogeneous)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  fromPointwise : Pointwise R ⇒ Prefix R
  fromPointwise []       = []
  fromPointwise (r ∷ rs) = r ∷ fromPointwise rs

  toPointwise : ∀ {as bs} → length as ≡ length bs →
                Prefix R as bs → Pointwise R as bs
  toPointwise {bs = []} eq [] = []
  toPointwise {bs = _ ∷ _} () []
  toPointwise eq (r ∷ rs) = r ∷ toPointwise (suc-injective eq) rs

module _ {a b c r s t} {A : Set a} {B : Set b} {C : Set c}
         {R : REL A B r} {S : REL B C s} {T : REL A C t} where

  trans : Trans R S T → Trans (Prefix R) (Prefix S) (Prefix T)
  trans rs⇒t []       ss       = []
  trans rs⇒t (r ∷ rs) (s ∷ ss) = rs⇒t r s ∷ trans rs⇒t rs ss

module _ {a b r s e} {A : Set a} {B : Set b}
         {R : REL A B r} {S : REL B A s} {E : REL A B e} where

  antisym : Antisym R S E → Antisym (Prefix R) (Prefix S) (Pointwise E)
  antisym rs⇒e []       []       = []
  antisym rs⇒e (r ∷ rs) (s ∷ ss) = rs⇒e r s ∷ antisym rs⇒e rs ss

------------------------------------------------------------------------
-- length

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  length-mono-Prefix-≤ : ∀ {as bs} → Prefix R as bs → length as ≤ length bs
  length-mono-Prefix-≤ []       = z≤n
  length-mono-Prefix-≤ (r ∷ rs) = s≤s (length-mono-Prefix-≤ rs)

------------------------------------------------------------------------
-- _++_

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  ++⁺ : ∀ {as bs cs ds} → Pointwise R as bs →
        Prefix R cs ds → Prefix R (as ++ cs) (bs ++ ds)
  ++⁺ []       cs⊆ds = cs⊆ds
  ++⁺ (r ∷ rs) cs⊆ds = r ∷ (++⁺ rs cs⊆ds)

  ++⁻ : ∀ {as bs cs ds} → length as ≡ length bs →
        Prefix R (as ++ cs) (bs ++ ds) → Prefix R cs ds
  ++⁻ {[]}    {[]}    eq rs       = rs
  ++⁻ {_ ∷ _} {_ ∷ _} eq (_ ∷ rs) = ++⁻ (suc-injective eq) rs
  ++⁻ {[]} {_ ∷ _} ()
  ++⁻ {_ ∷ _} {[]} ()

------------------------------------------------------------------------
-- map

module _ {a b c d r} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {R : REL C D r} where

  map⁺ : ∀ {as bs} (f : A → C) (g : B → D) →
         Prefix (λ a b → R (f a) (g b)) as bs →
         Prefix R (List.map f as) (List.map g bs)
  map⁺ f g []       = []
  map⁺ f g (r ∷ rs) = r ∷ map⁺ f g rs

  map⁻ : ∀ {as bs} (f : A → C) (g : B → D) →
         Prefix R (List.map f as) (List.map g bs) →
         Prefix (λ a b → R (f a) (g b)) as bs
  map⁻ {[]}     {bs}     f g rs       = []
  map⁻ {a ∷ as} {[]}     f g ()
  map⁻ {a ∷ as} {b ∷ bs} f g (r ∷ rs) = r ∷ map⁻ f g rs

------------------------------------------------------------------------
-- filter

module _ {a b r p q} {A : Set a} {B : Set b} {R : REL A B r}
         {P : Pred A p} {Q : Pred B q} (P? : U.Decidable P) (Q? : U.Decidable Q)
         (P⇒Q : ∀ {a b} → R a b → P a → Q b) (Q⇒P : ∀ {a b} → R a b → Q b → P a)
         where

  filter⁺ : ∀ {as bs} → Prefix R as bs → Prefix R (filter P? as) (filter Q? bs)
  filter⁺ [] = []
  filter⁺ {a ∷ as} {b ∷ bs} (r ∷ rs) with P? a | Q? b
  ... | yes pa | yes qb = r ∷ filter⁺ rs
  ... | yes pa | no ¬qb = ⊥-elim (¬qb (P⇒Q r pa))
  ... | no ¬pa | yes qb = ⊥-elim (¬pa (Q⇒P r qb))
  ... | no ¬pa | no ¬qb = filter⁺ rs

------------------------------------------------------------------------
-- take

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  take⁺ : ∀ {as bs} n → Prefix R as bs → Prefix R (take n as) (take n bs)
  take⁺ zero    rs       = []
  take⁺ (suc n) []       = []
  take⁺ (suc n) (r ∷ rs) = r ∷ take⁺ n rs

  take⁻ : ∀ {as bs} n →
    Prefix R (take n as) (take n bs) → Prefix R (drop n as) (drop n bs) →
    Prefix R as bs
  take⁻                   zero    hds       tls = tls
  take⁻ {[]}              (suc n) hds       tls = []
  take⁻ {a ∷ as} {[]}     (suc n) ()        tls
  take⁻ {a ∷ as} {b ∷ bs} (suc n) (r ∷ hds) tls = r ∷ take⁻ n hds tls

------------------------------------------------------------------------
-- drop

  drop⁺ : ∀ {as bs} n → Prefix R as bs → Prefix R (drop n as) (drop n bs)
  drop⁺ zero    rs       = rs
  drop⁺ (suc n) []       = []
  drop⁺ (suc n) (r ∷ rs) = drop⁺ n rs

  drop⁻ : ∀ {as bs} n → Pointwise R (take n as) (take n bs) →
          Prefix R (drop n as) (drop n bs) → Prefix R as bs
  drop⁻                 zero    hds       tls = tls
  drop⁻ {[]}            (suc n) hds       tls = []
  drop⁻ {_ ∷ _} {[]}    (suc n) ()        tls
  drop⁻ {_ ∷ _} {_ ∷ _} (suc n) (r ∷ hds) tls = r ∷ (drop⁻ n hds tls)

------------------------------------------------------------------------
-- replicate

  replicate⁺ : ∀ {m n a b} → m ≤ n → R a b → Prefix R (replicate m a) (replicate n b)
  replicate⁺ z≤n       r = []
  replicate⁺ (s≤s m≤n) r = r ∷ replicate⁺ m≤n r

  replicate⁻ : ∀ {m n a b} → m ≢ 0 → Prefix R (replicate m a) (replicate n b) → R a b
  replicate⁻ {zero}  {n}     m≢0 r  = ⊥-elim (m≢0 P.refl)
  replicate⁻ {suc m} {zero}  m≢0 ()
  replicate⁻ {suc m} {suc n} m≢0 rs = Prefix.head rs

------------------------------------------------------------------------
-- inits

module _ {a r} {A : Set a} {R : Rel A r} where

  inits⁺ : ∀ {as} → Pointwise R as as → All (flip (Prefix R) as) (inits as)
  inits⁺ []       = [] ∷ []
  inits⁺ (r ∷ rs) = [] ∷ All.map⁺ (All.map (r ∷_) (inits⁺ rs))

  inits⁻ : ∀ {as} → All (flip (Prefix R) as) (inits as) → Pointwise R as as
  inits⁻ {as = []}     rs       = []
  inits⁻ {as = a ∷ as} (r ∷ rs) =
    let (hd , tls) = All.unzip (All.map uncons (All.map⁻ rs)) in
    All.lookup hd ([]∈inits as) ∷ inits⁻ tls

------------------------------------------------------------------------
-- zip(With)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c}
         {d e f} {D : Set d} {E : Set e} {F : Set f}
         {r s t} {R : REL A D r} {S : REL B E s} {T : REL C F t} where

  zipWith⁺ : ∀ {as bs ds es} {f : A → B → C} {g : D → E → F} →
    (∀ {a b c d} → R a c → S b d → T (f a b) (g c d)) →
    Prefix R as ds → Prefix S bs es →
    Prefix T (zipWith f as bs) (zipWith g ds es)
  zipWith⁺ f []       ss       = []
  zipWith⁺ f (r ∷ rs) []       = []
  zipWith⁺ f (r ∷ rs) (s ∷ ss) = f r s ∷ zipWith⁺ f rs ss

module _ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {r s} {R : REL A C r} {S : REL B D s} where

  private
    R×S : REL (A × B) (C × D) _
    R×S (a , b) (c , d) = R a c × S b d

  zip⁺ : ∀ {as bs cs ds} → Prefix R as cs → Prefix S bs ds →
         Prefix R×S (zip as bs) (zip cs ds)
  zip⁺ = zipWith⁺ _,_

------------------------------------------------------------------------
-- Irrelevant

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  irrelevant : Irrelevant R → Irrelevant (Prefix R)
  irrelevant R-irr []       []         = P.refl
  irrelevant R-irr (r ∷ rs) (r′ ∷ rs′) =
    P.cong₂ _∷_ (R-irr r r′) (irrelevant R-irr rs rs′)

------------------------------------------------------------------------
-- Decidability

  prefix? : Decidable R → Decidable (Prefix R)
  prefix? R? []       bs       = yes []
  prefix? R? (a ∷ as) []       = no (λ ())
  prefix? R? (a ∷ as) (b ∷ bs) = Dec.map′ (uncurry _∷_) uncons
                               $ R? a b ×-dec prefix? R? as bs
