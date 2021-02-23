------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types --guardedness #-}

-- Disabled to prevent warnings from BoundedVec
{-# OPTIONS --warn=noUserWarning #-}

module Codata.Musical.Colist where

open import Category.Monad
open import Codata.Musical.Notation
open import Codata.Musical.Conat using (Coℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; nothing; just; Is-just)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Data.Nat.Base using (ℕ; zero; suc; _≥′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (s≤′s)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec.Bounded as Vec≤ using (Vec≤)
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; _↔̇_; Inverse; inverse)
open import Level using (_⊔_)
open import Relation.Binary
import Relation.Binary.Construct.FromRel as Ind
import Relation.Binary.Reasoning.Preorder as PreR
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Nullary
open import Relation.Nullary.Negation

module ¬¬Monad {p} where
  open RawMonad (¬¬-Monad {p}) public
open ¬¬Monad  -- we don't want the RawMonad content to be opened publicly

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Colist {a} (A : Set a) : Set a where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

{-# FOREIGN GHC
  data AgdaColist a    = Nil | Cons a (MAlonzo.RTE.Inf (AgdaColist a))
  type AgdaColist' l a = AgdaColist a
  #-}
{-# COMPILE GHC Colist = data AgdaColist' (Nil | Cons) #-}
{-# COMPILE UHC Colist = data __LIST__ (__NIL__ | __CONS__) #-}

module Colist-injective {a} {A : Set a} where

 ∷-injectiveˡ : ∀ {x y : A} {xs ys} → (Colist A ∋ x ∷ xs) ≡ y ∷ ys → x ≡ y
 ∷-injectiveˡ P.refl = P.refl

 ∷-injectiveʳ : ∀ {x y : A} {xs ys} → (Colist A ∋ x ∷ xs) ≡ y ∷ ys → xs ≡ ys
 ∷-injectiveʳ P.refl = P.refl

data Any {a p} {A : Set a} (P : A → Set p) :
         Colist A → Set (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)          → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P (♭ xs)) → Any P (x ∷ xs)

module _  {a p} {A : Set a} {P : A → Set p} where

 here-injective : ∀ {x xs p q} → (Any P (x ∷ xs) ∋ here p) ≡ here q → p ≡ q
 here-injective P.refl = P.refl

 there-injective : ∀ {x xs p q} → (Any P (x ∷ xs) ∋ there p) ≡ there q → p ≡ q
 there-injective P.refl = P.refl

data All {a p} {A : Set a} (P : A → Set p) :
         Colist A → Set (a ⊔ p) where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : ∞ (All P (♭ xs))) → All P (x ∷ xs)

module All-injective {a p} {A : Set a} {P : A → Set p} where

 ∷-injectiveˡ : ∀ {x xs} {px qx pxs qxs} →
                (All P (x ∷ xs) ∋ px ∷ pxs) ≡ qx ∷ qxs → px ≡ qx
 ∷-injectiveˡ P.refl = P.refl

 ∷-injectiveʳ : ∀ {x xs} {px qx pxs qxs} →
                (All P (x ∷ xs) ∋ px ∷ pxs) ≡ qx ∷ qxs → pxs ≡ qxs
 ∷-injectiveʳ P.refl = P.refl

------------------------------------------------------------------------
-- Some operations

null : ∀ {a} {A : Set a} → Colist A → Bool
null []      = true
null (_ ∷ _) = false

length : ∀ {a} {A : Set a} → Colist A → Coℕ
length []       = zero
length (x ∷ xs) = suc (♯ length (♭ xs))

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Colist A → Colist B
map f []       = []
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

fromList : ∀ {a} {A : Set a} → List A → Colist A
fromList []       = []
fromList (x ∷ xs) = x ∷ ♯ fromList xs

take : ∀ {a} {A : Set a} (n : ℕ) → Colist A → Vec≤ A n
take zero    xs       = Vec≤.[]
take (suc n) []       = Vec≤.[]
take (suc n) (x ∷ xs) = x Vec≤.∷ take n (♭ xs)

replicate : ∀ {a} {A : Set a} → Coℕ → A → Colist A
replicate zero    x = []
replicate (suc n) x = x ∷ ♯ replicate (♭ n) x

lookup : ∀ {a} {A : Set a} → ℕ → Colist A → Maybe A
lookup n       []       = nothing
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {a} {A : Set a} → Colist A → Colist A → Colist A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

-- Interleaves the two colists (until the shorter one, if any, has
-- been exhausted).

infixr 5 _⋎_

_⋎_ : ∀ {a} {A : Set a} → Colist A → Colist A → Colist A
[]       ⋎ ys = ys
(x ∷ xs) ⋎ ys = x ∷ ♯ (ys ⋎ ♭ xs)

concat : ∀ {a} {A : Set a} → Colist (List⁺ A) → Colist A
concat []                     = []
concat ((x ∷ [])       ∷ xss) = x ∷ ♯ concat (♭ xss)
concat ((x ∷ (y ∷ xs)) ∷ xss) = x ∷ ♯ concat ((y ∷ xs) ∷ xss)

[_] : ∀ {a} {A : Set a} → A → Colist A
[ x ] = x ∷ ♯ []

------------------------------------------------------------------------
-- Any lemmas

-- Any lemma for map.

Any-map : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
          {f : A → B} {xs} →
          Any P (map f xs) ↔ Any (P ∘ f) xs
Any-map {P = P} {f} {xs} = inverse to from from∘to to∘from
  where
  to : ∀ {xs} → Any P (map f xs) → Any (P ∘ f) xs
  to {x ∷ xs} (here px) = here px
  to {x ∷ xs} (there p) = there (to p)

  from : ∀ {xs} → Any (P ∘ f) xs → Any P (map f xs)
  from (here px) = here px
  from (there p) = there (from p)

  from∘to : ∀ {xs} (p : Any P (map f xs)) → from (to p) ≡ p
  from∘to {x ∷ xs} (here px) = P.refl
  from∘to {x ∷ xs} (there p) = P.cong there (from∘to p)

  to∘from : ∀ {xs} (p : Any (P ∘ f) xs) → to (from p) ≡ p
  to∘from (here px) = P.refl
  to∘from (there p) = P.cong there (to∘from p)

-- Any lemma for _⋎_. This lemma implies that every member of xs or ys
-- is a member of xs ⋎ ys, and vice versa.

Any-⋎ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} →
        Any P (xs ⋎ ys) ↔ (Any P xs ⊎ Any P ys)
Any-⋎ {P = P} = λ xs → record
  { to         = P.→-to-⟶ (to xs)
  ; from       = P.→-to-⟶ (from xs)
  ; inverse-of = record
    { left-inverse-of  = from∘to xs
    ; right-inverse-of = to∘from xs
    }
  }
  where
  to : ∀ xs {ys} → Any P (xs ⋎ ys) → Any P xs ⊎ Any P ys
  to []       p         = inj₂ p
  to (x ∷ xs) (here px) = inj₁ (here px)
  to (x ∷ xs) (there p) = [ inj₂ , inj₁ ∘ there ]′ (to _ p)

  mutual

    from-left : ∀ {xs ys} → Any P xs → Any P (xs ⋎ ys)
    from-left           (here px) = here px
    from-left {ys = ys} (there p) = there (from-right ys p)

    from-right : ∀ xs {ys} → Any P ys → Any P (xs ⋎ ys)
    from-right []       p = p
    from-right (x ∷ xs) p = there (from-left p)

  from : ∀ xs {ys} → Any P xs ⊎ Any P ys → Any P (xs ⋎ ys)
  from xs = Sum.[ from-left , from-right xs ]

  from∘to : ∀ xs {ys} (p : Any P (xs ⋎ ys)) → from xs (to xs p) ≡ p
  from∘to []                 p                          = P.refl
  from∘to (x ∷ xs)           (here px)                  = P.refl
  from∘to (x ∷ xs) {ys = ys} (there p)                  with to ys p | from∘to ys p
  from∘to (x ∷ xs) {ys = ys} (there .(from-left q))     | inj₁ q | P.refl = P.refl
  from∘to (x ∷ xs) {ys = ys} (there .(from-right ys q)) | inj₂ q | P.refl = P.refl

  mutual

    to∘from-left : ∀ {xs ys} (p : Any P xs) →
                   to xs {ys = ys} (from-left p) ≡ inj₁ p
    to∘from-left           (here px) = P.refl
    to∘from-left {ys = ys} (there p)
      rewrite to∘from-right ys p = P.refl

    to∘from-right : ∀ xs {ys} (p : Any P ys) →
                    to xs (from-right xs p) ≡ inj₂ p
    to∘from-right []                 p = P.refl
    to∘from-right (x ∷ xs) {ys = ys} p
      rewrite to∘from-left {xs = ys} {ys = ♭ xs} p = P.refl

  to∘from : ∀ xs {ys} (p : Any P xs ⊎ Any P ys) → to xs (from xs p) ≡ p
  to∘from xs = Sum.[ to∘from-left , to∘from-right xs ]

------------------------------------------------------------------------
-- Equality

-- xs ≈ ys means that xs and ys are equal.

infix 4 _≈_

data _≈_ {a} {A : Set a} : (xs ys : Colist A) → Set a where
  []  :                                       []     ≈ []
  _∷_ : ∀ x {xs ys} (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ x ∷ ys

-- The equality relation forms a setoid.

setoid : ∀ {ℓ} → Set ℓ → Setoid _ _
setoid A = record
  { Carrier       = Colist A
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {[]}     = []
  refl {x ∷ xs} = x ∷ ♯ refl

  sym : Symmetric _≈_
  sym []        = []
  sym (x ∷ xs≈) = x ∷ ♯ sym (♭ xs≈)

  trans : Transitive _≈_
  trans []        []         = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

module ≈-Reasoning where
  import Relation.Binary.Reasoning.Setoid as EqR
  private
    open module R {a} {A : Set a} = EqR (setoid A) public

-- map preserves equality.

map-cong : ∀ {a b} {A : Set a} {B : Set b}
           (f : A → B) → _≈_ =[ map f ]⇒ _≈_
map-cong f []        = []
map-cong f (x ∷ xs≈) = f x ∷ ♯ map-cong f (♭ xs≈)

-- Any respects pointwise implication (for the predicate) and equality
-- (for the colist).

Any-resp : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
           {xs ys} → (∀ {x} → P x → Q x) → xs ≈ ys →
           Any P xs → Any Q ys
Any-resp f (x ∷ xs≈) (here px) = here (f px)
Any-resp f (x ∷ xs≈) (there p) = there (Any-resp f (♭ xs≈) p)

-- Any maps pointwise isomorphic predicates and equal colists to
-- isomorphic types.

Any-cong : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
           {xs ys} → P ↔̇ Q → xs ≈ ys → Any P xs ↔ Any Q ys
Any-cong {A = A} {P} {Q} {xs} {ys} P↔Q = λ xs≈ys → record
  { to         = P.→-to-⟶ (to xs≈ys)
  ; from       = P.→-to-⟶ (from xs≈ys)
  ; inverse-of = record
    { left-inverse-of  = from∘to _
    ; right-inverse-of = to∘from _
    }
  }
  where
  open Setoid (setoid _) using (sym)

  to : ∀ {xs ys} → xs ≈ ys → Any P xs → Any Q ys
  to xs≈ys = Any-resp (Inverse.to P↔Q ⟨$⟩_) xs≈ys

  from : ∀ {xs ys} → xs ≈ ys → Any Q ys → Any P xs
  from xs≈ys = Any-resp (Inverse.from P↔Q ⟨$⟩_) (sym xs≈ys)

  to∘from : ∀ {xs ys} (xs≈ys : xs ≈ ys) (q : Any Q ys) →
            to xs≈ys (from xs≈ys q) ≡ q
  to∘from (x ∷ xs≈) (there q) = P.cong there (to∘from (♭ xs≈) q)
  to∘from (x ∷ xs≈) (here qx) =
    P.cong here (Inverse.right-inverse-of P↔Q qx)

  from∘to : ∀ {xs ys} (xs≈ys : xs ≈ ys) (p : Any P xs) →
            from xs≈ys (to xs≈ys p) ≡ p
  from∘to (x ∷ xs≈) (there p) = P.cong there (from∘to (♭ xs≈) p)
  from∘to (x ∷ xs≈) (here px) =
    P.cong here (Inverse.left-inverse-of P↔Q px)

------------------------------------------------------------------------
-- Indices

-- Converts Any proofs to indices into the colist. The index can also
-- be seen as the size of the proof.

index : ∀ {a p} {A : Set a} {P : A → Set p} {xs} → Any P xs → ℕ
index (here px) = zero
index (there p) = suc (index p)

-- The position returned by index is guaranteed to be within bounds.

lookup-index : ∀ {a p} {A : Set a} {P : A → Set p} {xs} (p : Any P xs) →
               Is-just (lookup (index p) xs)
lookup-index (here px) = just _
lookup-index (there p) = lookup-index p

-- Any-resp preserves the index.

index-Any-resp :
  ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
    {f : ∀ {x} → P x → Q x} {xs ys}
  (xs≈ys : xs ≈ ys) (p : Any P xs) →
  index (Any-resp f xs≈ys p) ≡ index p
index-Any-resp (x ∷ xs≈) (here px) = P.refl
index-Any-resp (x ∷ xs≈) (there p) =
  P.cong suc (index-Any-resp (♭ xs≈) p)

-- The left-to-right direction of Any-⋎ returns a proof whose size is
-- no larger than that of the input proof.

index-Any-⋎ :
  ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} (p : Any P (xs ⋎ ys)) →
  index p ≥′ [ index , index ]′ (Inverse.to (Any-⋎ xs) ⟨$⟩ p)
index-Any-⋎ []                 p         = ≤′-refl
index-Any-⋎ (x ∷ xs)           (here px) = ≤′-refl
index-Any-⋎ (x ∷ xs) {ys = ys} (there p)
  with Inverse.to (Any-⋎ ys) ⟨$⟩ p | index-Any-⋎ ys p
... | inj₁ q | q≤p = ≤′-step q≤p
... | inj₂ q | q≤p = s≤′s    q≤p

------------------------------------------------------------------------
-- Memberships, subsets, prefixes

-- x ∈ xs means that x is a member of xs.

infix 4 _∈_

_∈_ : ∀ {a} → {A : Set a} → A → Colist A → Set a
x ∈ xs = Any (_≡_ x) xs

-- xs ⊆ ys means that xs is a subset of ys.

infix 4 _⊆_

_⊆_ : ∀ {a} → {A : Set a} → Colist A → Colist A → Set a
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

-- xs ⊑ ys means that xs is a prefix of ys.

infix 4 _⊑_

data _⊑_ {a} {A : Set a} : Colist A → Colist A → Set a where
  []  : ∀ {ys}                            → []     ⊑ ys
  _∷_ : ∀ x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) → x ∷ xs ⊑ x ∷ ys

-- Any can be expressed using _∈_ (and vice versa).

Any-∈ : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
        Any P xs ↔ ∃ λ x → x ∈ xs × P x
Any-∈ {P = P} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ (λ { (x , x∈xs , p) → from x∈xs p })
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = λ { (x , x∈xs , p) → to∘from x∈xs p }
    }
  }
  where
  to : ∀ {xs} → Any P xs → ∃ λ x → x ∈ xs × P x
  to (here  p) = _ , here P.refl , p
  to (there p) = Prod.map id (Prod.map there id) (to p)

  from : ∀ {x xs} → x ∈ xs → P x → Any P xs
  from (here P.refl) p = here p
  from (there x∈xs)  p = there (from x∈xs p)

  to∘from : ∀ {x xs} (x∈xs : x ∈ xs) (p : P x) →
            to (from x∈xs p) ≡ (x , x∈xs , p)
  to∘from (here P.refl) p = P.refl
  to∘from (there x∈xs)  p =
    P.cong (Prod.map id (Prod.map there id)) (to∘from x∈xs p)

  from∘to : ∀ {xs} (p : Any P xs) →
            let (x , x∈xs , px) = to p in from x∈xs px ≡ p
  from∘to (here _)  = P.refl
  from∘to (there p) = P.cong there (from∘to p)

-- Prefixes are subsets.

⊑⇒⊆ : ∀ {a} → {A : Set a} → _⊑_ {A = A} ⇒ _⊆_
⊑⇒⊆ (x ∷ xs⊑ys) (here ≡x)    = here ≡x
⊑⇒⊆ (_ ∷ xs⊑ys) (there x∈xs) = there (⊑⇒⊆ (♭ xs⊑ys) x∈xs)

-- The prefix relation forms a poset.

⊑-Poset : ∀ {ℓ} → Set ℓ → Poset _ _ _
⊑-Poset A = record
  { Carrier        = Colist A
  ; _≈_            = _≈_
  ; _≤_            = _⊑_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Setoid.isEquivalence (setoid A)
      ; reflexive     = reflexive
      ; trans         = trans
      }
    ; antisym  = antisym
    }
  }
  where
  reflexive : _≈_ ⇒ _⊑_
  reflexive []        = []
  reflexive (x ∷ xs≈) = x ∷ ♯ reflexive (♭ xs≈)

  trans : Transitive _⊑_
  trans []        _          = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

  tail : ∀ {x xs y ys} → x ∷ xs ⊑ y ∷ ys → ♭ xs ⊑ ♭ ys
  tail (_ ∷ p) = ♭ p

  antisym : Antisymmetric _≈_ _⊑_
  antisym []       [] = []
  antisym (x ∷ p₁) p₂ = x ∷ ♯ antisym (♭ p₁) (tail p₂)

module ⊑-Reasoning {a} {A : Set a} where
  private module Base = POR (⊑-Poset A)

  open Base public
    hiding (step-<; begin-strict_; step-≤)

  infixr 2 step-⊑
  step-⊑ = Base.step-≤
  syntax step-⊑ x ys⊑zs xs⊑ys = x ⊑⟨ xs⊑ys ⟩ ys⊑zs

-- The subset relation forms a preorder.

⊆-Preorder : ∀ {ℓ} → Set ℓ → Preorder _ _ _
⊆-Preorder A = Ind.preorder (setoid A) _∈_
                 (λ xs≈ys → ⊑⇒⊆ (⊑P.reflexive xs≈ys))
  where module ⊑P = Poset (⊑-Poset A)

module ⊆-Reasoning {a} {A : Set a} where
  private module Base = PreR (⊆-Preorder A)

  open Base public
    hiding (step-∼)

  infixr 2 step-⊆
  infix  1 step-∈

  step-⊆ = Base.step-∼

  step-∈ : ∀ (x : A) {xs ys} → xs IsRelatedTo ys → x ∈ xs → x ∈ ys
  step-∈ x xs⊆ys x∈xs = (begin xs⊆ys) x∈xs

  syntax step-⊆ xs ys⊆zs xs⊆ys = xs ⊆⟨ xs⊆ys ⟩ ys⊆zs
  syntax step-∈ x  xs⊆ys x∈xs  = x  ∈⟨ x∈xs  ⟩ xs⊆ys

-- take returns a prefix.
take-⊑ : ∀ {a} {A : Set a} n (xs : Colist A) →
         let toColist = fromList {a} ∘ Vec≤.toList in
         toColist (take n xs) ⊑ xs
take-⊑ zero    xs       = []
take-⊑ (suc n) []       = []
take-⊑ (suc n) (x ∷ xs) = x ∷ ♯ take-⊑ n (♭ xs)

------------------------------------------------------------------------
-- Finiteness and infiniteness

-- Finite xs means that xs has finite length.

data Finite {a} {A : Set a} : Colist A → Set a where
  []  : Finite []
  _∷_ : ∀ x {xs} (fin : Finite (♭ xs)) → Finite (x ∷ xs)

module Finite-injective {a} {A : Set a} where

 ∷-injective : ∀ {x : A} {xs p q} → (Finite (x ∷ xs) ∋ x ∷ p) ≡ x ∷ q → p ≡ q
 ∷-injective P.refl = P.refl

-- Infinite xs means that xs has infinite length.

data Infinite {a} {A : Set a} : Colist A → Set a where
  _∷_ : ∀ x {xs} (inf : ∞ (Infinite (♭ xs))) → Infinite (x ∷ xs)

module Infinite-injective {a} {A : Set a} where

 ∷-injective : ∀ {x : A} {xs p q} → (Infinite (x ∷ xs) ∋ x ∷ p) ≡ x ∷ q → p ≡ q
 ∷-injective P.refl = P.refl

-- Colists which are not finite are infinite.

not-finite-is-infinite :
  ∀ {a} {A : Set a} (xs : Colist A) → ¬ Finite xs → Infinite xs
not-finite-is-infinite []       hyp = contradiction [] hyp
not-finite-is-infinite (x ∷ xs) hyp =
  x ∷ ♯ not-finite-is-infinite (♭ xs) (hyp ∘ _∷_ x)

-- Colists are either finite or infinite (classically).

finite-or-infinite :
  ∀ {a} {A : Set a} (xs : Colist A) → ¬ ¬ (Finite xs ⊎ Infinite xs)
finite-or-infinite xs = helper <$> excluded-middle
  where
  helper : Dec (Finite xs) → Finite xs ⊎ Infinite xs
  helper ( true because  [fin]) = inj₁ (invert [fin])
  helper (false because [¬fin]) =
    inj₂ $ not-finite-is-infinite xs (invert [¬fin])

-- Colists are not both finite and infinite.

not-finite-and-infinite :
  ∀ {a} {A : Set a} {xs : Colist A} → Finite xs → Infinite xs → ⊥
not-finite-and-infinite (x ∷ fin) (.x ∷ inf) =
  not-finite-and-infinite fin (♭ inf)

------------------------------------------------------------------------
-- Legacy

import Codata.Colist as C
open import Codata.Thunk
import Size

module _ {a} {A : Set a} where

  fromMusical : ∀ {i} → Colist A → C.Colist A i
  fromMusical []       = C.[]
  fromMusical (x ∷ xs) = x C.∷ λ where .force → fromMusical (♭ xs)

  toMusical : C.Colist A Size.∞ → Colist A
  toMusical C.[]       = []
  toMusical (x C.∷ xs) = x ∷ ♯ toMusical (xs .force)



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.3

open import Data.BoundedVec.Inefficient as BVec
  using (BoundedVec; []; _∷_)

take′ : ∀ {a} {A : Set a} (n : ℕ) → Colist A → BoundedVec A n
take′ zero    xs       = []
take′ (suc n) []       = []
take′ (suc n) (x ∷ xs) = x ∷ take′ n (♭ xs)
{-# WARNING_ON_USAGE take′
"Warning: take′ (and Data.BoundedVec) was deprecated in v1.3.
Please use take (and Data.Vec.Bounded) instead."
#-}

take′-⊑ : ∀ {a} {A : Set a} n (xs : Colist A) →
         let toColist = fromList {a} ∘ BVec.toList in
         toColist (take′ n xs) ⊑ xs
take′-⊑ zero    xs       = []
take′-⊑ (suc n) []       = []
take′-⊑ (suc n) (x ∷ xs) = x ∷ ♯ take′-⊑ n (♭ xs)
{-# WARNING_ON_USAGE take′-⊑
"Warning: take′-⊑ (and Data.BoundedVec) was deprecated in v1.3.
Please use take-⊑ (and Data.Vec.Bounded) instead."
#-}
