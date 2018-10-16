------------------------------------------------------------------------
-- The Agda standard library
--
-- Bag and set equality
------------------------------------------------------------------------

module Data.List.Relation.BagAndSetEquality where

open import Algebra using (CommutativeSemiring; CommutativeMonoid)
open import Algebra.FunctionProperties using (Idempotent)
open import Category.Monad using (RawMonad)
open import Data.List
open import Data.List.Categorical using (monad; module MonadProperties)
import Data.List.Properties as LP
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Properties
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Subset.Propositional.Properties
  using (⊆-preorder)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Sum.Relation.Pointwise using (_⊎-cong_)
open import Function
open import Function.Equality using (_⟨$⟩_)
import Function.Equivalence as FE
open import Function.Inverse as Inv using (_↔_; Inverse; inverse)
open import Function.Related as Related using (↔⇒; ⌊_⌋; ⌊_⌋→; ⇒→; SK-sym)
open import Function.Related.TypeIsomorphisms
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_; refl)
open import Relation.Nullary
open import Data.List.Membership.Propositional.Properties

------------------------------------------------------------------------
-- Definitions

open Related public using (Kind; Symmetric-kind) renaming
  ( implication         to subset
  ; reverse-implication to superset
  ; equivalence         to set
  ; injection           to subbag
  ; reverse-injection   to superbag
  ; bijection           to bag
  )

[_]-Order : Kind → ∀ {a} → Set a → Preorder _ _ _
[ k ]-Order A = Related.InducedPreorder₂ k {A = A} _∈_

[_]-Equality : Symmetric-kind → ∀ {a} → Set a → Setoid _ _
[ k ]-Equality A = Related.InducedEquivalence₂ k {A = A} _∈_

infix 4 _∼[_]_

_∼[_]_ : ∀ {a} {A : Set a} → List A → Kind → List A → Set _
_∼[_]_ {A = A} xs k ys = Preorder._∼_ ([ k ]-Order A) xs ys

private
  module Eq  {k a} {A : Set a} = Setoid ([ k ]-Equality A)
  module Ord {k a} {A : Set a} = Preorder ([ k ]-Order A)
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})
  module MP = MonadProperties

------------------------------------------------------------------------
-- Bag equality implies the other relations.

bag-=⇒ : ∀ {k a} {A : Set a} {xs ys : List A} →
         xs ∼[ bag ] ys → xs ∼[ k ] ys
bag-=⇒ xs≈ys = ↔⇒ xs≈ys

------------------------------------------------------------------------
-- "Equational" reasoning for _⊆_ along with an additional relatedness

module ⊆-Reasoning where
  import Relation.Binary.PreorderReasoning as PreR
  private
    open module PR {a} {A : Set a} = PreR (⊆-preorder A) public
      hiding (_≈⟨_⟩_) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

  infixr 2 _∼⟨_⟩_
  infix  1 _∈⟨_⟩_

  _∈⟨_⟩_ : ∀ {a} {A : Set a} x {xs ys : List A} →
           x ∈ xs → xs IsRelatedTo ys → x ∈ ys
  x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

  _∼⟨_⟩_ : ∀ {k a} {A : Set a} xs {ys zs : List A} →
           xs ∼[ ⌊ k ⌋→ ] ys → ys IsRelatedTo zs → xs IsRelatedTo zs
  xs ∼⟨ xs≈ys ⟩ ys≈zs = xs ⊆⟨ ⇒→ xs≈ys ⟩ ys≈zs

------------------------------------------------------------------------
-- Congruence lemmas
------------------------------------------------------------------------
-- _∷_

module _ {a k} {A : Set a} {x y : A} {xs ys} where

  ∷-cong : x ≡ y → xs ∼[ k ] ys → x ∷ xs ∼[ k ] y ∷ ys
  ∷-cong refl xs≈ys {y} =
    y ∈ x ∷ xs        ↔⟨ SK-sym $ ∷↔ (y ≡_) ⟩
    (y ≡ x ⊎ y ∈ xs)  ∼⟨ (y ≡ x ∎) ⊎-cong xs≈ys ⟩
    (y ≡ x ⊎ y ∈ ys)  ↔⟨ ∷↔ (y ≡_) ⟩
    y ∈ x ∷ ys        ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- map

module _ {ℓ k} {A B : Set ℓ} {f g : A → B} {xs ys} where

  map-cong : f ≗ g → xs ∼[ k ] ys → map f xs ∼[ k ] map g ys
  map-cong f≗g xs≈ys {x} =
    x ∈ map f xs            ↔⟨ SK-sym $ map↔ ⟩
    Any (λ y → x ≡ f y) xs  ∼⟨ Any-cong (↔⇒ ∘ helper) xs≈ys ⟩
    Any (λ y → x ≡ g y) ys  ↔⟨ map↔ ⟩
    x ∈ map g ys            ∎
    where
    open Related.EquationalReasoning

    helper : ∀ y → x ≡ f y ↔ x ≡ g y
    helper y = record
      { to         = P.→-to-⟶ (λ x≡fy → P.trans x≡fy (        f≗g y))
      ; from       = P.→-to-⟶ (λ x≡gy → P.trans x≡gy (P.sym $ f≗g y))
      ; inverse-of = record
        { left-inverse-of  = λ _ → P.≡-irrelevance _ _
        ; right-inverse-of = λ _ → P.≡-irrelevance _ _
        }
      }

------------------------------------------------------------------------
-- _++_

module _ {a k} {A : Set a} {xs₁ xs₂ ys₁ ys₂ : List A} where

  ++-cong : xs₁ ∼[ k ] xs₂ → ys₁ ∼[ k ] ys₂ →
            xs₁ ++ ys₁ ∼[ k ] xs₂ ++ ys₂
  ++-cong xs₁≈xs₂ ys₁≈ys₂ {x} =
    x ∈ xs₁ ++ ys₁       ↔⟨ SK-sym $ ++↔ ⟩
    (x ∈ xs₁ ⊎ x ∈ ys₁)  ∼⟨ xs₁≈xs₂ ⊎-cong ys₁≈ys₂ ⟩
    (x ∈ xs₂ ⊎ x ∈ ys₂)  ↔⟨ ++↔ ⟩
    x ∈ xs₂ ++ ys₂       ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- concat

module _ {a k} {A : Set a} {xss yss : List (List A)} where

  concat-cong : xss ∼[ k ] yss → concat xss ∼[ k ] concat yss
  concat-cong xss≈yss {x} =
    x ∈ concat xss        ↔⟨ SK-sym concat↔ ⟩
    Any (Any (x ≡_)) xss  ∼⟨ Any-cong (λ _ → _ ∎) xss≈yss ⟩
    Any (Any (x ≡_)) yss  ↔⟨ concat↔ ⟩
    x ∈ concat yss         ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _>>=_

module _ {ℓ k} {A B : Set ℓ} {xs ys} {f g : A → List B} where

  >>=-cong : xs ∼[ k ] ys → (∀ x → f x ∼[ k ] g x) →
             (xs >>= f) ∼[ k ] (ys >>= g)
  >>=-cong xs≈ys f≈g {x} =
    x ∈ (xs >>= f)          ↔⟨ SK-sym >>=↔ ⟩
    Any (λ y → x ∈ f y) xs  ∼⟨ Any-cong (λ x → f≈g x) xs≈ys ⟩
    Any (λ y → x ∈ g y) ys  ↔⟨ >>=↔ ⟩
    x ∈ (ys >>= g)          ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _⊛_

module _ {ℓ k} {A B : Set ℓ} {fs gs : List (A → B)} {xs ys} where

  ⊛-cong : fs ∼[ k ] gs → xs ∼[ k ] ys → (fs ⊛ xs) ∼[ k ] (gs ⊛ ys)
  ⊛-cong fs≈gs xs≈ys =
    >>=-cong fs≈gs λ f →
    >>=-cong xs≈ys λ x →
    _ ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _⊗_

module _ {ℓ k} {A B : Set ℓ} {xs₁ xs₂ : List A} {ys₁ ys₂ : List B} where

  ⊗-cong : xs₁ ∼[ k ] xs₂ → ys₁ ∼[ k ] ys₂ →
           (xs₁ ⊗ ys₁) ∼[ k ] (xs₂ ⊗ ys₂)
  ⊗-cong xs₁≈xs₂ ys₁≈ys₂ =
    ⊛-cong (⊛-cong (Ord.refl {x = [ _,_ ]}) xs₁≈xs₂) ys₁≈ys₂

------------------------------------------------------------------------
-- Other properties

-- _++_ and [] form a commutative monoid, with either bag or set
-- equality as the underlying equality.

commutativeMonoid : ∀ {a} → Symmetric-kind → Set a →
                    CommutativeMonoid _ _
commutativeMonoid {a} k A = record
  { Carrier             = List A
  ; _≈_                 = _∼[ ⌊ k ⌋ ]_
  ; _∙_                 = _++_
  ; ε                   = []
  ; isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = Eq.isEquivalence
      ; assoc         = λ xs ys zs →
                          Eq.reflexive (LP.++-assoc xs ys zs)
      ; ∙-cong        = ++-cong
      }
    ; identityˡ = λ xs {x} → x ∈ xs ∎
    ; comm      = λ xs ys {x} →
                    x ∈ xs ++ ys  ↔⟨ ++↔++ xs ys ⟩
                    x ∈ ys ++ xs  ∎
    }
  }
  where open Related.EquationalReasoning

-- The only list which is bag or set equal to the empty list (or a
-- subset or subbag of the list) is the empty list itself.

empty-unique : ∀ {k a} {A : Set a} {xs : List A} →
               xs ∼[ ⌊ k ⌋→ ] [] → xs ≡ []
empty-unique {xs = []}    _    = refl
empty-unique {xs = _ ∷ _} ∷∼[] with ⇒→ ∷∼[] (here refl)
... | ()

-- _++_ is idempotent (under set equality).

++-idempotent : ∀ {a} {A : Set a} → Idempotent {A = List A} _∼[ set ]_ _++_
++-idempotent {a} xs {x} =
  x ∈ xs ++ xs  ∼⟨ FE.equivalence ([ id , id ]′ ∘ _⟨$⟩_ (Inverse.from $ ++↔))
                                  (_⟨$⟩_ (Inverse.to $ ++↔) ∘ inj₁) ⟩
  x ∈ xs        ∎
  where open Related.EquationalReasoning

-- The list monad's bind distributes from the left over _++_.

>>=-left-distributive :
  ∀ {ℓ} {A B : Set ℓ} (xs : List A) {f g : A → List B} →
  (xs >>= λ x → f x ++ g x) ∼[ bag ] (xs >>= f) ++ (xs >>= g)
>>=-left-distributive {ℓ} xs {f} {g} {y} =
  y ∈ (xs >>= λ x → f x ++ g x)                      ↔⟨ SK-sym $ >>=↔ ⟩
  Any (λ x → y ∈ f x ++ g x) xs                      ↔⟨ SK-sym (Any-cong (λ _ → ++↔) (_ ∎)) ⟩
  Any (λ x → y ∈ f x ⊎ y ∈ g x) xs                   ↔⟨ SK-sym $ ⊎↔ ⟩
  (Any (λ x → y ∈ f x) xs ⊎ Any (λ x → y ∈ g x) xs)  ↔⟨ >>=↔ ⟨ _⊎-cong_ ⟩ >>=↔ ⟩
  (y ∈ (xs >>= f) ⊎ y ∈ (xs >>= g))                  ↔⟨ ++↔ ⟩
  y ∈ (xs >>= f) ++ (xs >>= g)                       ∎
  where open Related.EquationalReasoning

-- The same applies to _⊛_.

⊛-left-distributive :
  ∀ {ℓ} {A B : Set ℓ} (fs : List (A → B)) xs₁ xs₂ →
  (fs ⊛ (xs₁ ++ xs₂)) ∼[ bag ] (fs ⊛ xs₁) ++ (fs ⊛ xs₂)
⊛-left-distributive {B = B} fs xs₁ xs₂ = begin
  fs ⊛ (xs₁ ++ xs₂)                         ≡⟨⟩
  (fs >>= λ f → xs₁ ++ xs₂ >>= return ∘ f)  ≡⟨ (MP.cong (refl {x = fs}) λ f →
                                                MP.right-distributive xs₁ xs₂ (return ∘ f)) ⟩
  (fs >>= λ f → (xs₁ >>= return ∘ f) ++
                (xs₂ >>= return ∘ f))       ≈⟨ >>=-left-distributive fs ⟩

  (fs >>= λ f → xs₁ >>= return ∘ f) ++
  (fs >>= λ f → xs₂ >>= return ∘ f)         ≡⟨⟩

  (fs ⊛ xs₁) ++ (fs ⊛ xs₂)                  ∎
  where open EqR ([ bag ]-Equality B)

private

  -- If x ∷ xs is set equal to x ∷ ys, then xs and ys are not
  -- necessarily set equal.

  ¬-drop-cons : ∀ {a} {A : Set a} {x : A} →
    ¬ (∀ {xs ys} → x ∷ xs ∼[ set ] x ∷ ys → xs ∼[ set ] ys)
  ¬-drop-cons {x = x} drop-cons
    with FE.Equivalence.to x∼[] ⟨$⟩ here refl
    where
    x,x≈x :  (x ∷ x ∷ []) ∼[ set ] [ x ]
    x,x≈x = ++-idempotent [ x ]

    x∼[] : [ x ] ∼[ set ] []
    x∼[] = drop-cons x,x≈x
  ... | ()

-- However, the corresponding property does hold for bag equality.

drop-cons : ∀ {a} {A : Set a} {x : A} {xs ys} →
            x ∷ xs ∼[ bag ] x ∷ ys → xs ∼[ bag ] ys
drop-cons {x = x} eq = inverse (f eq) (f $ Inv.sym eq) (f∘f eq) (f∘f $ Inv.sym eq)
  where
  open Inverse
  open P.≡-Reasoning

  f : ∀ {xs ys z} → (z ∈ x ∷ xs) ↔ (z ∈ x ∷ ys) → z ∈ xs → z ∈ ys
  f inv z∈xs with to inv ⟨$⟩ there z∈xs | left-inverse-of inv (there z∈xs)
  ... | there z∈ys | left⁺ = z∈ys
  ... | here  refl | left⁺ with to inv ⟨$⟩ here refl | left-inverse-of inv (here refl)
  ...   | there z∈ys | left⁰ = z∈ys
  ...   | here  refl | left⁰ with begin
    here refl               ≡⟨ P.sym left⁰ ⟩
    from inv ⟨$⟩ here refl  ≡⟨ left⁺ ⟩
    there z∈xs              ∎
  ... | ()

  f∘f : ∀ {xs ys z} (inv : (z ∈ x ∷ xs) ↔ (z ∈ x ∷ ys)) (p : z ∈ xs) →
        f (Inv.sym inv) (f inv p) ≡ p
  f∘f inv z∈xs with to inv ⟨$⟩ there z∈xs | left-inverse-of inv (there z∈xs)
  f∘f inv z∈xs | there z∈ys  | left⁺ with from inv ⟨$⟩ there z∈ys | right-inverse-of inv (there z∈ys)
  f∘f inv z∈xs | there z∈ys  | refl | .(there z∈xs) | _ = refl
  f∘f inv z∈xs | here refl   | left⁺ with to inv ⟨$⟩ here refl | left-inverse-of inv (here refl)
  f∘f inv z∈xs | here refl   | left⁺  | there z∈ys  | left⁰ with from inv ⟨$⟩ there z∈ys | right-inverse-of inv (there z∈ys)
  f∘f inv z∈xs | here refl   | left⁺  | there z∈ys  | refl | .(here refl) | _ with from inv ⟨$⟩ here refl
                                                                                   | right-inverse-of inv (here refl)
  f∘f inv z∈xs | here refl   | refl   | there z∈ys  | refl | .(here refl) | _ | .(there z∈xs) | _ = refl
  f∘f inv z∈xs | here refl   | left⁺  | here  refl  | left⁰ with begin
    here refl               ≡⟨ P.sym left⁰ ⟩
    from inv ⟨$⟩ here refl  ≡⟨ left⁺ ⟩
    there z∈xs                ∎
  ... | ()
