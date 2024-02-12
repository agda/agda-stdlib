------------------------------------------------------------------------
-- The Agda standard library
--
-- Bag and set equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.BagAndSetEquality where

open import Algebra using (Idempotent; CommutativeMonoid)
open import Algebra.Structures.Biased using (isCommutativeMonoidˡ)
open import Effect.Monad using (RawMonad)
open import Data.Empty
open import Data.Fin.Base
open import Data.List.Base
open import Data.List.Effectful using (monad; module Applicative; module MonadProperties)
import Data.List.Properties as LP
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties hiding (++-comm)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties
  using (⊆-preorder)
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.Product.Base as Prod hiding (map)
import Data.Product.Function.Dependent.Propositional as Σ
open import Data.Sum.Base as Sum hiding (map)
open import Data.Sum.Properties hiding (map-cong)
open import Data.Sum.Function.Propositional using (_⊎-cong_)
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Function.Bundles using (_↔_; Inverse; Equivalence; mk↔ₛ′; mk⇔)
open import Function.Related.Propositional as Related
  using (↔⇒; ⌊_⌋; ⌊_⌋→; ⇒→; K-refl; SK-sym)
open import Function.Related.TypeIsomorphisms
open import Function.Properties.Inverse using (↔-sym; ↔-trans; to-from)
open import Level using (Level)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Definitions using (Trans)
open import Relation.Binary.Bundles using (Preorder; Setoid)
import Relation.Binary.Reasoning.Setoid as EqR
import Relation.Binary.Reasoning.Preorder as PreorderReasoning
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; _≗_; refl)
open import Relation.Binary.Reasoning.Syntax
open import Relation.Nullary.Negation using (¬_)
open import Data.List.Membership.Propositional.Properties

private
  variable
    a b : Level
    A B : Set a
    x y : A
    ws xs ys zs : List A

------------------------------------------------------------------------
-- Definitions

open Related public using (Kind; SymmetricKind) renaming
  ( implication         to subset
  ; reverseImplication  to superset
  ; equivalence         to set
  ; injection           to subbag
  ; reverseInjection    to superbag
  ; bijection           to bag
  )

[_]-Order : Kind → Set a → Preorder _ _ _
[ k ]-Order A = Related.InducedPreorder₂ {A = A} k _∈_

[_]-Equality : SymmetricKind → Set a → Setoid _ _
[ k ]-Equality A = Related.InducedEquivalence₂ {A = A} k _∈_

infix 4 _∼[_]_

_∼[_]_ : ∀ {a} {A : Set a} → List A → Kind → List A → Set _
_∼[_]_ {A = A} xs k ys = Preorder._≲_ ([ k ]-Order A) xs ys

private
  module Eq  {k a} {A : Set a} = Setoid ([ k ]-Equality A)
  module Ord {k a} {A : Set a} = Preorder ([ k ]-Order A)
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})
  module MP = MonadProperties

------------------------------------------------------------------------
-- Bag equality implies the other relations.

bag-=⇒ : ∀ {k} → xs ∼[ bag ] ys → xs ∼[ k ] ys
bag-=⇒ xs≈ys = ↔⇒ xs≈ys

------------------------------------------------------------------------
-- "Equational" reasoning for _⊆_ along with an additional relatedness

module ⊆-Reasoning {A : Set a} where
  private module Base = PreorderReasoning (⊆-preorder A)

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨; step-∼; step-≲)
    renaming (≲-go to ⊆-go)

  open begin-membership-syntax _IsRelatedTo_ _∈_ (λ x → begin x) public
  open ⊆-syntax _IsRelatedTo_ _IsRelatedTo_ ⊆-go public

  module _ {k : Related.ForwardKind} where
    ∼-go : Trans _∼[ ⌊ k ⌋→ ]_ _IsRelatedTo_ _IsRelatedTo_
    ∼-go eq = ⊆-go (⇒→ eq)

    open ∼-syntax _IsRelatedTo_ _IsRelatedTo_ ∼-go public


------------------------------------------------------------------------
-- Congruence lemmas
------------------------------------------------------------------------
-- _∷_

module _ {k} {x y : A} {xs ys} where

  ∷-cong : x ≡ y → xs ∼[ k ] ys → x ∷ xs ∼[ k ] y ∷ ys
  ∷-cong refl xs≈ys {y} = begin
    y ∈ x ∷ xs        ↔⟨ SK-sym $ ∷↔ (y ≡_) ⟩
    (y ≡ x ⊎ y ∈ xs)  ∼⟨ K-refl ⊎-cong xs≈ys ⟩
    (y ≡ x ⊎ y ∈ ys)  ↔⟨ ∷↔ (y ≡_) ⟩
    y ∈ x ∷ ys        ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- map

module _ {k} {f g : A → B} {xs ys} where

  map-cong : f ≗ g → xs ∼[ k ] ys → map f xs ∼[ k ] map g ys
  map-cong f≗g xs≈ys {x} = begin
    x ∈ map f xs            ↔⟨ SK-sym $ map↔ ⟩
    Any (λ y → x ≡ f y) xs  ∼⟨ Any-cong (↔⇒ ∘ helper) xs≈ys ⟩
    Any (λ y → x ≡ g y) ys  ↔⟨ map↔ ⟩
    x ∈ map g ys            ∎
    where
    open Related.EquationalReasoning

    helper : ∀ y → x ≡ f y ↔ x ≡ g y
    helper y = mk↔ₛ′
      (λ x≡fy → P.trans x≡fy (        f≗g y))
      (λ x≡gy → P.trans x≡gy (P.sym $ f≗g y))
      (λ { P.refl → P.trans-symˡ (f≗g y) })
      λ { P.refl → P.trans-symʳ (f≗g y) }

------------------------------------------------------------------------
-- _++_

module _ {k} {xs₁ xs₂ ys₁ ys₂ : List A} where

  ++-cong : xs₁ ∼[ k ] xs₂ → ys₁ ∼[ k ] ys₂ →
            xs₁ ++ ys₁ ∼[ k ] xs₂ ++ ys₂
  ++-cong xs₁≈xs₂ ys₁≈ys₂ {x} = begin
    x ∈ xs₁ ++ ys₁       ↔⟨ SK-sym $ ++↔ ⟩
    (x ∈ xs₁ ⊎ x ∈ ys₁)  ∼⟨ xs₁≈xs₂ ⊎-cong ys₁≈ys₂ ⟩
    (x ∈ xs₂ ⊎ x ∈ ys₂)  ↔⟨ ++↔ ⟩
    x ∈ xs₂ ++ ys₂       ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- concat

module _ {k} {xss yss : List (List A)} where

  concat-cong : xss ∼[ k ] yss → concat xss ∼[ k ] concat yss
  concat-cong xss≈yss {x} = begin
    x ∈ concat xss        ↔⟨ SK-sym concat↔ ⟩
    Any (Any (x ≡_)) xss  ∼⟨ Any-cong (λ _ → _ ∎) xss≈yss ⟩
    Any (Any (x ≡_)) yss  ↔⟨ concat↔ ⟩
    x ∈ concat yss         ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _>>=_

module _ {k} {A B : Set a} {xs ys} {f g : A → List B} where

  >>=-cong : xs ∼[ k ] ys → (∀ x → f x ∼[ k ] g x) →
             (xs >>= f) ∼[ k ] (ys >>= g)
  >>=-cong xs≈ys f≈g {x} = begin
    x ∈ (xs >>= f)          ↔⟨ SK-sym >>=↔ ⟩
    Any (λ y → x ∈ f y) xs  ∼⟨ Any-cong (λ x → f≈g x) xs≈ys ⟩
    Any (λ y → x ∈ g y) ys  ↔⟨ >>=↔ ⟩
    x ∈ (ys >>= g)          ∎
    where open Related.EquationalReasoning


------------------------------------------------------------------------
-- _⊛_

module _ {k} {A B : Set a} {fs gs : List (A → B)} {xs ys} where

  ⊛-cong : fs ∼[ k ] gs → xs ∼[ k ] ys → (fs ⊛ xs) ∼[ k ] (gs ⊛ ys)
  ⊛-cong fs≈gs xs≈ys {x} = begin
    x ∈ (fs ⊛ xs)
      ≡⟨ P.cong (x ∈_) (Applicative.unfold-⊛ fs xs) ⟩
    x ∈ (fs >>= λ f → xs >>= λ x → pure (f x))
      ∼⟨ >>=-cong fs≈gs (λ f → >>=-cong xs≈ys λ x → K-refl) ⟩
    x ∈ (gs >>= λ g → ys >>= λ y → pure (g y))
      ≡⟨ P.cong (x ∈_) (Applicative.unfold-⊛ gs ys) ⟨
    x ∈ (gs ⊛ ys) ∎
    where open Related.EquationalReasoning

------------------------------------------------------------------------
-- _⊗_

module _ {ℓ k} {A B : Set ℓ} {xs₁ xs₂ : List A} {ys₁ ys₂ : List B} where

  ⊗-cong : xs₁ ∼[ k ] xs₂ → ys₁ ∼[ k ] ys₂ →
           (xs₁ ⊗ ys₁) ∼[ k ] (xs₂ ⊗ ys₂)
  ⊗-cong xs₁≈xs₂ ys₁≈ys₂ =
    ⊛-cong (map-cong (λ _ → refl) xs₁≈xs₂) ys₁≈ys₂

------------------------------------------------------------------------
-- Other properties

-- _++_ and [] form a commutative monoid, with either bag or set
-- equality as the underlying equality.

commutativeMonoid : SymmetricKind → Set a → CommutativeMonoid _ _
commutativeMonoid {a} k A = record
  { Carrier             = List A
  ; _≈_                 = _∼[ ⌊ k ⌋ ]_
  ; _∙_                 = _++_
  ; ε                   = []
  ; isCommutativeMonoid = isCommutativeMonoidˡ record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = Eq.isEquivalence
        ; ∙-cong        = ++-cong
        }
      ; assoc         = λ xs ys zs →
                          Eq.reflexive (LP.++-assoc xs ys zs)
      }
    ; identityˡ = λ xs → K-refl
    ; comm      = λ xs ys → ↔⇒ (++↔++ xs ys)
    }
  }
  where open Related.EquationalReasoning

-- The only list which is bag or set equal to the empty list (or a
-- subset or subbag of the list) is the empty list itself.

empty-unique : ∀ {k} → xs ∼[ ⌊ k ⌋→ ] [] → xs ≡ []
empty-unique {xs = []}    _    = refl
empty-unique {xs = _ ∷ _} ∷∼[] with ⇒→ ∷∼[] (here refl)
... | ()

-- _++_ is idempotent (under set equality).

++-idempotent : Idempotent {A = List A} _∼[ set ]_ _++_
++-idempotent xs {x} =
  x ∈ xs ++ xs  ∼⟨ mk⇔ ([ id , id ]′ ∘ (Inverse.from $ ++↔))
                                  (Inverse.to ++↔ ∘ inj₁) ⟩
  x ∈ xs        ∎
  where open Related.EquationalReasoning

-- The list monad's bind distributes from the left over _++_.

>>=-left-distributive :
  ∀ (xs : List A) {f g : A → List B} →
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
  ∀ (fs : List (A → B)) xs₁ xs₂ →
  (fs ⊛ (xs₁ ++ xs₂)) ∼[ bag ] (fs ⊛ xs₁) ++ (fs ⊛ xs₂)
⊛-left-distributive {B = B} fs xs₁ xs₂ = begin
  fs ⊛ (xs₁ ++ xs₂)                       ≡⟨ Applicative.unfold-⊛ fs (xs₁ ++ xs₂) ⟩
  (fs >>= λ f → xs₁ ++ xs₂ >>= pure ∘ f)  ≡⟨ (MP.cong (refl {x = fs}) λ f →
                                                MP.right-distributive xs₁ xs₂ (pure ∘ f)) ⟩
  (fs >>= λ f → (xs₁ >>= pure ∘ f) ++
                (xs₂ >>= pure ∘ f))       ≈⟨ >>=-left-distributive fs ⟩

  (fs >>= λ f → xs₁ >>= pure ∘ f) ++
  (fs >>= λ f → xs₂ >>= pure ∘ f)         ≡⟨ P.cong₂ _++_ (Applicative.unfold-⊛ fs xs₁) (Applicative.unfold-⊛ fs xs₂) ⟨

  (fs ⊛ xs₁) ++ (fs ⊛ xs₂)                ∎
  where open EqR ([ bag ]-Equality B)

private

  -- If x ∷ xs is set equal to x ∷ ys, then xs and ys are not
  -- necessarily set equal.

  ¬-drop-cons : ∀ {x : A} →
    ¬ (∀ {xs ys} → x ∷ xs ∼[ set ] x ∷ ys → xs ∼[ set ] ys)
  ¬-drop-cons {x = x} drop-cons with Equivalence.to x∼[] (here refl)
    where
    x,x≈x :  (x ∷ x ∷ []) ∼[ set ] [ x ]
    x,x≈x = ++-idempotent [ x ]

    x∼[] : [ x ] ∼[ set ] []
    x∼[] = drop-cons x,x≈x
  ... | ()

-- However, the corresponding property does hold for bag equality.

drop-cons : ∀ {x : A} {xs ys} → x ∷ xs ∼[ bag ] x ∷ ys → xs ∼[ bag ] ys
drop-cons {x = x} {xs} {ys} x∷xs≈x∷ys =
  ⊎-left-cancellative
    (∼→⊎↔⊎ x∷xs≈x∷ys)
    (lemma x∷xs≈x∷ys)
    (lemma (SK-sym x∷xs≈x∷ys))

  where

  -- TODO: Some of the code below could perhaps be exposed to users.

  -- List membership can be expressed as "there is an index which
  -- points to the element".

  ∈-index : ∀ {z} (xs : List A) → z ∈ xs ↔ ∃ λ i → z ≡ lookup xs i
  ∈-index {z = z} [] =
    z ∈ []                              ↔⟨ SK-sym ⊥↔Any[] ⟩
    ⊥                                   ↔⟨ mk↔ₛ′ (λ ()) (λ { (() , _) }) (λ { (() , _) }) (λ ()) ⟩
    (∃ λ (i : Fin 0) → z ≡ lookup [] i)  ∎
    where
    open Related.EquationalReasoning
  ∈-index {z = z} (x ∷ xs) =
    z ∈ x ∷ xs                         ↔⟨ SK-sym (∷↔ _) ⟩
    (z ≡ x ⊎ z ∈ xs)                   ↔⟨ K-refl ⊎-cong ∈-index xs ⟩
    (z ≡ x ⊎ ∃ λ i → z ≡ lookup xs i)  ↔⟨ mk↔ₛ′ (λ { (inj₁ p) → zero , p; (inj₂ (i , p)) → suc i , p })
                                                  (λ { (zero , p) → inj₁ p; (suc i , p) → inj₂ (i , p) })
                                                  (λ { (zero , _) → refl; (suc _ , _) → refl })
                                                  (λ { (inj₁ _) → refl; (inj₂ _) → refl }) ⟩
    (∃ λ i → z ≡ lookup (x ∷ xs) i)    ∎
    where
    open Related.EquationalReasoning

  -- The index which points to the element.

  index-of : ∀ {a} {A : Set a} {z} {xs : List A} →
             z ∈ xs → Fin (length xs)
  index-of = proj₁ ∘ (Inverse.to (∈-index _))

  -- The type ∃ λ z → z ∈ xs is isomorphic to Fin n, where n is the
  -- length of xs.
  --
  -- Thierry Coquand pointed out that (a variant of) this statement is
  -- a generalisation of the fact that singletons are contractible.

  Fin-length : ∀ {a} {A : Set a}
               (xs : List A) → (∃ λ z → z ∈ xs) ↔ Fin (length xs)
  Fin-length xs =
    (∃ λ z → z ∈ xs)                   ↔⟨ Σ.cong K-refl (∈-index xs) ⟩
    (∃ λ z → ∃ λ i → z ≡ lookup xs i)  ↔⟨ ∃∃↔∃∃ _ ⟩
    (∃ λ i → ∃ λ z → z ≡ lookup xs i)  ↔⟨ Σ.cong K-refl (mk↔ₛ′ _ (λ _ → _ , refl) (λ _ → refl) (λ { (_ , refl) → refl })) ⟩
    (Fin (length xs) × ⊤)              ↔⟨ ×-identityʳ _ _ ⟩
    Fin (length xs)                    ∎
    where
    open Related.EquationalReasoning

  -- From this lemma we get that lists which are bag equivalent have
  -- related lengths.

  Fin-length-cong : ∀ {a} {A : Set a} {xs ys : List A} →
                    xs ∼[ bag ] ys → Fin (length xs) ↔ Fin (length ys)
  Fin-length-cong {xs = xs} {ys} xs≈ys =
    Fin (length xs)   ↔⟨ SK-sym $ Fin-length xs ⟩
    ∃ (λ z → z ∈ xs)  ↔⟨ Σ.cong K-refl xs≈ys ⟩
    ∃ (λ z → z ∈ ys)  ↔⟨ Fin-length ys ⟩
    Fin (length ys)   ∎
    where
    open Related.EquationalReasoning

  -- The index-of function commutes with applications of certain
  -- inverses.

  index-of-commutes :
    ∀ {a} {A : Set a} {z : A} {xs ys} →
    (xs≈ys : xs ∼[ bag ] ys) (p : z ∈ xs) →
    index-of (Inverse.to xs≈ys p) ≡
    Inverse.to (Fin-length-cong xs≈ys) (index-of p)
  index-of-commutes {z = z} {xs} {ys} xs≈ys p =
    index-of (to xs≈ys p)                                        ≡⟨ lemma z p ⟩

    index-of (to xs≈ys (proj₂
      (from (Fin-length xs) (to (Fin-length xs) (z , p)))))   ≡⟨⟩

    index-of (proj₂ (Prod.map id (to xs≈ys)
      (from (Fin-length xs) (to (Fin-length xs) (z , p)))))  ≡⟨⟩

    to (Fin-length ys) (Prod.map id (to xs≈ys)
      (from (Fin-length xs) (index-of p)))                          ≡⟨⟩

    to (Fin-length-cong xs≈ys) (index-of p)                        ∎
    where
    open P.≡-Reasoning
    open Inverse

    lemma :
      ∀ z p →
      index-of (to xs≈ys p) ≡
      index-of (to xs≈ys (proj₂
        (from (Fin-length xs) (to (Fin-length xs) (z , p)))))
    lemma z p with to (Fin-length xs) (z , p)
                 | strictlyInverseʳ (Fin-length xs) (z , p)
    lemma .(lookup xs i) .(from (∈-index xs) (i , refl)) | i | refl =
      refl

  -- Bag equivalence isomorphisms preserve index equality. Note that
  -- this means that, even if the underlying equality is proof
  -- relevant, a bag equivalence isomorphism cannot map two distinct
  -- proofs, that point to the same position, to different positions.

  index-equality-preserved :
    ∀ {a} {A : Set a} {z : A} {xs ys} {p q : z ∈ xs}
    (xs≈ys : xs ∼[ bag ] ys) →
    index-of p ≡ index-of q →
    index-of (Inverse.to xs≈ys p) ≡
    index-of (Inverse.to xs≈ys q)
  index-equality-preserved {p = p} {q} xs≈ys eq =
    index-of (Inverse.to xs≈ys p)                  ≡⟨ index-of-commutes xs≈ys p ⟩
    Inverse.to (Fin-length-cong xs≈ys) (index-of p)  ≡⟨ P.cong (Inverse.to (Fin-length-cong xs≈ys)) eq ⟩
    Inverse.to (Fin-length-cong xs≈ys) (index-of q)  ≡⟨ P.sym $ index-of-commutes xs≈ys q ⟩
    index-of (Inverse.to xs≈ys q)                  ∎
    where
    open P.≡-Reasoning

  -- The old inspect idiom.

  inspect : ∀ {a} {A : Set a} (x : A) → ∃ (x ≡_)
  inspect x = x , refl

  -- A function is "well-behaved" if any "left" element which is the
  -- image of a "right" element is in turn not mapped to another
  -- "left" element.

  Well-behaved : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
                 (A ⊎ B → A ⊎ C) → Set _
  Well-behaved f =
    ∀ {b a a′} → f (inj₂ b) ≡ inj₁ a → f (inj₁ a) ≢ inj₁ a′

  -- The type constructor _⊎_ is left cancellative for certain
  -- well-behaved inverses.

  ⊎-left-cancellative :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    (f : (A ⊎ B) ↔ (A ⊎ C)) →
    Well-behaved (Inverse.to   f) →
    Well-behaved (Inverse.from f) →
    B ↔ C
  ⊎-left-cancellative {A = A} = λ inv to-hyp from-hyp → mk↔ₛ′
    (g (to   inv) to-hyp)
    (g (from inv) from-hyp)
    (g∘g (SK-sym inv) from-hyp to-hyp)
    (g∘g         inv  to-hyp from-hyp)
    where
    open Inverse

    module _
      {a b c} {A : Set a} {B : Set b} {C : Set c}
      (f : A ⊎ B → A ⊎ C)
      (hyp : Well-behaved f)
      where

      mutual

        g : B → C
        g b = g′ (inspect (f (inj₂ b)))

        g′ : ∀ {b} → ∃ (f (inj₂ b) ≡_) → C
        g′ (inj₂ c , _)  = c
        g′ (inj₁ a , eq) = g″ eq (inspect (f (inj₁ a)))

        g″ : ∀ {a b} →
             f (inj₂ b) ≡ inj₁ a → ∃ (f (inj₁ a) ≡_) → C
        g″ _   (inj₂ c , _)   = c
        g″ eq₁ (inj₁ _ , eq₂) = ⊥-elim $ hyp eq₁ eq₂

    g∘g : ∀ {b c} {B : Set b} {C : Set c}
          (f : (A ⊎ B) ↔ (A ⊎ C)) →
          (to-hyp   : Well-behaved (to   f)) →
          (from-hyp : Well-behaved (from f)) →
          ∀ b → g (from f) from-hyp (g (to f) to-hyp b) ≡ b
    g∘g f to-hyp from-hyp b = g∘g′
      where
      open P.≡-Reasoning

      g∘g′ : g (from f) from-hyp (g (to f) to-hyp b) ≡ b
      g∘g′ with inspect (to f (inj₂ b))
      g∘g′ | inj₂ c , eq₁ with inspect (from f (inj₂ c))
      ...   | inj₂ b′ , eq₂ = inj₂-injective (
        inj₂ b′            ≡⟨ P.sym eq₂ ⟩
        from f (inj₂ c)   ≡⟨ to-from f eq₁ ⟩
        inj₂ b            ∎)
      ...   | inj₁ a  , eq₂ with
        inj₁ a             ≡⟨ P.sym eq₂ ⟩
        from f (inj₂ c)    ≡⟨ to-from f eq₁ ⟩
        inj₂ b             ∎
      ... | ()
      g∘g′ | inj₁ a , eq₁ with inspect (to f (inj₁ a))
      g∘g′ | inj₁ a , eq₁ | inj₁ a′ , eq₂ = ⊥-elim $ to-hyp eq₁ eq₂
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ with inspect (from f (inj₂ c))
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ | inj₂ b′ , eq₃ with
        inj₁ a             ≡⟨ P.sym (to-from f eq₂) ⟩
        from f (inj₂ c)    ≡⟨ eq₃ ⟩
        inj₂ b′            ∎
      ... | ()
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ | inj₁ a′ , eq₃ with inspect (from f $ inj₁ a′)
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ | inj₁ a′ , eq₃ | inj₁ a″ , eq₄ = ⊥-elim $ from-hyp eq₃ eq₄
      g∘g′ | inj₁ a , eq₁ | inj₂ c  , eq₂ | inj₁ a′ , eq₃ | inj₂ b′ , eq₄ = inj₂-injective (
        let lemma =
              inj₁ a′             ≡⟨ P.sym eq₃ ⟩
              from f (inj₂ c)    ≡⟨ to-from f eq₂ ⟩
              inj₁ a             ∎
        in
        inj₂ b′             ≡⟨ P.sym eq₄ ⟩
        from f (inj₁ a′)    ≡⟨ P.cong (from f ∘ inj₁) $ inj₁-injective lemma ⟩
        from f (inj₁ a)    ≡⟨ to-from f eq₁ ⟩
        inj₂ b              ∎)

  -- Some final lemmas.

  ∼→⊎↔⊎ :
    ∀ {x : A} {xs ys} →
    x ∷ xs ∼[ bag ] x ∷ ys →
    ∀ {z} → (z ≡ x ⊎ z ∈ xs) ↔ (z ≡ x ⊎ z ∈ ys)
  ∼→⊎↔⊎ {x = x} {xs} {ys} x∷xs≈x∷ys {z} =
    (z ≡ x ⊎ z ∈ xs)  ↔⟨ ∷↔ _ ⟩
    z ∈ x ∷ xs        ↔⟨ x∷xs≈x∷ys ⟩
    z ∈ x ∷ ys        ↔⟨ SK-sym (∷↔ _) ⟩
    (z ≡ x ⊎ z ∈ ys)  ∎
    where
    open Related.EquationalReasoning

  lemma : ∀ {xs ys} (inv : x ∷ xs ∼[ bag ] x ∷ ys) {z} →
          Well-behaved (Inverse.to (∼→⊎↔⊎ inv {z}))
  lemma {xs} inv {b = z∈xs} {a = p} {a′ = q} hyp₁ hyp₂ with
    zero                                                                  ≡⟨⟩
    index-of {xs = x ∷ xs} (here p)                                       ≡⟨⟩
    index-of {xs = x ∷ xs} (to (∷↔ _) $ inj₁ p)                         ≡⟨ P.cong (index-of ∘ (to (∷↔ (_ ≡_)))) $ P.sym $
                                                                               to-from (∼→⊎↔⊎ inv) {x = inj₁ p} hyp₂ ⟩
    index-of {xs = x ∷ xs} (to (∷↔ _) $ (from (∼→⊎↔⊎ inv) $ inj₁ q))  ≡⟨ P.cong index-of $
                                                                               strictlyInverseˡ (∷↔ _) (from inv (here q)) ⟩
    index-of {xs = x ∷ xs} (to (SK-sym inv) $ here q)                   ≡⟨ index-equality-preserved (SK-sym inv) refl ⟩
    index-of {xs = x ∷ xs} (to (SK-sym inv) $ here p)                   ≡⟨ P.cong index-of $ P.sym $
                                                                               strictlyInverseˡ (∷↔ _) (from inv (here p)) ⟩
    index-of {xs = x ∷ xs} (to (∷↔ _) (from (∼→⊎↔⊎ inv) $ inj₁ p))  ≡⟨ P.cong (index-of ∘ (to (∷↔ (_ ≡_)))) $
                                                                               to-from (∼→⊎↔⊎ inv) {x = inj₂ z∈xs} hyp₁ ⟩
    index-of {xs = x ∷ xs} (to (∷↔ _) $ inj₂ z∈xs)                      ≡⟨⟩
    index-of {xs = x ∷ xs} (there z∈xs)                                   ≡⟨⟩
    suc (index-of {xs = xs} z∈xs)                                         ∎
    where
    open Inverse
    open P.≡-Reasoning
  ... | ()

------------------------------------------------------------------------
-- Relationships to other relations

↭⇒∼bag : _↭_ {A = A} ⇒ _∼[ bag ]_
↭⇒∼bag {A = A} xs↭ys {v} = mk↔ₛ′ (to xs↭ys) (from xs↭ys) (to∘from xs↭ys) (from∘to xs↭ys)
  where
  to : ∀ {xs ys} → xs ↭ ys → v ∈ xs → v ∈ ys
  to xs↭ys = Any-resp-↭ {A = A} xs↭ys

  from : ∀ {xs ys} → xs ↭ ys → v ∈ ys → v ∈ xs
  from xs↭ys = Any-resp-↭ (↭-sym xs↭ys)

  from∘to : ∀ {xs ys} (p : xs ↭ ys) (q : v ∈ xs) → from p (to p q) ≡ q
  from∘to refl          v∈xs                 = refl
  from∘to (prep _ _)    (here refl)          = refl
  from∘to (prep _ p)    (there v∈xs)         = P.cong there (from∘to p v∈xs)
  from∘to (swap x y p)  (here refl)          = refl
  from∘to (swap x y p)  (there (here refl))  = refl
  from∘to (swap x y p)  (there (there v∈xs)) = P.cong (there ∘ there) (from∘to p v∈xs)
  from∘to (trans p₁ p₂) v∈xs
    rewrite from∘to p₂ (Any-resp-↭ p₁ v∈xs)
          | from∘to p₁ v∈xs                  = refl

  to∘from : ∀ {xs ys} (p : xs ↭ ys) (q : v ∈ ys) → to p (from p q) ≡ q
  to∘from p with from∘to (↭-sym p)
  ... | res rewrite ↭-sym-involutive p = res

∼bag⇒↭ : _∼[ bag ]_ ⇒ _↭_ {A = A}
∼bag⇒↭ {A = A} {[]} eq with empty-unique (↔-sym eq)
... | refl = refl
∼bag⇒↭ {A = A} {x ∷ xs} eq with ∈-∃++ (Inverse.to (eq {x}) (here P.refl))
... | zs₁ , zs₂ , p rewrite p = begin
  x ∷ xs           <⟨ ∼bag⇒↭ (drop-cons (↔-trans eq (comm zs₁ (x ∷ zs₂)))) ⟩
  x ∷ (zs₂ ++ zs₁) <⟨ ++-comm zs₂ zs₁ ⟩
  x ∷ (zs₁ ++ zs₂) ↭⟨ shift x zs₁ zs₂ ⟨
  zs₁ ++ x ∷ zs₂   ∎
  where
  open CommutativeMonoid (commutativeMonoid bag A)
  open PermutationReasoning
