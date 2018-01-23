------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to bag and set equality
------------------------------------------------------------------------

-- Bag and set equality are defined in Data.List.Any.

module Data.List.Any.BagAndSetEquality where

open import Algebra
open import Algebra.FunctionProperties
open import Category.Monad
open import Data.List as List hiding (lookup)
open import Data.List.Categorical using (monad; module MonadProperties)
import Data.List.Properties as LP
open import Data.List.Any as Any using (Any; index); open Any.Any
open import Data.List.Any.Properties
open import Data.List.Any.Membership.Propositional
open import Data.Product
open import Data.Sum
open import Data.Sum.Relation.General
open import Data.Fin as F using (Fin)
import Data.Fin.Properties as FP
private
  module Tbl where
    open import Data.Table public
    open import Data.Table.Properties public
open Tbl using (Table)
open import Function
open import Function.Equality using (_⟨$⟩_)
import Function.Equivalence as FE
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Related as Related using (↔⇒; ⌊_⌋; ⌊_⌋→; ⇒→)
open import Function.Related.TypeIsomorphisms
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_)
open import Relation.Nullary
import Data.Product.Relation.SigmaPropositional as OverΣ
open OverΣ using (OverΣ)

open import Data.List.Any.Membership.Propositional.Properties
private
  module Eq  {k a} {A : Set a} = Setoid ([ k ]-Equality A)
  module Ord {k a} {A : Set a} = Preorder ([ k ]-Order A)
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)
  module ListMonoid {a} {A : Set a} = Monoid (LP.++-monoid A)
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})
  module MP = MonadProperties

------------------------------------------------------------------------
-- Congruence lemmas

-- _∷_ is a congruence.

∷-cong : ∀ {a k} {A : Set a} {x₁ x₂ : A} {xs₁ xs₂} →
         x₁ ≡ x₂ → xs₁ ∼[ k ] xs₂ → x₁ ∷ xs₁ ∼[ k ] x₂ ∷ xs₂
∷-cong {x₂ = x} {xs₁} {xs₂} P.refl xs₁≈xs₂ {y} =
  y ∈ x ∷ xs₁        ↔⟨ sym $ ∷↔ (_≡_ y) ⟩
  (y ≡ x ⊎ y ∈ xs₁)  ∼⟨ (y ≡ x ∎) ⊎-cong xs₁≈xs₂ ⟩
  (y ≡ x ⊎ y ∈ xs₂)  ↔⟨ ∷↔ (_≡_ y) ⟩
  y ∈ x ∷ xs₂        ∎
  where open Related.EquationalReasoning

-- List.map is a congruence.

map-cong : ∀ {ℓ k} {A B : Set ℓ} {f₁ f₂ : A → B} {xs₁ xs₂} →
           f₁ ≗ f₂ → xs₁ ∼[ k ] xs₂ →
           List.map f₁ xs₁ ∼[ k ] List.map f₂ xs₂
map-cong {ℓ} {f₁ = f₁} {f₂} {xs₁} {xs₂} f₁≗f₂ xs₁≈xs₂ {x} =
  x ∈ List.map f₁ xs₁       ↔⟨ sym $ map↔ {a = ℓ} {b = ℓ} {p = ℓ} ⟩
  Any (λ y → x ≡ f₁ y) xs₁  ∼⟨ Any-cong (↔⇒ ∘ helper) xs₁≈xs₂ ⟩
  Any (λ y → x ≡ f₂ y) xs₂  ↔⟨ map↔ {a = ℓ} {b = ℓ} {p = ℓ} ⟩
  x ∈ List.map f₂ xs₂       ∎
  where
  open Related.EquationalReasoning

  helper : ∀ y → x ≡ f₁ y ↔ x ≡ f₂ y
  helper y = record
    { to         = P.→-to-⟶ (λ x≡f₁y → P.trans x≡f₁y (        f₁≗f₂ y))
    ; from       = P.→-to-⟶ (λ x≡f₂y → P.trans x≡f₂y (P.sym $ f₁≗f₂ y))
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.≡-irrelevance _ _
      ; right-inverse-of = λ _ → P.≡-irrelevance _ _
      }
    }

-- _++_ is a congruence.

++-cong : ∀ {a k} {A : Set a} {xs₁ xs₂ ys₁ ys₂ : List A} →
          xs₁ ∼[ k ] xs₂ → ys₁ ∼[ k ] ys₂ →
          xs₁ ++ ys₁ ∼[ k ] xs₂ ++ ys₂
++-cong {a} {xs₁ = xs₁} {xs₂} {ys₁} {ys₂} xs₁≈xs₂ ys₁≈ys₂ {x} =
  x ∈ xs₁ ++ ys₁       ↔⟨ sym $ ++↔ {a = a} {p = a} ⟩
  (x ∈ xs₁ ⊎ x ∈ ys₁)  ∼⟨ xs₁≈xs₂ ⊎-cong ys₁≈ys₂ ⟩
  (x ∈ xs₂ ⊎ x ∈ ys₂)  ↔⟨ ++↔ {a = a} {p = a} ⟩
  x ∈ xs₂ ++ ys₂       ∎
  where open Related.EquationalReasoning

-- concat is a congruence.

concat-cong : ∀ {a k} {A : Set a} {xss₁ xss₂ : List (List A)} →
              xss₁ ∼[ k ] xss₂ → concat xss₁ ∼[ k ] concat xss₂
concat-cong {a} {xss₁ = xss₁} {xss₂} xss₁≈xss₂ {x} =
  x ∈ concat xss₁         ↔⟨ sym $ concat↔ {a = a} {p = a} ⟩
  Any (Any (_≡_ x)) xss₁  ∼⟨ Any-cong (λ _ → _ ∎) xss₁≈xss₂ ⟩
  Any (Any (_≡_ x)) xss₂  ↔⟨ concat↔ {a = a} {p = a} ⟩
  x ∈ concat xss₂         ∎
  where open Related.EquationalReasoning

-- The list monad's bind is a congruence.

>>=-cong : ∀ {ℓ k} {A B : Set ℓ} {xs₁ xs₂} {f₁ f₂ : A → List B} →
           xs₁ ∼[ k ] xs₂ → (∀ x → f₁ x ∼[ k ] f₂ x) →
           (xs₁ >>= f₁) ∼[ k ] (xs₂ >>= f₂)
>>=-cong {ℓ} {xs₁ = xs₁} {xs₂} {f₁} {f₂} xs₁≈xs₂ f₁≈f₂ {x} =
  x ∈ (xs₁ >>= f₁)          ↔⟨ sym $ >>=↔ {ℓ = ℓ} {p = ℓ} ⟩
  Any (λ y → x ∈ f₁ y) xs₁  ∼⟨ Any-cong (λ x → f₁≈f₂ x) xs₁≈xs₂ ⟩
  Any (λ y → x ∈ f₂ y) xs₂  ↔⟨ >>=↔ {ℓ = ℓ} {p = ℓ} ⟩
  x ∈ (xs₂ >>= f₂)          ∎
  where open Related.EquationalReasoning

-- _⊛_ is a congruence.

⊛-cong : ∀ {ℓ k} {A B : Set ℓ} {fs₁ fs₂ : List (A → B)} {xs₁ xs₂} →
         fs₁ ∼[ k ] fs₂ → xs₁ ∼[ k ] xs₂ →
         (fs₁ ⊛ xs₁) ∼[ k ] (fs₂ ⊛ xs₂)
⊛-cong fs₁≈fs₂ xs₁≈xs₂ =
  >>=-cong fs₁≈fs₂ λ f →
  >>=-cong xs₁≈xs₂ λ x →
  _ ∎
  where open Related.EquationalReasoning

-- _⊗_ is a congruence.

⊗-cong : ∀ {ℓ k} {A B : Set ℓ} {xs₁ xs₂ : List A} {ys₁ ys₂ : List B} →
         xs₁ ∼[ k ] xs₂ → ys₁ ∼[ k ] ys₂ →
         (xs₁ ⊗ ys₁) ∼[ k ] (xs₂ ⊗ ys₂)
⊗-cong {ℓ} xs₁≈xs₂ ys₁≈ys₂ =
  ⊛-cong (⊛-cong (Ord.refl {x = [ _,_ {a = ℓ} {b = ℓ} ]})
                 xs₁≈xs₂)
         ys₁≈ys₂

------------------------------------------------------------------------
-- Other properties

-- _++_ and [] form a commutative monoid, with either bag or set
-- equality as the underlying equality.

commutativeMonoid : ∀ {a} → Symmetric-kind → Set a →
                    CommutativeMonoid _ _
commutativeMonoid {a} k A = record
  { Carrier             = List A
  ; _≈_                 = λ xs ys → xs ∼[ ⌊ k ⌋ ] ys
  ; _∙_                 = _++_
  ; ε                   = []
  ; isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = Eq.isEquivalence
      ; assoc         = λ xs ys zs →
                          Eq.reflexive (ListMonoid.assoc xs ys zs)
      ; ∙-cong        = ++-cong
      }
    ; identityˡ = λ xs {x} → x ∈ xs ∎
    ; comm      = λ xs ys {x} →
                    x ∈ xs ++ ys  ↔⟨ ++↔++ {a = a} {p = a} xs ys ⟩
                    x ∈ ys ++ xs  ∎
    }
  }
  where open Related.EquationalReasoning

-- The only list which is bag or set equal to the empty list (or a
-- subset or subbag of the list) is the empty list itself.

empty-unique : ∀ {k a} {A : Set a} {xs : List A} →
               xs ∼[ ⌊ k ⌋→ ] [] → xs ≡ []
empty-unique {xs = []}    _    = P.refl
empty-unique {xs = _ ∷ _} ∷∼[] with ⇒→ ∷∼[] (here P.refl)
... | ()

-- _++_ is idempotent (under set equality).

++-idempotent : ∀ {a} {A : Set a} →
                Idempotent (λ (xs ys : List A) → xs ∼[ set ] ys) _++_
++-idempotent {a} xs {x} =
  x ∈ xs ++ xs  ∼⟨ FE.equivalence ([ id , id ]′ ∘ _⟨$⟩_ (Inverse.from $ ++↔ {a = a} {p = a}))
                                  (_⟨$⟩_ (Inverse.to $ ++↔ {a = a} {p = a}) ∘ inj₁) ⟩
  x ∈ xs        ∎
  where open Related.EquationalReasoning

-- The list monad's bind distributes from the left over _++_.

>>=-left-distributive :
  ∀ {ℓ} {A B : Set ℓ} (xs : List A) {f g : A → List B} →
  (xs >>= λ x → f x ++ g x) ∼[ bag ] (xs >>= f) ++ (xs >>= g)
>>=-left-distributive {ℓ} xs {f} {g} {y} =
  y ∈ (xs >>= λ x → f x ++ g x)                      ↔⟨ sym $ >>=↔ {ℓ = ℓ} {p = ℓ} ⟩
  Any (λ x → y ∈ f x ++ g x) xs                      ↔⟨ sym (Any-cong (λ _ → ++↔ {a = ℓ} {p = ℓ}) (_ ∎)) ⟩
  Any (λ x → y ∈ f x ⊎ y ∈ g x) xs                   ↔⟨ sym $ ⊎↔ {a = ℓ} {p = ℓ} {q = ℓ} ⟩
  (Any (λ x → y ∈ f x) xs ⊎ Any (λ x → y ∈ g x) xs)  ↔⟨ >>=↔ {ℓ = ℓ} {p = ℓ} ⟨ ×⊎.+-cong {ℓ = ℓ} ⟩ >>=↔ {ℓ = ℓ} {p = ℓ} ⟩
  (y ∈ (xs >>= f) ⊎ y ∈ (xs >>= g))                  ↔⟨ ++↔ {a = ℓ} {p = ℓ} ⟩
  y ∈ (xs >>= f) ++ (xs >>= g)                       ∎
  where open Related.EquationalReasoning

-- The same applies to _⊛_.

⊛-left-distributive :
  ∀ {ℓ} {A B : Set ℓ} (fs : List (A → B)) xs₁ xs₂ →
  (fs ⊛ (xs₁ ++ xs₂)) ∼[ bag ] (fs ⊛ xs₁) ++ (fs ⊛ xs₂)
⊛-left-distributive {B = B} fs xs₁ xs₂ = begin
  fs ⊛ (xs₁ ++ xs₂)                         ≡⟨ P.refl ⟩
  (fs >>= λ f → xs₁ ++ xs₂ >>= return ∘ f)  ≡⟨ (MP.cong (P.refl {x = fs}) λ f →
                                                MP.right-distributive xs₁ xs₂ (return ∘ f)) ⟩
  (fs >>= λ f → (xs₁ >>= return ∘ f) ++
                (xs₂ >>= return ∘ f))       ≈⟨ >>=-left-distributive fs ⟩

  (fs >>= λ f → xs₁ >>= return ∘ f) ++
  (fs >>= λ f → xs₂ >>= return ∘ f)         ≡⟨ P.refl ⟩

  (fs ⊛ xs₁) ++ (fs ⊛ xs₂)                  ∎
  where open EqR ([ bag ]-Equality B)

private

  -- If x ∷ xs is set equal to x ∷ ys, then xs and ys are not
  -- necessarily set equal.

  ¬-drop-cons :
    ∀ {a} {A : Set a} {x : A} →
    ¬ (∀ {xs ys} → x ∷ xs ∼[ set ] x ∷ ys → xs ∼[ set ] ys)
  ¬-drop-cons {x = x} drop-cons
    with FE.Equivalence.to x∼[] ⟨$⟩ here P.refl
    where
    x,x≈x :  (x ∷ x ∷ []) ∼[ set ] [ x ]
    x,x≈x = ++-idempotent [ x ]

    x∼[] : [ x ] ∼[ set ] []
    x∼[] = drop-cons x,x≈x
  ... | ()

-- However, the corresponding property does hold for bag equality.

drop-cons : ∀ {a} {A : Set a} {x : A} {xs ys} →
            x ∷ xs ∼[ bag ] x ∷ ys → xs ∼[ bag ] ys
drop-cons {A = A} {x} {xs} {ys} x∷xs≈x∷ys {z} = record
  { to         = P.→-to-⟶ $ f           x∷xs≈x∷ys
  ; from       = P.→-to-⟶ $ f $ Inv.sym x∷xs≈x∷ys
  ; inverse-of = record
    { left-inverse-of  = f∘f           x∷xs≈x∷ys
    ; right-inverse-of = f∘f $ Inv.sym x∷xs≈x∷ys
    }
  }
  where
  open Inverse
  open P.≡-Reasoning

  f : ∀ {xs ys z} → (z ∈ x ∷ xs) ↔ (z ∈ x ∷ ys) → z ∈ xs → z ∈ ys
  f inv z∈xs with to inv ⟨$⟩ there z∈xs | left-inverse-of inv (there z∈xs)
  f inv z∈xs | there z∈ys   | left⁺ = z∈ys
  f inv z∈xs | here  z≡x    | left⁺ with to inv ⟨$⟩ here z≡x | left-inverse-of inv (here z≡x)
  f inv z∈xs | here  z≡x    | left⁺ | there z∈ys   | left⁰ = z∈ys
  f inv z∈xs | here  P.refl | left⁺ | here  P.refl | left⁰ with begin
    here P.refl               ≡⟨ P.sym left⁰ ⟩
    from inv ⟨$⟩ here P.refl  ≡⟨ left⁺ ⟩
    there z∈xs                ∎
  ... | ()

  f∘f : ∀ {xs ys z}
        (inv : (z ∈ x ∷ xs) ↔ (z ∈ x ∷ ys)) (p : z ∈ xs) →
        f (Inv.sym inv) (f inv p) ≡ p
  f∘f inv z∈xs with to inv ⟨$⟩ there z∈xs | left-inverse-of inv (there z∈xs)
  f∘f inv z∈xs | there z∈ys  | left⁺ with from inv ⟨$⟩ there z∈ys | right-inverse-of inv (there z∈ys)
  f∘f inv z∈xs | there z∈ys  | P.refl | .(there z∈xs) | _ = P.refl
  f∘f inv z∈xs | here z≡x    | left⁺ with to inv ⟨$⟩ here z≡x | left-inverse-of inv (here z≡x)
  f∘f inv z∈xs | here z≡x    | left⁺  | there z∈ys   | left⁰ with from inv ⟨$⟩ there z∈ys | right-inverse-of inv (there z∈ys)
  f∘f inv z∈xs | here z≡x    | left⁺  | there z∈ys   | P.refl | .(here z≡x) | _ with from inv ⟨$⟩ here z≡x
                                                                                   | right-inverse-of inv (here z≡x)
  f∘f inv z∈xs | here z≡x    | P.refl | there z∈ys   | P.refl | .(here z≡x) | _ | .(there z∈xs) | _ = P.refl
  f∘f inv z∈xs | here P.refl | left⁺  | here  P.refl | left⁰ with begin
    here P.refl               ≡⟨ P.sym left⁰ ⟩
    from inv ⟨$⟩ here P.refl  ≡⟨ left⁺ ⟩
    there z∈xs                ∎
  ... | ()


-- Some properties connecting permutations on finite sets to bag equality
module _ {a} {A : Set a} where
  -- If two lists are bag-equal, then there is a bijection between distinct
  -- elements of each list.

  bag-∈-↔ : ∀ {xs ys : List A} → xs ∼[ bag ] ys → (∃ λ x → x ∈ xs) ↔ (∃ λ y → y ∈ ys)
  bag-∈-↔ {xs}{ys} p = record
    { to = P.→-to-⟶ λ {(x , x∈xs) → x , Inverse.to p ⟨$⟩ x∈xs}
    ; from = P.→-to-⟶ λ {(y , y∈ys) → y , Inverse.from p ⟨$⟩ y∈ys}
    ; inverse-of = record
      { left-inverse-of = λ _ → OverΣ.to-≡ (P.refl , Inverse.left-inverse-of p _)
      ; right-inverse-of = λ _ → OverΣ.to-≡ (P.refl , Inverse.right-inverse-of p _)
      }
    }


  -- There is a bijection between distinct elements of a list and a set the size
  -- of the list's length.

  ∈-↔-length : (xs : List A) → (∃ λ x → x ∈ xs) ↔ (Fin (length xs))
  ∈-↔-length xs = record
    { to = P.→-to-⟶ (index ∘ proj₂)
    ; from = P.→-to-⟶ Tbl.lookup∈
    ; inverse-of = record
      { left-inverse-of = Tbl.lookup∈-index ∘ proj₂
      ; right-inverse-of = λ _ → Tbl.index-fromList-∈
      }
    }


  -- A bag-equality between two lists induces a permutation between the indices of
  -- their elements.

  bag-permutation : ∀ {xs ys : List A} → xs ∼[ bag ] ys → Fin (length xs) ↔ Fin (length ys)
  bag-permutation {xs} {ys} p =
    Fin (length xs)    ↔⟨ fr-sym (∈-↔-length xs) ⟩
    (∃ λ x → x ∈ xs)   ↔⟨ bag-∈-↔ p ⟩
    (∃ λ y → y ∈ ys)   ↔⟨ ∈-↔-length ys ⟩
    Fin (length ys)    ∎
    where open Related.EquationalReasoning renaming (sym to fr-sym)


  -- If two lists are bag-equal, then they have the same length.

  bag-length-≡ : ∀ {xs ys : List A} → xs ∼[ bag ] ys → length xs ≡ length ys
  bag-length-≡ p = FP.↔-≡ (bag-permutation p)


  -- The permutation between list element indices given by 'bag-permutation'
  -- correctly maps elements of each list to each other.

  bag-permutation-correct : ∀ {xs ys : List A} (p : xs ∼[ bag ] ys) → Tbl.fromList xs Tbl.≗ (Tbl.permute (bag-permutation p) (Tbl.fromList ys))
  bag-permutation-correct {xs} {ys} p i =
    begin
      lookup (fromList xs) i                                        ≡⟨ P.sym (fromList-index (Inverse.to p ⟨$⟩ fromList-∈ i)) ⟩
      lookup (fromList ys) (index (Inverse.to p ⟨$⟩ fromList-∈ i))  ≡⟨⟩
      lookup (Tbl.permute (bag-permutation p) (fromList ys)) i      ∎
    where
      open P.≡-Reasoning
      open Tbl

