------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership relation for AVL Maps
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}
open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Map.Membership
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (true; false)
open import Data.Maybe.Base using (just; nothing; is-just)
open import Data.Product as Prod using (_×_; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent renaming (Pointwise to _×ᴿ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _∘′_)
open import Level using (Level)

open import Relation.Binary using (Transitive; Symmetric; _Respectsˡ_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Intersection using (_∩_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (Reflects; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open StrictTotalOrder strictTotalOrder renaming (Carrier to Key) hiding (trans)
open Eq using (_≉_; refl; sym; trans)
open import Data.Tree.AVL strictTotalOrder using (tree)
open import Data.Tree.AVL.Indexed strictTotalOrder using (key)
import Data.Tree.AVL.Indexed.Relation.Unary.Any strictTotalOrder as IAny
import Data.Tree.AVL.Indexed.Relation.Unary.Any.Properties strictTotalOrder as IAnyₚ
open import Data.Tree.AVL.Key strictTotalOrder using (⊥⁺<[_]<⊤⁺)
open import Data.Tree.AVL.Map strictTotalOrder
open import Data.Tree.AVL.Map.Relation.Unary.Any strictTotalOrder as Mapₚ using (Any)
open import Data.Tree.AVL.Relation.Unary.Any strictTotalOrder as Any using (tree)

private
  variable
    v p q : Level
    V : Set v
    m : Map V
    k k′ : Key
    x x′ y y′ : V
    kx : Key × V

infix 4 _∈_

private
  Is : Rel (Key × V) _
  Is = _≈_ ×ᴿ _≡_

  Is-trans : Transitive (Is {V = V})
  Is-trans {i = i} {k = k} = ×-transitive Eq.trans ≡-trans {i = i} {k = k}

  Is-sym : Symmetric (Is {V = V})
  Is-sym {x = x} {y = y} = ×-symmetric sym ≡-sym {x} {y}

------------------------------------------------------------------------
-- Membership: ∈

_∈_ : Key × V → Map V → Set _
kx ∈ m = Any (Is kx) m

_∉_ : Key × V → Map V → Set _
kx ∉ m = ¬ kx ∈ m

∈-Respectsˡ : _∈_ {V = V} Respectsˡ Is
∈-Respectsˡ x~y = Any.map (Is-trans (Is-sym x~y))

∈-empty : kx ∉ empty
∈-empty (tree ())

------------------------------------------------------------------------
-- singleton

∈-singleton⁺ : (k , x) ∈ singleton k x
∈-singleton⁺ = tree (IAnyₚ.singleton⁺ _ _ (refl , ≡-refl))

∈-singleton⁻ : (k , x) ∈ singleton k′ x′ → k ≈ k′ × x ≡ x′
∈-singleton⁻ (tree p) = IAnyₚ.singleton⁻ _ _ p

private
  ≈-lookup : (p : (k , x) ∈ m) → k ≈ Any.lookupKey p
  ≈-lookup (tree p) = proj₁ (IAnyₚ.lookup-result p)

------------------------------------------------------------------------
-- insert

∈-insert⁺ : k ≉ k′ → (k , x) ∈ m → (k , x) ∈ insert k′ x′ m
∈-insert⁺ {k′ = k′} {m = m@(tree t)} k≉k′ (tree p) =
  tree (IAnyₚ.insert⁺ _ _ _ (⊥⁺<[ _ ]<⊤⁺) p k′≉key-p)
  where
  k′≉key-p : k′ ≉ Any.lookupKey (tree p)
  k′≉key-p k′≈key-p = k≉k′ (Eq.trans (≈-lookup (tree p)) (Eq.sym k′≈key-p))

∈-insert⁺⁺ : (k , x) ∈ insert k x m
∈-insert⁺⁺ {k = k} {m = tree t} with IAny.any? ((k ≟_) ∘ key) t
... | yes k∈ = tree (IAnyₚ.Any-insert-just _ _ _ _ (λ k′ → _, ≡-refl) k∈)
... | no ¬k∈ = tree (IAnyₚ.Any-insert-nothing _ _ _ _ (refl , ≡-refl) ¬k∈)

private
  Is-Resp : ∀ {kv k k′ v} → k ≈ k′ → Is {V = V} kv (k′ , v) → Is kv (k , v)
  Is-Resp = (λ{ k′≈l (k≈l , x≡) → (trans k≈l (sym k′≈l) , x≡)})

∈-insert⁻ : (k , x) ∈ insert k′ x′ m → (k ≈ k′ × x ≡ x′) ⊎ (k ≉ k′ × (k , x) ∈ m)
∈-insert⁻ {m = tree t} (tree kx∈insert)
    with IAnyₚ.insert⁻ Is-Resp _ _ t (⊥⁺<[ _ ]<⊤⁺) kx∈insert
... | inj₁ p = inj₁ p
... | inj₂ p = let k′≉p , k≈p , _ = IAnyₚ.lookup-result p
                   k≉k′ = λ k≈k′ → k′≉p (trans (sym k≈k′) k≈p)
               in inj₂ (k≉k′ , tree (IAny.map proj₂ p))

------------------------------------------------------------------------
-- lookup

∈-lookup⁺ : (k , x) ∈ m → lookup m k ≡ just x
∈-lookup⁺ {k = k} {m = tree t} (tree kx∈m)
    with IAnyₚ.lookup⁺ t k (⊥⁺<[ _ ]<⊤⁺) kx∈m | IAnyₚ.lookup-result kx∈m
... | inj₁ p≉k        | k≈p , x≡p = contradiction (sym k≈p) p≉k
... | inj₂ (p≈k , eq) | k≈p , x≡p = ≡-trans eq (cong just (≡-sym x≡p))

∈-lookup⁻ : lookup m k ≡ just x → (k , x) ∈ m
∈-lookup⁻ {m = tree t} {k = k} {x = x} eq
  = tree (IAny.map (Prod.map sym ≡-sym) (IAnyₚ.lookup⁻ t k x (⊥⁺<[ _ ]<⊤⁺) eq))

∈-lookup-nothing⁺ : (∀ x → (k , x) ∉ m) → lookup m k ≡ nothing
∈-lookup-nothing⁺ {k = k} {m = m@(tree t)} k∉m with lookup m k in eq
... | nothing = ≡-refl
... | just x = contradiction (∈-lookup⁻ eq) (k∉m x)

∈-lookup-nothing⁻ : lookup m k ≡ nothing → (k , x) ∉ m
∈-lookup-nothing⁻ eq kx∈m with ≡-trans (≡-sym eq) (∈-lookup⁺ kx∈m)
... | ()

------------------------------------------------------------------------
-- ∈?

∈-∈? : (k , x) ∈ m → (k ∈? m) ≡ true
∈-∈? = cong is-just ∘ ∈-lookup⁺

∉-∈? : (∀ x → (k , x) ∉ m) → (k ∈? m) ≡ false
∉-∈? = cong is-just ∘ ∈-lookup-nothing⁺

∈?-∈ : (k ∈? m) ≡ true → ∃[ x ] (k , x) ∈ m
∈?-∈ {k = k} {m = m} ≡true with lookup m k in eq
... | just x = x , ∈-lookup⁻ eq

∈?-∉ : (k ∈? m) ≡ false → ∀ x → (k , x) ∉ m
∈?-∉ {k = k} {m = m} ≡false x with lookup m k in eq
... | nothing = ∈-lookup-nothing⁻ eq

∈?-Reflects-∈ : Reflects (∃[ x ] (k , x) ∈ m) (k ∈? m)
∈?-Reflects-∈ {k = k} {m = m} with lookup m k in eq
... | just x = Reflects.ofʸ (x , ∈-lookup⁻ eq)
... | nothing = Reflects.ofⁿ (∈-lookup-nothing⁻ eq ∘ proj₂)
