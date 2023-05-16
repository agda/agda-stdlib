------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the membership relation for AVL Maps identifying values up to
-- propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Map.Membership.Propositional.Properties
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
open import Data.Tree.AVL.Map.Membership.Propositional strictTotalOrder
open import Data.Tree.AVL.Relation.Unary.Any strictTotalOrder as Any using (tree)

private
  variable
    v p q : Level
    V : Set v
    m : Map V
    k k′ : Key
    x x′ y y′ : V
    kx : Key × V

≈ₖᵥ-trans : Transitive (_≈ₖᵥ_ {V = V})
≈ₖᵥ-trans {i = i} {k = k} = ×-transitive Eq.trans ≡-trans {i = i} {k = k}

≈ₖᵥ-sym : Symmetric (_≈ₖᵥ_ {V = V})
≈ₖᵥ-sym {x = x} {y = y} = ×-symmetric sym ≡-sym {x} {y}

∈ₖᵥ-Respectsˡ : _∈ₖᵥ_ {V = V} Respectsˡ _≈ₖᵥ_
∈ₖᵥ-Respectsˡ x~y = Any.map (≈ₖᵥ-trans (≈ₖᵥ-sym x~y))

∈ₖᵥ-empty : kx ∉ₖᵥ empty
∈ₖᵥ-empty (tree ())

------------------------------------------------------------------------
-- singleton

∈ₖᵥ-singleton⁺ : (k , x) ∈ₖᵥ singleton k x
∈ₖᵥ-singleton⁺ = tree (IAnyₚ.singleton⁺ _ _ _ (refl , ≡-refl))

∈ₖᵥ-singleton⁻ : (k , x) ∈ₖᵥ singleton k′ x′ → k ≈ k′ × x ≡ x′
∈ₖᵥ-singleton⁻ (tree p) = IAnyₚ.singleton⁻ _ _ _ p

private
  ≈-lookup : (p : (k , x) ∈ₖᵥ m) → k ≈ Any.lookupKey p
  ≈-lookup (tree p) = proj₁ (IAnyₚ.lookup-result p)

------------------------------------------------------------------------
-- insert

∈ₖᵥ-insert⁺ : k ≉ k′ → (k , x) ∈ₖᵥ m → (k , x) ∈ₖᵥ insert k′ x′ m
∈ₖᵥ-insert⁺ {k′ = k′} {m = m@(tree t)} k≉k′ (tree p) =
  tree (IAnyₚ.insert⁺ _ _ _ (⊥⁺<[ _ ]<⊤⁺) p k′≉key-p)
  where
  k′≉key-p : k′ ≉ Any.lookupKey (tree p)
  k′≉key-p k′≈key-p = k≉k′ (Eq.trans (≈-lookup (tree p)) (Eq.sym k′≈key-p))

∈ₖᵥ-insert⁺⁺ : (k , x) ∈ₖᵥ insert k x m
∈ₖᵥ-insert⁺⁺ {k = k} {m = tree t} with IAny.any? ((k ≟_) ∘ key) t
... | yes k∈ = tree (IAnyₚ.Any-insert-just _ _ _ _ (λ k′ → _, ≡-refl) k∈)
... | no ¬k∈ = tree (IAnyₚ.Any-insert-nothing _ _ _ _ (refl , ≡-refl) ¬k∈)

private
  ≈ₖᵥ-Resp : k ≈ k′ → kx ≈ₖᵥ (k′ , x) → kx ≈ₖᵥ (k , x)
  ≈ₖᵥ-Resp = (λ{ k′≈l (k≈l , x≡) → (trans k≈l (sym k′≈l) , x≡)})

∈ₖᵥ-insert⁻ : (k , x) ∈ₖᵥ insert k′ x′ m → (k ≈ k′ × x ≡ x′) ⊎ (k ≉ k′ × (k , x) ∈ₖᵥ m)
∈ₖᵥ-insert⁻ {m = tree t} (tree kx∈insert)
    with IAnyₚ.insert⁻ ≈ₖᵥ-Resp _ _ t (⊥⁺<[ _ ]<⊤⁺) kx∈insert
... | inj₁ p = inj₁ p
... | inj₂ p = let k′≉p , k≈p , _ = IAnyₚ.lookup-result p
                   k≉k′ = λ k≈k′ → k′≉p (trans (sym k≈k′) k≈p)
               in inj₂ (k≉k′ , tree (IAny.map proj₂ p))

------------------------------------------------------------------------
-- lookup

∈ₖᵥ-lookup⁺ : (k , x) ∈ₖᵥ m → lookup m k ≡ just x
∈ₖᵥ-lookup⁺ {k = k} {m = tree t} (tree kx∈m)
    with IAnyₚ.lookup⁺ t k (⊥⁺<[ _ ]<⊤⁺) kx∈m | IAnyₚ.lookup-result kx∈m
... | inj₁ p≉k        | k≈p , x≡p = contradiction (sym k≈p) p≉k
... | inj₂ (p≈k , eq) | k≈p , x≡p = ≡-trans eq (cong just (≡-sym x≡p))

∈ₖᵥ-lookup⁻ : lookup m k ≡ just x → (k , x) ∈ₖᵥ m
∈ₖᵥ-lookup⁻ {m = tree t} {k = k} {x = x} eq
  = tree (IAny.map (Prod.map sym ≡-sym) (IAnyₚ.lookup⁻ t k x (⊥⁺<[ _ ]<⊤⁺) eq))

∈ₖᵥ-lookup-nothing⁺ : (∀ x → (k , x) ∉ₖᵥ m) → lookup m k ≡ nothing
∈ₖᵥ-lookup-nothing⁺ {k = k} {m = m@(tree t)} k∉m with lookup m k in eq
... | nothing = ≡-refl
... | just x = contradiction (∈ₖᵥ-lookup⁻ eq) (k∉m x)

∈ₖᵥ-lookup-nothing⁻ : lookup m k ≡ nothing → (k , x) ∉ₖᵥ m
∈ₖᵥ-lookup-nothing⁻ eq kx∈m with ≡-trans (≡-sym eq) (∈ₖᵥ-lookup⁺ kx∈m)
... | ()

------------------------------------------------------------------------
-- member

∈ₖᵥ-member : (k , x) ∈ₖᵥ m → member k m ≡ true
∈ₖᵥ-member = cong is-just ∘ ∈ₖᵥ-lookup⁺

∉ₖᵥ-member : (∀ x → (k , x) ∉ₖᵥ m) → member k m ≡ false
∉ₖᵥ-member = cong is-just ∘ ∈ₖᵥ-lookup-nothing⁺

member-∈ₖᵥ : member k m ≡ true → ∃[ x ] (k , x) ∈ₖᵥ m
member-∈ₖᵥ {k = k} {m = m} ≡true with lookup m k in eq
... | just x = x , ∈ₖᵥ-lookup⁻ eq

member-∉ₖᵥ : member k m ≡ false → ∀ x → (k , x) ∉ₖᵥ m
member-∉ₖᵥ {k = k} {m = m} ≡false x with lookup m k in eq
... | nothing = ∈ₖᵥ-lookup-nothing⁻ eq

member-Reflects-∈ₖᵥ : Reflects (∃[ x ] (k , x) ∈ₖᵥ m) (member k m)
member-Reflects-∈ₖᵥ {k = k} {m = m} with lookup m k in eq
... | just x = Reflects.ofʸ (x , ∈ₖᵥ-lookup⁻ eq)
... | nothing = Reflects.ofⁿ (∈ₖᵥ-lookup-nothing⁻ eq ∘ proj₂)
