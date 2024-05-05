------------------------------------------------------------------------
-- The Agda standard library
--
-- Boolean algebra expressions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Lattice using (BooleanAlgebra; isBooleanAlgebraʳ;
  isDistributiveLatticeʳʲᵐ)

module Algebra.Lattice.Properties.BooleanAlgebra.Expression
  {b} (B : BooleanAlgebra b b)
  where

open BooleanAlgebra B

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Effectful as Vec
import Function.Identity.Effectful as Identity
open import Data.Vec.Properties using (lookup-map)
open import Data.Vec.Relation.Binary.Pointwise.Extensional as PW
  using (Pointwise; ext)
open import Effect.Applicative as Applicative
open import Function.Base using (_∘_; _$_; flip)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≗_)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
import Relation.Binary.Reflection as Reflection

-- Expressions made up of variables and the operations of a boolean
-- algebra.

infixr 7 _and_
infixr 6 _or_

data Expr n : Set b where
  var        : (x : Fin n) → Expr n
  _or_ _and_ : (e₁ e₂ : Expr n) → Expr n
  not        : (e : Expr n) → Expr n
  top bot    : Expr n

-- The semantics of an expression, parametrised by an applicative
-- functor.

module Semantics
  {F : Set b → Set b}
  (A : RawApplicative F)
  where

  open RawApplicative A

  ⟦_⟧ : ∀ {n} → Expr n → Vec (F Carrier) n → F Carrier
  ⟦ var x     ⟧ ρ = Vec.lookup ρ x
  ⟦ e₁ or e₂  ⟧ ρ = _∨_ <$> ⟦ e₁ ⟧ ρ ⊛ ⟦ e₂ ⟧ ρ
  ⟦ e₁ and e₂ ⟧ ρ = _∧_ <$> ⟦ e₁ ⟧ ρ ⊛ ⟦ e₂ ⟧ ρ
  ⟦ not e     ⟧ ρ = ¬_ <$> ⟦ e ⟧ ρ
  ⟦ top       ⟧ ρ = pure ⊤
  ⟦ bot       ⟧ ρ = pure ⊥

-- flip Semantics.⟦_⟧ e is natural.

module Naturality
  {F₁ F₂ : Set b → Set b}
  {A₁ : RawApplicative F₁}
  {A₂ : RawApplicative F₂}
  (f : Applicative.Morphism A₁ A₂)
  where

  open ≡-Reasoning
  open Applicative.Morphism f
  open Semantics A₁ renaming (⟦_⟧ to ⟦_⟧₁)
  open Semantics A₂ renaming (⟦_⟧ to ⟦_⟧₂)
  open RawApplicative A₁ renaming (pure to pure₁; _<$>_ to _<$>₁_; _⊛_ to _⊛₁_)
  open RawApplicative A₂ renaming (pure to pure₂; _<$>_ to _<$>₂_; _⊛_ to _⊛₂_)

  natural : ∀ {n} (e : Expr n) → op ∘ ⟦ e ⟧₁ ≗ ⟦ e ⟧₂ ∘ Vec.map op
  natural (var x) ρ = begin
    op (Vec.lookup ρ x)                                            ≡⟨ ≡.sym $ lookup-map x op ρ ⟩
    Vec.lookup (Vec.map op ρ) x                                    ∎
  natural (e₁ or e₂) ρ = begin
    op (_∨_ <$>₁ ⟦ e₁ ⟧₁ ρ ⊛₁ ⟦ e₂ ⟧₁ ρ)                       ≡⟨ op-⊛ _ _ ⟩
    op (_∨_ <$>₁ ⟦ e₁ ⟧₁ ρ) ⊛₂ op (⟦ e₂ ⟧₁ ρ)                  ≡⟨ ≡.cong₂ _⊛₂_ (op-<$> _ _) ≡.refl ⟩
    _∨_ <$>₂ op (⟦ e₁ ⟧₁ ρ) ⊛₂ op (⟦ e₂ ⟧₁ ρ)                  ≡⟨ ≡.cong₂ (λ e₁ e₂ → _∨_ <$>₂ e₁ ⊛₂ e₂) (natural e₁ ρ) (natural e₂ ρ) ⟩
    _∨_ <$>₂ ⟦ e₁ ⟧₂ (Vec.map op ρ) ⊛₂ ⟦ e₂ ⟧₂ (Vec.map op ρ)  ∎
  natural (e₁ and e₂) ρ = begin
    op (_∧_ <$>₁ ⟦ e₁ ⟧₁ ρ ⊛₁ ⟦ e₂ ⟧₁ ρ)                       ≡⟨ op-⊛ _ _ ⟩
    op (_∧_ <$>₁ ⟦ e₁ ⟧₁ ρ) ⊛₂ op (⟦ e₂ ⟧₁ ρ)                  ≡⟨ ≡.cong₂ _⊛₂_ (op-<$> _ _) ≡.refl ⟩
    _∧_ <$>₂ op (⟦ e₁ ⟧₁ ρ) ⊛₂ op (⟦ e₂ ⟧₁ ρ)                  ≡⟨ ≡.cong₂ (λ e₁ e₂ → _∧_ <$>₂ e₁ ⊛₂ e₂) (natural e₁ ρ) (natural e₂ ρ) ⟩
    _∧_ <$>₂ ⟦ e₁ ⟧₂ (Vec.map op ρ) ⊛₂ ⟦ e₂ ⟧₂ (Vec.map op ρ)  ∎
  natural (not e) ρ = begin
    op (¬_ <$>₁ ⟦ e ⟧₁ ρ)                                      ≡⟨ op-<$> _ _ ⟩
    ¬_ <$>₂ op (⟦ e ⟧₁ ρ)                                      ≡⟨ ≡.cong (¬_ <$>₂_) (natural e ρ) ⟩
    ¬_ <$>₂ ⟦ e ⟧₂ (Vec.map op ρ)                              ∎
  natural top ρ = begin
    op (pure₁ ⊤)                                                   ≡⟨ op-pure _ ⟩
    pure₂ ⊤                                                        ∎
  natural bot ρ = begin
    op (pure₁ ⊥)                                                   ≡⟨ op-pure _ ⟩
    pure₂ ⊥                                                        ∎

-- An example of how naturality can be used: Any boolean algebra can
-- be lifted, in a pointwise manner, to vectors of carrier elements.

lift : ℕ → BooleanAlgebra b b
lift n = record
  { Carrier          = Vec Carrier n
  ; _≈_              = Pointwise _≈_
  ; _∨_              = zipWith _∨_
  ; _∧_              = zipWith _∧_
  ; ¬_               = map ¬_
  ; ⊤                = pure ⊤
  ; ⊥                = pure ⊥
  ; isBooleanAlgebra = isBooleanAlgebraʳ $ record
    { isDistributiveLattice = isDistributiveLatticeʳʲᵐ $ record
      { isLattice = record
        { isEquivalence = PW.isEquivalence isEquivalence
        ; ∨-comm        = λ xs ys → ext λ i →
                            solve i 2 (λ x y → x or y , y or x)
                                  (∨-comm _ _) xs ys
        ; ∨-assoc       = λ xs ys _ → ext λ i →
                            solve i 3
                              (λ x y z → (x or y) or z , x or (y or z))
                              (∨-assoc _ _ _) xs ys _
        ; ∨-cong        = λ {xs} {ys} {us} {vs} xs≈us ys≈vs → ext λ i →
                            solve₁ i 4 (λ x y u v → x or y , u or v)
                                   xs us ys vs
                                   (∨-cong (Pointwise.app xs≈us i)
                                           (Pointwise.app ys≈vs i))
        ; ∧-comm        = λ xs ys → ext λ i →
                            solve i 2 (λ x y → x and y , y and x)
                                  (∧-comm _ _) xs ys
        ; ∧-assoc       = λ xs ys _ → ext λ i →
                            solve i 3
                              (λ x y z → (x and y) and z ,
                                         x and (y and z))
                              (∧-assoc _ _ _) xs ys _
        ; ∧-cong        = λ {xs} {ys} {us} {vs} xs≈ys us≈vs → ext λ i →
                            solve₁ i 4 (λ x y u v → x and y , u and v)
                                   xs us ys vs
                                   (∧-cong (Pointwise.app xs≈ys i)
                                           (Pointwise.app us≈vs i))
        ; absorptive    =
          (λ xs ys → ext λ i →
            solve i 2 (λ x y → x or (x and y) , x) (∨-absorbs-∧ _ _) xs ys) ,
          (λ xs ys → ext λ i →
            solve i 2 (λ x y → x and (x or y) , x) (∧-absorbs-∨ _ _) xs ys)
        }
      ; ∨-distribʳ-∧ = λ xs ys zs → ext λ i →
                         solve i 3
                               (λ x y z → (y and z) or x ,
                                          (y or x) and (z or x))
                               (∨-distribʳ-∧ _ _ _) xs ys zs
      }
    ; ∨-complementʳ = λ xs → ext λ i →
                        solve i 1 (λ x → x or (not x) , top)
                              (∨-complementʳ _) xs
    ; ∧-complementʳ = λ xs → ext λ i →
                        solve i 1 (λ x → x and (not x) , bot)
                              (∧-complementʳ _) xs
    ; ¬-cong        = λ {xs} {ys} xs≈ys → ext λ i →
                        solve₁ i 2 (λ x y → not x , not y) xs ys
                               (¬-cong (Pointwise.app xs≈ys i))
    }
  }
  where
  open RawApplicative Vec.applicative
    using (pure; zipWith) renaming (_<$>_ to map)

  ⟦_⟧Id : ∀ {n} → Expr n → Vec Carrier n → Carrier
  ⟦_⟧Id = Semantics.⟦_⟧ Identity.applicative

  ⟦_⟧Vec : ∀ {m n} → Expr n → Vec (Vec Carrier m) n → Vec Carrier m
  ⟦_⟧Vec = Semantics.⟦_⟧ Vec.applicative

  open module R {n} (i : Fin n) =
    Reflection setoid var
      (λ e ρ → Vec.lookup (⟦ e ⟧Vec ρ) i)
      (λ e ρ → ⟦ e ⟧Id (Vec.map (flip Vec.lookup i) ρ))
      (λ e ρ → sym $ reflexive $
                 Naturality.natural (Vec.lookup-morphism i) e ρ)
