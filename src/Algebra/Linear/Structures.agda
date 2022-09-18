------------------------------------------------------------------------
-- The Agda standard library
--
-- Some linear algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Structures where

open import Algebra using (CommutativeRing; Field; Op₂)
open import Algebra.Construct.NaturalChoice.Base using (MinOperator)
open import Algebra.Module               using (Module)
open import Algebra.Morphism.Definitions
  using (Homomorphic₂′; Homomorphic₂′′)
open import Data.List
open import Data.List.Properties         using (length-zipWith)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat.Properties
  using (⊓-operator; ≤-reflexive)
open import Data.Product                 hiding (map)
open import Function                     using (_∘_; id)
open import Level                        using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_)
open import Relation.Binary.Reasoning.MultiSetoid

import Data.List.Relation.Binary.Equality.Setoid as ListEq
import Data.Nat                                  as ℕ
import Function.Relation.Binary.Equality         as ExtEq

module PE = Eq.≡-Reasoning

module _
  {r ℓr m ℓm : Level}
  (fld       : Field r ℓr)
  (open Field fld renaming (Carrier to S))  -- "S" for scalar.
  (mod       : Module ring m ℓm)            -- `ring` comes from `fld`.
  where

  open ExtEq setoid
  open ListEq setoid using (_≋_; ≋-refl; ≋-setoid; ≋-sym)
    renaming ( _∷_  to _∷′_ )
  open Module mod renaming (Carrierᴹ to V)  -- "V" for vector.
  open import Algebra.Definitions _≈_
    using ( Congruent₂; Commutative ; RightIdentity; LeftIdentity
          ; RightZero ; LeftZero; _DistributesOverˡ_
          )
  open import Data.List.Properties.CommutativeRing ring

  -- A set of "vectors" forms a basis for a space iff:
  --   1. it _spans_ the space, and
  --   2. all vectors in the set are linearly independent.
  --
  -- Re: linear independence, from the Wikipedia article on vector spaces:
  -- "Also equivalently, they are linearly independent if a linear combination
  -- results in the zero vector if and only if all its coefficients are zero."
  --
  -- ToDo: List => Foldable Functor
  record IsBasis : Set (suc (ℓm ⊔ ℓr ⊔ r ⊔ m)) where

    -- Accumulate a list of vectors, scaled by a list of scalars.
    vacc : List S → List V → V
    vacc ss vs = foldr _+ᴹ_ 0ᴹ (zipWith (_*ₗ_) ss vs)

    field
      basisSet         : List V
      basisComplete    : ∀ {v : V} → ∃ (λ ss → vacc ss basisSet ≈ᴹ v)
      basisIndependent : (ss : List S) → vacc ss basisSet ≈ᴹ 0ᴹ →
                         All (_≈ 0#) ss

  -- From the Wikipedia article on vector spaces (`Modules` section):
  -- "For example, modules need not have bases, as the Z-module
  -- (that is, abelian group) Z/2Z shows; those modules that do
  -- (including all vector spaces) are known as free modules.
  -- Nevertheless, a vector space can be compactly defined as a module
  -- over a ring which is a field, with the elements being called vectors."
  --
  -- I've asserted two things in the following code, which I infer from
  -- the quote above:
  --   1. All vector spaces _must_ have a basis.
  --   2. I can use `Module` to represent a vector space, as long as the
  --      ring I pass it comes from a `Field`.
  --      (Note, above, that `ring` comes from `fld`.)
  --
  -- Note that, due to the two explicit parameters of the enclosing
  -- anonymous module, this definition would need to be invoked by client
  -- code as: `IsVectorSpace <Field> <Module> ...`, making the linkage
  -- to a particular `Field` and `Module` explicit.
  record IsVectorSpace : Set (suc (ℓm ⊔ ℓr ⊔ m ⊔ r)) where

    field
      basis : IsBasis

    open IsBasis basis public

    -- Scale a vector according to some reduction function.
    vscale : (V → S) → V → V
    vscale f = uncurry _*ₗ_ ∘ < f , id >

    -- Accumulate a list of vectors, according to some reduction function.
    vgen : (V → S) → List V → V
    vgen f = foldr (_+ᴹ_ ∘ vscale f) 0ᴹ

  -- An _Inner Product Space_ is a vector space augmented with a function
  -- that takes two vectors and returns a scalar.
  record IsInnerProductSpace (f : V → V → S) : Set (suc (ℓm ⊔ ℓr ⊔ m ⊔ r)) where

    field
      isVectorSpace : IsVectorSpace

    open IsVectorSpace isVectorSpace public

  -- I'm coining the term _Dot Product Space_ to imply an
  -- `IsInnerProductSpace` in which the inner product is the standard
  -- "dot product". This requires that the underlying `Module` be
  -- _Representable_ (i.e. - have an associated _indexing_ function).
  -- Here, we capture this constraint by requiring a homomorphic `toList` function.
  --
  -- Furthermore, I'm going to require that the basis of a `DotProductSpace`
  -- be orthonormal, because that seems the proper and usual thing to do.
  -- (It's not really a narrowing of the scope in any way, since a
  -- non-orthonormal basis can easily be converted to an orthonormal
  -- equivalent with the same span.)
  record IsDotProductSpace
    (toList : V → List S) : Set (suc (ℓm ⊔ ℓr ⊔ m ⊔ r)) where

    _∙_ : V → V → S
    _∙_ u v = foldr _+_ 0# (zipWith _*_ (toList u) (toList v))

    field
      isVectorSpace  : IsVectorSpace
      basisOrthonorm : ∀ {v : V} →
                       v ≈ᴹ IsVectorSpace.vgen isVectorSpace
                              (v ∙_)
                              (IsBasis.basisSet
                                 (IsVectorSpace.basis isVectorSpace)
                              )
      cardinality    : ℕ.ℕ
      toList-len     : ∀ {v} → length (toList v) ≡ cardinality
      toList-homo-+  : {u v : V} →
                       toList (u +ᴹ v) ≋ zipWith _+_ (toList u) (toList v)
      toList-homo‿-  : {v : V} →
                       toList (-ᴹ v) ≋ map -_ (toList v)
      toList-homo-*ₗ : {s : S} {v : V} →
                       toList (s *ₗ v) ≋ map (s *_) (toList v)
      toList-homo-*ᵣ : {s : S} {v : V} →
                       toList (v *ᵣ s) ≋ map (_* s) (toList v)
      toList-cong    : ∀ {u v} → u ≈ᴹ v → toList u ≋ toList v
      toList-zero    : toList 0ᴹ ≋ replicate cardinality 0#

    len[u]≡len[v] : ∀ {u v} → length (toList u) ≡ length (toList v)
    len[u]≡len[v] {u} {v} = PE.begin
      length (toList u) PE.≡⟨ toList-len ⟩
      cardinality       PE.≡⟨ Eq.sym toList-len ⟩
      length (toList v) PE.∎

    isInnerProductSpace : IsInnerProductSpace _∙_
    isInnerProductSpace = record {isVectorSpace = isVectorSpace}

    open IsInnerProductSpace isInnerProductSpace public

    --------------------------------------------------------------------
    -- Properties of the Dot Product

    ∙-comm : ∀ {u v} → u ∙ v ≈ v ∙ u
    ∙-comm {u} {v} = begin⟨ setoid ⟩
      u ∙ v                               ≡⟨⟩
      foldr _+_ 0# (zipWith _*_ (u′) (v′)) ≈⟨
        foldr-cong (zipWith _*_ (u′) (v′)) (zipWith _*_ (v′) (u′)) +-cong
        (zipWith-comm *-comm (u′) (v′))      ⟩
      foldr _+_ 0# (zipWith _*_ (v′) (u′)) ≡⟨⟩
      v ∙ u                               ∎
      where
      u′ = toList u
      v′ = toList v

    ∙-distrib-+ : {a b c : V} →
                  length (toList a) ≡ length (toList b) →
                  length (toList a) ≡ length (toList c) →
                  a ∙ (b +ᴹ c) ≈ (a ∙ b) + (a ∙ c)
    ∙-distrib-+ {a} {b} {c} |a|≡|b| |a|≡|c| = begin⟨ setoid ⟩
      a ∙ (b +ᴹ c)
        ≡⟨⟩
      foldr _+_ 0# (zipWith _*_ (a′) (toList (b +ᴹ c)))
        ≈⟨ foldr-cong (zipWith _*_ (a′) (toList (b +ᴹ c)))
                      (zipWith _*_ (a′) (b′ +ᴸ c′))
                      +-cong
                      (zipWith-congˡ *-cong toList-homo-+) ⟩
      foldr _+_ 0# (zipWith _*_ (a′) (b′ +ᴸ c′))
        ≈⟨ foldr-cong (zipWith _*_ (a′) (b′ +ᴸ c′))
                      (zipWith _*_ a′ b′ +ᴸ zipWith _*_ a′ c′)
                      +-cong
                      zipWith-*-distrib-+ᴸ ⟩
      foldr _+_ 0# (zipWith _*_ a′ b′ +ᴸ zipWith _*_ a′ c′)
        ≈⟨ foldr-+-distrib-+ᴸ {zipWith _*_ a′ b′} {zipWith _*_ a′ c′} |a*b|≡|a*c| ⟩
      foldr _+_ 0# (zipWith _*_ a′ b′) + foldr _+_ 0# (zipWith _*_ a′ c′)
        ≡⟨⟩
      (a ∙ b) + (a ∙ c)
        ∎
      where
      a′ = toList a
      b′ = toList b
      c′ = toList c
      a*b = zipWith _*_ a′ b′
      a*c = zipWith _*_ a′ c′
      open MinOperator ⊓-operator
      |a*b|≡|a*c| : length a*b ≡ length a*c
      |a*b|≡|a*c| = PE.begin
        length a*b                PE.≡⟨⟩
        length (zipWith _*_ a′ b′) PE.≡⟨ length-zipWith _*_ a′ b′ ⟩
        length a′ ℕ.⊓ length b′    PE.≡⟨ x≤y⇒x⊓y≈x (≤-reflexive |a|≡|b|) ⟩
        length a′                  PE.≡⟨ Eq.sym (x≤y⇒x⊓y≈x (≤-reflexive |a|≡|c|)) ⟩
        length a′ ℕ.⊓ length c′    PE.≡⟨ Eq.sym (length-zipWith _*_ a′ c′) ⟩
        length (zipWith _*_ a′ c′) PE.≡⟨⟩
        length a*c                PE.∎

    ∙-comm-*ₗ : ∀ {s a b} → a ∙ (s *ₗ b) ≈ s * (a ∙ b)
    ∙-comm-*ₗ {s} {a} {b} = begin⟨ setoid ⟩
      a ∙ (s *ₗ b)
        ≡⟨⟩
      foldr _+_ 0# (zipWith _*_ a′ (toList (s *ₗ b)))
        ≈⟨ foldr-cong (zipWith _*_ a′ (toList (s *ₗ b)))
                      (zipWith _*_ a′ (map (s *_) b′))
                      +-cong
                      (zipWith-congˡ *-cong toList-homo-*ₗ) ⟩
      foldr _+_ 0# (zipWith _*_ a′ (map (s *_) b′))
        ≈⟨ foldr-cong (zipWith _*_ a′ (map (s *_) b′))
                      (map (s *_) (a*b))
                      +-cong
                      (zipWith-comm-map′ *-homo) ⟩
      foldr _+_ 0# (map (s *_) (a*b))
        ≈⟨ sym (distrib-foldr {xs = a*b} +-identityʳ zeroʳ +-cong distribˡ) ⟩
      s * foldr _+_ 0# (a*b)
        ≈⟨ *-cong refl refl ⟩
      s * (a ∙ b)
        ∎
      where
      a′ = toList a
      b′ = toList b
      a*b = zipWith _*_ a′ b′
      *-homo : Homomorphic₂′′ S S _≈_ _*_ (s *_)
      *-homo x y = begin⟨ setoid ⟩
        x * (s * y) ≈⟨ *-comm x (s * y) ⟩
        (s * y) * x ≈⟨ *-assoc s y x ⟩
        s * (y * x) ≈⟨ *-cong refl (*-comm y x) ⟩
        s * (x * y) ∎


    ∙-comm-*ᵣ : ∀ {s a b} → a ∙ (b *ᵣ s) ≈ (a ∙ b) * s
    ∙-comm-*ᵣ {s} {a} {b} = begin⟨ setoid ⟩
      a ∙ (b *ᵣ s)
        ≡⟨⟩
      foldr _+_ 0# (zipWith _*_ a′ (toList (b *ᵣ s)))
        ≈⟨ foldr-cong (zipWith _*_ a′ (toList (b *ᵣ s)))
                      (zipWith _*_ a′ (map (_* s) b′))
                      +-cong
                      (zipWith-congˡ *-cong toList-homo-*ᵣ) ⟩
      foldr _+_ 0# (zipWith _*_ a′ (map (_* s) b′))
        ≈⟨ foldr-cong (zipWith _*_ a′ (map (_* s) b′))
                      (map (_* s) (a*b))
                      +-cong
                      (zipWith-comm-map′ *-homo) ⟩
      foldr _+_ 0# (map (_* s) (a*b))
        ≈⟨ sym (distrib-foldr {xs = a*b} +-identityʳ zeroˡ +-cong distribʳ) ⟩
      foldr _+_ 0# (a*b) * s
        ≈⟨ *-cong refl refl ⟩
      (a ∙ b) * s
        ∎
      where
      a′ = toList a
      b′ = toList b
      a*b = zipWith _*_ a′ b′
      *-homo : Homomorphic₂′′ S S _≈_ _*_ (_* s)
      *-homo x y = sym (*-assoc x y s)

    ∙-congˡ : ∀ {a b c} → b ≈ᴹ c → a ∙ b ≈ a ∙ c
    ∙-congˡ {a} {b} {c} b≈c = begin⟨ setoid ⟩
      a ∙ b
        ≡⟨⟩
      foldr _+_ 0# (zipWith _*_ a′ b′)
        ≈⟨ foldr-cong a*b a*c +-cong (zipWith-congˡ *-cong (toList-cong b≈c)) ⟩
      foldr _+_ 0# (zipWith _*_ a′ c′)
        ≡⟨⟩
      a ∙ c
        ∎
      where
      a′ = toList a
      b′ = toList b
      c′ = toList c
      a*b = zipWith _*_ a′ b′
      a*c = zipWith _*_ a′ c′

    ∙-congʳ : ∀ {a b c} → b ≈ᴹ c → b ∙ a ≈ c ∙ a
    ∙-congʳ {a} {b} {c} b≈c = begin⟨ setoid ⟩
      b ∙ a ≈⟨ ∙-comm ⟩
      a ∙ b ≈⟨ ∙-congˡ b≈c ⟩
      a ∙ c ≈⟨ ∙-comm ⟩
      c ∙ a ∎

    ∙-idˡ : ∀ {a} → 0ᴹ ∙ a ≈ 0#
    ∙-idˡ {a} = begin⟨ setoid ⟩
      0ᴹ ∙ a
        ≡⟨⟩
      foldr _+_ 0# (zipWith _*_ (toList 0ᴹ) (toList a))
        ≈⟨ foldr-cong (zipWith _*_ (toList 0ᴹ) (toList a))
                      (zipWith _*_ (replicate cardinality 0#) a′)
                      +-cong
                      (zipWith-congʳ *-cong toList-zero) ⟩
      foldr _+_ 0# (zipWith _*_ (replicate cardinality 0#) a′)
        ≈⟨ foldr-cong (zipWith _*_ (replicate cardinality 0#) a′)
                      (replicate (cardinality ℕ.⊓ len[a]) 0#)
                      +-cong
                      (zipWith-zero zeroˡ a′) ⟩
      foldr _+_ 0# (replicate (cardinality ℕ.⊓ len[a]) 0#)
        ≈⟨ foldr-id {_+_} {n = (cardinality ℕ.⊓ len[a])} +-identityˡ ⟩
      0#
        ∎
      where
      a′     = toList a
      len[a] = length a′

    ∙-idʳ : ∀ {a} → a ∙ 0ᴹ ≈ 0#
    ∙-idʳ {a} = begin⟨ setoid ⟩
      a ∙ 0ᴹ ≈⟨ ∙-comm ⟩
      0ᴹ ∙ a ≈⟨ ∙-idˡ ⟩
      0#     ∎

    ∙-homo-⁻¹ : ∀ {a b} → a ∙ (-ᴹ b) ≈ - (a ∙ b)
    ∙-homo-⁻¹ {a} {b} = begin⟨ setoid ⟩
      a ∙ (-ᴹ b)
        ≡⟨⟩
      foldr _+_ 0# (zipWith _*_ (toList a) (toList (-ᴹ b)))
        ≈⟨ foldr-cong (zipWith _*_ (toList a) (toList (-ᴹ b)))
                      (zipWith _*_ a′ (map -_ b′))
                      +-cong
                      (zipWith-congˡ *-cong toList-homo‿-) ⟩
      foldr _+_ 0# (zipWith _*_ a′ (map -_ b′))
        ≈⟨ foldr-cong (zipWith _*_ a′ (map -_ b′))
                      (map -_ a*b)
                      +-cong
                      zipWith-*-homo‿- ⟩
      foldr _+_ 0# (map -_ a*b)
        ≈⟨ foldr-homo‿- {a*b} ⟩
      - (foldr _+_ 0# a*b)
        ≡⟨⟩
      - (a ∙ b)
        ∎
      where
      a′  = toList a
      b′  = toList b
      a*b = zipWith _*_ a′ b′
