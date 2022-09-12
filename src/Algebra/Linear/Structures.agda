------------------------------------------------------------------------
-- The Agda standard library
--
-- Some linear algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Structures where

open import Algebra using (CommutativeRing; Field; Op₁; Op₂; Group; Ring)
open import Algebra.Construct.NaturalChoice.Base using (MinOperator)
open import Algebra.Module                      using (Module)
open import Algebra.Morphism.Definitions
  using (Homomorphic₂′; Homomorphic₂′′)
open import Algebra.Structures                  using (IsField)
open import Data.List
open import Data.List.Properties
  using (length-++; length-zipWith)
open import Data.List.Relation.Unary.All        using (All)
open import Data.List.Relation.Binary.Pointwise using ()
  renaming (head to head′; tail to tail′)
open import Data.Nat.Properties
  using (suc-injective; ⊓-operator; ≤-reflexive)
open import Data.Product                        hiding (map)
open import Function                            hiding (_∘_)
-- open import Function.Equality                   using (≡-setoid)
open import Level                               using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_)
-- open Eq.≡-Reasoning using ()
--   renaming
--   ( begin_ to beginᴾ_
--   ; _≡⟨⟩_ to _≡⟨⟩ᴾ_
--   ; step-≡ to step-≡ᴾ
--   ; _∎ to _∎ᴾ
--   )
open import Relation.Binary.Reasoning.MultiSetoid

import Algebra.Properties.Group                  as PropGroup
import Algebra.Properties.Ring                   as PropRing
import Data.List.Relation.Binary.Equality.Setoid as ListEq
import Data.Nat                                  as ℕ
import Function.Relation.Binary.Equality         as ExtEq

-- syntax step-≡ᴾ x y≡z x≡y = x ≡ᴾ⟨  x≡y ⟩ y≡z
module PE = Eq.≡-Reasoning

module _
  {r ℓr m ℓm : Level}
  (fld       : Field r ℓr)
  (open Field fld renaming (Carrier to S))  -- "S" for scalar.
  (mod       : Module ring m ℓm)            -- `ring` comes from `fld`.
  where
  
  open Module mod renaming (Carrierᴹ to V)  -- "V" for vector.
  open ExtEq setoid
  open import Algebra.Definitions _≈_
    using ( Congruent₂; Commutative ; RightIdentity; LeftIdentity
          ; RightZero ; LeftZero; _DistributesOverˡ_
          )

  group : Group _ _
  group = record { isGroup = +-isGroup }

  ring′ : Ring _ _
  ring′ = record { isRing = isRing }

  open PropGroup group
  open PropRing  ring′
  
  -- Accumulate a list of vectors, scaled by a list of scalars.
  vacc : List S → List V → V
  vacc ss vs = foldr _+ᴹ_ 0ᴹ (zipWith (_*ₗ_) ss vs)

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
  record IsDotProductSpace (toList : V → List S) : Set (suc (ℓm ⊔ ℓr ⊔ m ⊔ r)) where

    open ListEq setoid using (_≋_; ≋-refl; ≋-setoid; ≋-sym)
      renaming ( _∷_  to _∷′_
               )
    
    field
      isVectorSpace  : IsVectorSpace
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
      
    _∙_ : V → V → S
    _∙_ u v = foldr _+_ 0# (zipWith _*_ (toList u) (toList v))

    isInnerProductSpace : IsInnerProductSpace _∙_
    isInnerProductSpace = record {isVectorSpace = isVectorSpace}
    
    open IsInnerProductSpace isInnerProductSpace public

    -- List properties over a `CommutativeRing` under equivalence
    -- ToDo: Move to: `Data.List.Properties.Setoid.

    _+ᴸ_ : List S → List S → List S
    _+ᴸ_ xs ys = zipWith _+_ xs ys

    length-suc : {xs : List S} {x : S} → length (x ∷ xs) ≡ ℕ.suc (length xs)
    length-suc {[]}     = Eq.refl
    length-suc {x ∷ xs} = Eq.refl
    
    length-∷-suc : {xs ys : List S} {x y : S} →
                   length xs ≡ length ys → length (x ∷ xs) ≡ length (y ∷ ys)
    length-∷-suc {[]}     {[]}     |xs|≡|ys| = Eq.refl
    length-∷-suc {x ∷ xs} {y ∷ ys} |xs|≡|ys| = Eq.cong ℕ.suc |xs|≡|ys|
    
    --------------------------------------------------------------------
    -- Zeros

    zipWith-zero : {_∘_ : Op₂ S} {ϵ : S} → {n : ℕ.ℕ} →
                   LeftZero ϵ _∘_ → (xs : List S) →
                   zipWith _∘_ (replicate n ϵ) xs ≋
                     replicate (n ℕ.⊓ length xs) ϵ
    zipWith-zero {_∘_} {ϵ} {ℕ.zero}  zero []       = ≋-refl
    zipWith-zero {_∘_} {ϵ} {ℕ.zero}  zero (x ∷ xs) = ≋-refl
    zipWith-zero {_∘_} {ϵ} {ℕ.suc n} zero []       = ≋-refl
    zipWith-zero {_∘_} {ϵ} {ℕ.suc n} zero (x ∷ xs) =
      (zero x) ∷′ (zipWith-zero zero xs)

    --------------------------------------------------------------------
    -- Identities

    foldr-id : {_∘_ : Op₂ S} {x ϵ : S} {n : ℕ.ℕ} → LeftIdentity ϵ _∘_ →
               foldr _∘_ x (replicate n ϵ) ≈ x
    foldr-id               {n = ℕ.zero}  id = refl
    foldr-id {_∘_} {x} {ϵ} {n = ℕ.suc n} id = begin⟨ setoid ⟩
      (ϵ ∘ foldr _∘_ x (replicate n ϵ)) ≈⟨ id (foldr _∘_ x (replicate n ϵ)) ⟩
      foldr _∘_ x (replicate n ϵ)       ≈⟨ foldr-id {_∘_} {n = n} id ⟩
      x                                 ∎
    
    --------------------------------------------------------------------
    -- Congruences
    
    foldr-cong : ∀ {f : Op₂ S} {x : S} (xs ys : List S) → Congruent₂ f →
                 xs ≋ ys → foldr f x xs ≈ foldr f x ys
    foldr-cong []       []       f-cong xs≈ys = refl
    foldr-cong (x ∷ xs) (y ∷ ys) f-cong xs≈ys =
      f-cong (head′ xs≈ys) (foldr-cong xs ys f-cong (tail′ xs≈ys))

    zipWith-congˡ : {xs ys zs : List S} {∘ : Op₂ S} → Congruent₂ ∘ →
                   ys ≋ zs → (zipWith ∘ xs ys) ≋ (zipWith ∘ xs zs)
    zipWith-congˡ {[]}     {[]}          {[]}     ∘-cong ys≋zs = ≋-refl
    zipWith-congˡ {[]}     {y ∷ []}      {z ∷ zs} ∘-cong ys≋zs = ≋-refl
    zipWith-congˡ {[]}     {y ∷ y₁ ∷ ys} {z ∷ zs} ∘-cong ys≋zs = ≋-refl
    zipWith-congˡ {x ∷ xs} {[]}          {[]}     ∘-cong ys≋zs = ≋-refl
    zipWith-congˡ {x ∷ xs} {y ∷ ys}      {z ∷ zs} ∘-cong ys≋zs =
      (∘-cong refl (head′ ys≋zs)) ∷′ zipWith-congˡ ∘-cong (tail′ ys≋zs)

    zipWith-congʳ : {xs ys zs : List S} {∘ : Op₂ S} → Congruent₂ ∘ →
                   xs ≋ ys → (zipWith ∘ xs zs) ≋ (zipWith ∘ ys zs)
    zipWith-congʳ {[]}     {[]}      {[]}     ∘-cong xs≋ys = ≋-refl
    zipWith-congʳ {[]}     {[]}      {z ∷ zs} ∘-cong xs≋ys = ≋-refl
    zipWith-congʳ {x ∷ xs} {y ∷ ys}  {[]}     ∘-cong xs≋ys = ≋-refl
    zipWith-congʳ {x ∷ xs} {y ∷ ys}  {z ∷ zs} ∘-cong xs≋ys =
      ∘-cong (head′ xs≋ys) refl ∷′ zipWith-congʳ ∘-cong (tail′ xs≋ys)

    --------------------------------------------------------------------
    -- Commutativities
    
    zipWith-comm : {f : Op₂ S} → Commutative f → (xs ys : List S) →
                   zipWith f xs ys ≋ zipWith f ys xs
    zipWith-comm f-comm []       []       = ≋-refl
    zipWith-comm f-comm []       (y ∷ ys) = ≋-refl
    zipWith-comm f-comm (x ∷ xs) []       = ≋-refl
    zipWith-comm f-comm (x ∷ xs) (y ∷ ys) =
      (f-comm x y) ∷′ (zipWith-comm f-comm xs ys)

    zipWith-comm-map : {f : Op₂ S} {g : Op₁ S} {xs ys : List S} →
                       Homomorphic₂′ S S _≈_ f g →
                       zipWith f (map g xs) ys ≋ map g (zipWith f xs ys)
    zipWith-comm-map {f} {g} {[]}     {[]}     _        = ≋-refl
    zipWith-comm-map {f} {g} {[]}     {y ∷ ys} _        = ≋-refl
    zipWith-comm-map {f} {g} {x ∷ xs} {[]}     _        = ≋-refl
    zipWith-comm-map {f} {g} {x ∷ xs} {y ∷ ys} f-homo-g =
      f-homo-g x y ∷′ zipWith-comm-map f-homo-g
                       
    zipWith-comm-map′ : {f : Op₂ S} {g : Op₁ S} {xs ys : List S} →
                       Homomorphic₂′′ S S _≈_ f g →
                       zipWith f xs (map g ys) ≋ map g (zipWith f xs ys)
    zipWith-comm-map′ {f} {g} {[]}     {[]}     _        = ≋-refl
    zipWith-comm-map′ {f} {g} {[]}     {y ∷ ys} _        = ≋-refl
    zipWith-comm-map′ {f} {g} {x ∷ xs} {[]}     _        = ≋-refl
    zipWith-comm-map′ {f} {g} {x ∷ xs} {y ∷ ys} f-homo-g =
      f-homo-g x y ∷′ zipWith-comm-map′ f-homo-g
      
    --------------------------------------------------------------------
    -- Distributivities
    
    ∷-distrib-+ : {x y : S} {xs ys : List S} →
                  x + y ∷ xs +ᴸ ys ≋ (x ∷ xs) +ᴸ (y ∷ ys)
    ∷-distrib-+ {x} {y} {[]} {[]}          = ≋-refl
    ∷-distrib-+ {x} {y} {[]} {y₁ ∷ ys}     = ≋-refl
    ∷-distrib-+ {x} {y} {x₁ ∷ xs} {[]}     = ≋-refl
    ∷-distrib-+ {x} {y} {x₁ ∷ xs} {y₁ ∷ ys} = refl ∷′ ≋-sym ∷-distrib-+
    
    zipWith-*-distrib-+ᴸ : {xs ys zs : List S} →
                           zipWith _*_ xs (ys +ᴸ zs) ≋ zipWith _*_ xs ys
                                                     +ᴸ zipWith _*_ xs zs
    zipWith-*-distrib-+ᴸ {[]} {[]} {[]}             = ≋-refl
    zipWith-*-distrib-+ᴸ {[]} {[]} {z ∷ []}         = ≋-refl
    zipWith-*-distrib-+ᴸ {[]} {[]} {z ∷ z₁ ∷ zs}     = ≋-refl
    zipWith-*-distrib-+ᴸ {[]} {y ∷ ys} {[]}         = ≋-refl
    zipWith-*-distrib-+ᴸ {[]} {y ∷ ys} {z ∷ zs}     = ≋-refl
    zipWith-*-distrib-+ᴸ {x ∷ xs} {[]} {[]}         = ≋-refl
    zipWith-*-distrib-+ᴸ {x ∷ xs} {[]} {z ∷ zs}     = ≋-refl
    zipWith-*-distrib-+ᴸ {x ∷ xs} {y ∷ ys} {[]}     = ≋-refl
    zipWith-*-distrib-+ᴸ {x ∷ xs} {y ∷ ys} {z ∷ zs} = begin⟨ ≋-setoid ⟩
      x * (y + z) ∷ zipWith _*_ xs (zipWith _+_ ys zs)           ≈⟨
        (refl ∷′ zipWith-*-distrib-+ᴸ)                              ⟩
      x * (y + z) ∷ zipWith _*_ xs ys +ᴸ zipWith _*_ xs zs       ≈⟨
        ((distribˡ x y z) ∷′ ≋-refl)                                ⟩
      (x * y) + (x * z) ∷ zipWith _*_ xs ys +ᴸ zipWith _*_ xs zs ≈⟨ ∷-distrib-+ ⟩
      (x * y ∷ zipWith _*_ xs ys) +ᴸ (x * z ∷ zipWith _*_ xs zs) ∎

    foldr-+-distrib-+ᴸ : {xs ys : List S} → length xs ≡ length ys →
                         foldr _+_ 0# (xs +ᴸ ys) ≈ (foldr _+_ 0# xs)
                                                 + (foldr _+_ 0# ys)
    foldr-+-distrib-+ᴸ {[]}     {[]}     _ = sym (+-identityˡ 0#)
    foldr-+-distrib-+ᴸ {x ∷ xs} {y ∷ ys} |xs|≡|ys| = begin⟨ setoid ⟩
      x + y + foldr _+_ 0# (xs +ᴸ ys)
        ≈⟨ +-assoc x y (foldr _+_ 0# (xs +ᴸ ys)) ⟩
      x + (y + foldr _+_ 0# (xs +ᴸ ys))
        ≈⟨ +-cong refl (+-comm y (foldr _+_ 0# (xs +ᴸ ys))) ⟩
      x + (foldr _+_ 0# (xs +ᴸ ys) + y)
        ≈⟨ +-cong refl (+-cong (foldr-+-distrib-+ᴸ
                                  {xs} {ys} (suc-injective |xs|≡|ys|)) refl) ⟩
      x + (foldr _+_ 0# xs + foldr _+_ 0# ys + y)
        ≈⟨ +-cong refl (+-assoc (foldr _+_ 0# xs) (foldr _+_ 0# ys) y) ⟩
      x + (foldr _+_ 0# xs + (foldr _+_ 0# ys + y))
        ≈⟨ +-cong refl (+-cong refl (+-comm (foldr _+_ 0# ys) y)) ⟩
      x + (foldr _+_ 0# xs + (y + foldr _+_ 0# ys))
        ≈⟨ sym (+-assoc x (foldr _+_ 0# xs) ((y + foldr _+_ 0# ys))) ⟩
      x + foldr _+_ 0# xs + (y + foldr _+_ 0# ys)
        ∎

    distrib-foldr : ∀ {ϵ y : S} {xs : List S} {_∙_ _∘_ : Op₂ S} →
                    RightIdentity ϵ _∘_       →
                    RightZero     ϵ _∙_       →
                    Congruent₂    _∘_         →
                     _∙_ DistributesOverˡ _∘_ →
                    y ∙ (foldr _∘_ ϵ xs) ≈ foldr _∘_ ϵ (map (y ∙_) xs)
    distrib-foldr {ϵ} {y} {[]}     {_∙_} {_∘_} _ zero _ _ = zero y
    distrib-foldr {ϵ} {y} {x ∷ xs} {_∙_} {_∘_} id zero cong distrib =
      begin⟨ setoid ⟩
        (y ∙ (x ∘ foldr _∘_ ϵ xs))
      ≈⟨ distrib y x (foldr _∘_ ϵ xs) ⟩
        (y ∙ x) ∘ (y ∙ foldr _∘_ ϵ xs)
      ≈⟨ cong refl (distrib-foldr {y = y} {xs = xs} id (λ x → zero y)
                                  cong (λ x → distrib y)) ⟩
        (y ∙ x) ∘ foldr _∘_ ϵ (map (_∙_ y) xs)
      ∎
    
    --------------------------------------------------------------------
    -- Homomorphisms
    
    foldr-homo‿- : ∀ {xs} →
                   foldr _+_ 0# (map -_ xs) ≈ -_ (foldr _+_ 0# xs)
    foldr-homo‿- {[]}     = begin⟨ setoid ⟩
      0#          ≈⟨ sym (-‿inverseʳ 0#) ⟩
      0# + (- 0#) ≈⟨ +-identityˡ (- 0#) ⟩
      - 0#        ∎
    foldr-homo‿- {x ∷ xs} = begin⟨ setoid ⟩
      - x + foldr _+_ 0# (map -_ xs) ≈⟨ +-congˡ (foldr-homo‿- {xs}) ⟩
      - x + (- foldr _+_ 0# xs)      ≈⟨ +-comm (- x) (- foldr _+_ 0# xs) ⟩
      - foldr _+_ 0# xs + (- x)      ≈⟨ sym (⁻¹-anti-homo-∙ x (foldr _+_ 0# xs)) ⟩
      - (x + foldr _+_ 0# xs)        ∎

    zipWith-*-homo‿- : ∀ {xs ys} →
                       zipWith _*_ xs (map -_ ys) ≋ map -_ (zipWith _*_ xs ys)
    zipWith-*-homo‿- {[]}     {[]}     = ≋-refl
    zipWith-*-homo‿- {[]}     {y ∷ ys} = ≋-refl
    zipWith-*-homo‿- {x ∷ xs} {[]}     = ≋-refl
    zipWith-*-homo‿- {x ∷ xs} {y ∷ ys} = sym (-‿distribʳ-* x y)
                                       ∷′ zipWith-*-homo‿-

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
                      -- (zipWith-comm-map′ *-homo) ⟩
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

      -- I was hoping that this might work, but alas no postulate in the
      -- standard library that `b *ᵣ s` must equal `s *ₗ b`. :(
      -- a ∙ (b *ᵣ s) ≈⟨ ∙-congˡ (≈ᴹ-sym {!!}) ⟩
      -- a ∙ (s *ₗ b) ≈⟨ ∙-comm-*ₗ ⟩
      -- s * (a ∙ b)  ≈⟨ *-comm s (a ∙ b) ⟩
      -- (a ∙ b) * s  ∎
    
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
