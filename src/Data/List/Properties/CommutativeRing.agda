------------------------------------------------------------------------
-- The Agda standard library
--
-- List-related properties over a CommutativeRing
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeRing)
open import Level           using (Level)

module Data.List.Properties.CommutativeRing
  {r ℓ  : Level}
  (ring : CommutativeRing r ℓ)
  where

open import Algebra
  using ( Group; Ring;
          Op₁; Op₂
        )
open import Algebra.Morphism.Definitions
  using (Homomorphic₂′; Homomorphic₂′′)
open import Data.List
open import Data.List.Relation.Binary.Pointwise using ()
  renaming (head to head′; tail to tail′)
open import Data.Nat.Properties
  using (suc-injective; ⊓-operator; ≤-reflexive)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Binary.Reasoning.MultiSetoid

import Algebra.Properties.Group                  as PropGroup
import Algebra.Properties.Ring                   as PropRing
import Data.List.Relation.Binary.Equality.Setoid as ListEq
import Data.Nat                                  as ℕ

open CommutativeRing ring renaming (Carrier to S)
open ListEq setoid using (_≋_; ≋-refl; ≋-setoid; ≋-sym)
  renaming ( _∷_  to _∷′_ )

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

