------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences on pointwise equality of freely adding an infimum to a Set
------------------------------------------------------------------------

open import Relation.Binary

module Relation.Binary.Construction.Infimum.Pointwise
       {a e} {A : Set a} (_≈_ : Rel A e) where

open import Relation.Binary.Construction.Pointed.Pointwise _≈_
  renaming (_≈∙_ to _≈₋_; ∙≈∙ to ⊥⁺≈⊥⁺
           ; ≈∙-refl to ≈₋-refl
           ; ≈∙-sym to ≈₋-sym
           ; ≈∙-trans to ≈₋-trans
           ; ≈∙-dec to ≈₋-dec
           ; ≈∙-irrelevance to ≈₋-irrelevance
           ; ≈∙-substitutive to ≈₋-substitutive
           ; ≈∙-isEquivalence to ≈₋-isEquivalence
           ; ≈∙-isDecEquivalence to ≈₋-isDecEquivalence
           )
  public
