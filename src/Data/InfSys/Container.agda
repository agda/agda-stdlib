------------------------------------------------------------------------
-- The Agda standard library
--
-- Library for (Generalized) Inference Systems
-- Equivalence wrt Indexed (Endo)Containers
------------------------------------------------------------------------

{-# OPTIONS --sized-types --guardedness --without-K #-}

open import Agda.Builtin.Equality
open import Codata.Sized.Thunk
open import Data.Container.Indexed
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Level
open import Relation.Unary using (_⊆_)
open import Size

module Data.InfSys.Container {𝓁}(U : Set 𝓁) where

  module ISCont {𝓁p} where

    private
      variable
        𝓁c 𝓁c' 𝓁' : Level

    ISCont : {𝓁c : Level} → Set _
    ISCont {𝓁c} = Container U U 𝓁c 𝓁p

    ISContClosed : (is : ISCont {𝓁c}) → (U → Set 𝓁') → Set _
    ISContClosed is P = (⟦ is ⟧ P ⊆ P)

    _↾_ : ISCont {𝓁c} → (U → Set 𝓁') → ISCont {_}
    (is ↾ P) .Command  u       = is .Command u × P u
    (is ↾ P) .Response (c , p) = is .Response c
    (is ↾ P) .next (c , p) r   = is .next c r

    _∪_ : ISCont {𝓁c} → ISCont {𝓁c'} → ISCont {_}
    (is ∪ is') .Command  u = is .Command u  ⊎ is' .Command u
    (is ∪ is') .Response   = [ is .Response , is' .Response ]
    (is ∪ is') .next       = [ is .next     , is' .next     ]

    Ind⟦_⟧ = μ

    -- Coinductive interpretation

    record CoInd⟦_⟧ (is : ISCont {𝓁c}) (u : U) : Set (𝓁c ⊔ 𝓁p) where
        coinductive
        constructor cofold_
        field
            unfold : ⟦ is ⟧ CoInd⟦ is ⟧ u

    -- Sized coinductive interpretation

    record CoInd⟦_⟧^ (is : ISCont {𝓁c}) (i : Size) (u : U) :
        Set (𝓁c ⊔ 𝓁p) where
        coinductive
        constructor cofold_
        field
            unfold : {j : Size< i} → ⟦ is ⟧ (CoInd⟦ is ⟧^ j) u

    -- Sized coinductive interpretation (using Thunk)

    data SCoInd⟦_⟧ (is : ISCont {𝓁c}) (u : U) (i : Size) :
        Set (𝓁c ⊔ 𝓁p) where
        sfold : ⟦ is ⟧ (λ u → Thunk (SCoInd⟦ is ⟧ u) i) u →
                SCoInd⟦ is ⟧ u i

    FCoInd⟦_,_⟧ : (I : ISCont {𝓁c}) (C : ISCont {𝓁c'}) → U → Set _
    FCoInd⟦ I , C ⟧ = CoInd⟦ I ↾ Ind⟦ I ∪ C ⟧ ⟧

    module _
      {𝓁c 𝓁'} (is : ISCont {𝓁c})
      (P : U → Set 𝓁') (closed : ISContClosed is P)
      where

      open import Data.W.Indexed using (iter)

      ind[_] : Ind⟦ is ⟧ ⊆ P
      ind[_] = iter is closed

    module _
      {𝓁c 𝓁'} (is : ISCont {𝓁c})
      (P : U → Set 𝓁') (consistent : P ⊆ ⟦ is ⟧ P)
      where

      open CoInd⟦_⟧

      coind[] : P ⊆ CoInd⟦ is ⟧
      coind[] p .unfold .proj₁ = consistent p .proj₁
      coind[] p .unfold .proj₂ r = coind[] (consistent p .proj₂ r)

    module _
      {𝓁c 𝓁c' 𝓁'}(I : ISCont {𝓁c}) (C : ISCont {𝓁c'})
      (P : U → Set 𝓁')
      (bounded : P ⊆ Ind⟦ I ∪ C ⟧) (consistent : P ⊆ ⟦ I ⟧ P)
      where

      open CoInd⟦_⟧

      bounded-coind[] : P ⊆ FCoInd⟦ I , C ⟧
      bounded-coind[] p .unfold .proj₁ .proj₁ = consistent p .proj₁
      bounded-coind[] p .unfold .proj₁ .proj₂ = bounded p
      bounded-coind[] p .unfold .proj₂ r      = bounded-coind[] (consistent p .proj₂ r)

  module _ {𝓁p} where

    open ISCont {𝓁p}
    open import Data.InfSys.Base {𝓁} as IS
    open IS.MetaRule
    open IS.IS

    private
      variable
        𝓁c 𝓁n 𝓁P : Level
        𝓁P' 𝓁' 𝓁n' : Level
        𝓁1 𝓁2 : Level

    {- Every IS is an EndoContainer -}

    C[_] : IS {𝓁c} {𝓁p} {𝓁n} U → ISCont {𝓁 ⊔ 𝓁c ⊔ 𝓁n}
    C[ is ] .Command u =
      Σ[ rn ∈ is .Names ]
      Σ[ c ∈ is .rules rn .Ctx ] u ≡ is .rules rn .conclu c
    C[ is ] .Response (rn , c , refl) = is .rules rn .Pos c
    C[ is ] .next (rn , c , refl) r = is .rules rn .prems c r

    {- Every EndoContainer is an IS -}

    IS[_] : ∀{𝓁'} → ISCont {𝓁'} → IS {zero} {𝓁p} {𝓁 ⊔ 𝓁'} U
    IS[_] C .Names = Σ[ u ∈ U ] C .Command u
    IS[ C ] .rules (u , c) = record
           { Ctx = ⊤
           ; Pos = λ _ → C .Response c
           ; prems = λ _ r → C .next c r
           ; conclu = λ _ → u
           }

    {- Equivalence -}

    isf-to-c : {is : IS {𝓁c} {𝓁p} {𝓁n} U} {P : U → Set 𝓁P} →
               ISF[ is ] P ⊆ ⟦ C[ is ] ⟧ P
    isf-to-c (rn , c , refl , pr) = (rn , c , refl) , pr

    c-to-isf : {C : ISCont {𝓁'}} {P : U → Set 𝓁P} →
               ⟦ C ⟧ P ⊆ ISF[ IS[ C ] ] P
    c-to-isf (c , pr) = (_ , c) , tt , refl , pr

    ∪-IS-eq : {is : IS {𝓁c} {𝓁p} {𝓁n} U}
              {is' : IS {𝓁c} {𝓁p} {𝓁n'} U}
              {P : U → Set 𝓁P} →
              ISF[ is IS.∪ is' ] P ⊆ ⟦ C[ is ] ISCont.∪ C[ is' ] ⟧ P
    ∪-IS-eq (inj₁ rn , c , refl , pr) = inj₁ (rn , c , refl) , pr
    ∪-IS-eq (inj₂ rn , c , refl , pr) = inj₂ (rn , c , refl) , pr

    ∪-C-eq : {c : ISCont {𝓁1}} {c' : ISCont {𝓁2}}
             {P : U → Set 𝓁P} →
             ⟦ c ISCont.∪ c' ⟧ P ⊆ ISF[ IS[ c ] IS.∪ IS[ c' ] ] P
    ∪-C-eq (inj₁ c , r) = inj₁ (_ , c) , tt , refl , r
    ∪-C-eq (inj₂ c , r) = inj₂ (_ , c) , tt , refl , r

    ⊓-IS-eq : {is : IS {𝓁c} {𝓁p} {𝓁n} U}
              {P : U → Set 𝓁P}
              {P' : U → Set 𝓁P'} →
              ISF[ is ⊓ P ] P' ⊆ ⟦ C[ is ] ↾ P ⟧ P'
    ⊓-IS-eq (rn , (c , Pu) , refl , pr) = ((rn , c , refl) , Pu) , pr

    ↾-C-eq : {c : ISCont {𝓁c}}
             {P : U → Set 𝓁P} {P' : U → Set 𝓁P'} →
             ⟦ c ↾ P ⟧ P' ⊆ ISF[ IS[ c ] ⊓ P ] P'
    ↾-C-eq ((c , Pu) , r) = (_ , c) , (tt , Pu) , refl , r
