------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

-- The definition of lexicographic ordering used here is suitable if
-- the argument order is a strict partial order. 

module Data.List.Relation.StrictLex where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Function using (_∘_; flip; id)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Base using (List; []; _∷_)
open import Level using (_⊔_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary
open import Relation.Binary.Consequences
open import Data.List.Relation.Pointwise as Pointwise
   using ([]; _∷_; head; tail)

-- The lexicographic ordering itself can be either strict or non-strict,
-- depending on whether type P is inhabited.

data Lex {a ℓ₁ ℓ₂} {A : Set a} (P : Set) (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) : Rel (List A) (ℓ₁ ⊔ ℓ₂) where
  base : P                             → Lex P _≈_ _<_ []       []
  halt : ∀ {y ys}                      → Lex P _≈_ _<_ []       (y ∷ ys)
  this : ∀ {x xs y ys} (x<y : x < y)   → Lex P _≈_ _<_ (x ∷ xs) (y ∷ ys)
  next : ∀ {x xs y ys} (x≈y : x ≈ y)
         (xs⊴ys : Lex P _≈_ _<_ xs ys) → Lex P _≈_ _<_ (x ∷ xs) (y ∷ ys)

-- General properties

module _ {a ℓ₁ ℓ₂} {A : Set a} {P : Set} {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} where

  private
    _≋_ = Pointwise.Rel _≈_
    _≺_ = Lex P _≈_ _<_
  
  ¬≤-this : ∀ {x y xs ys} → ¬ (x ≈ y) → ¬ (x < y) →
            ¬ (x ∷ xs) ≺ (y ∷ ys)
  ¬≤-this x≉y x≮y (this x<y)       = x≮y x<y
  ¬≤-this x≉y x≮y (next x≈y xs⊴ys) = x≉y x≈y

  ¬≤-next : ∀ {x y xs ys} → ¬ x < y → ¬ xs ≺ ys →
            ¬ (x ∷ xs) ≺ (y ∷ ys)
  ¬≤-next x≮y ¬xs⊴ys (this x<y)       = x≮y x<y
  ¬≤-next x≮y ¬xs⊴ys (next x≈y xs⊴ys) = ¬xs⊴ys xs⊴ys

  transitive : IsEquivalence _≈_ → _<_ Respects₂ _≈_ → Transitive _<_ →
               Transitive _≺_
  transitive eq resp tr = trans
    where
    trans : Transitive (Lex P _≈_ _<_)
    trans (base p)         (base _)         = base p
    trans (base y)         halt             = halt
    trans halt             (this y<z)       = halt
    trans halt             (next y≈z ys⊴zs) = halt
    trans (this x<y)       (this y<z)       = this (tr x<y y<z)
    trans (this x<y)       (next y≈z ys⊴zs) = this (proj₁ resp y≈z x<y)
    trans (next x≈y xs⊴ys) (this y<z)       =
      this (proj₂ resp (IsEquivalence.sym eq x≈y) y<z)
    trans (next x≈y xs⊴ys) (next y≈z ys⊴zs) =
      next (IsEquivalence.trans eq x≈y y≈z) (trans xs⊴ys ys⊴zs)

  antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _<_ →  Asymmetric _<_ →
                  Antisymmetric _≋_ _≺_
  antisymmetric sym ir asym = as
    where
    as : Antisymmetric _≋_ _≺_
    as (base _)         (base _)         = []
    as halt             ()
    as (this x<y)       (this y<x)       = ⊥-elim (asym x<y y<x)
    as (this x<y)       (next y≈x ys⊴xs) = ⊥-elim (ir (sym y≈x) x<y)
    as (next x≈y xs⊴ys) (this y<x)       = ⊥-elim (ir (sym x≈y) y<x)
    as (next x≈y xs⊴ys) (next y≈x ys⊴xs) = x≈y ∷ as xs⊴ys ys⊴xs

  respects₂ : IsEquivalence _≈_ → _<_ Respects₂ _≈_ → _≺_ Respects₂ _≋_
  respects₂ eq (resp₁ , resp₂) = resp¹ , resp²
    where
    open IsEquivalence eq using () renaming (sym to ≈-sym; trans to ≈-trans)
    
    resp¹ : ∀ {xs} → Lex P _≈_ _<_ xs Respects _≋_
    resp¹ []            xs⊴[]            = xs⊴[]
    resp¹ (_   ∷ _)     halt             = halt
    resp¹ (x≈y ∷ _)     (this z<x)       = this (resp₁ x≈y z<x)
    resp¹ (x≈y ∷ xs≋ys) (next z≈x zs⊴xs) =
      next (≈-trans z≈x x≈y) (resp¹ xs≋ys zs⊴xs)

    resp² : ∀ {ys} → flip (Lex P _≈_ _<_) ys Respects _≋_
    resp² []            []⊴ys            = []⊴ys
    resp² (x≈z ∷ _)     (this x<y)       = this (resp₂ x≈z x<y)
    resp² (x≈z ∷ xs≋zs) (next x≈y xs⊴ys) =
      next (≈-trans (≈-sym x≈z) x≈y) (resp² xs≋zs xs⊴ys)

  decidable : Dec P → Decidable _≈_ → Decidable _<_ → Decidable _≺_
  decidable (yes p) dec-≈ dec-< []       []       = yes (base p)
  decidable (no ¬p) dec-≈ dec-< []       []       = no λ{(base p) → ¬p p}
  decidable dec-P   dec-≈ dec-< []       (y ∷ ys) = yes halt
  decidable dec-P   dec-≈ dec-< (x ∷ xs) []       = no λ()
  decidable dec-P   dec-≈ dec-< (x ∷ xs) (y ∷ ys) with dec-< x y
  ... | yes x<y = yes (this x<y)
  ... | no x≮y with dec-≈ x y
  ...   | no x≉y = no (¬≤-this x≉y x≮y)
  ...   | yes x≈y with decidable dec-P dec-≈ dec-< xs ys
  ...     | yes xs⊴ys = yes (next x≈y xs⊴ys)
  ...     | no ¬xs⊴ys = no (¬≤-next x≮y ¬xs⊴ys)
  
----------------------------------------------------------------------
-- Strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  Lex-< : (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) → Rel (List A) (ℓ₁ ⊔ ℓ₂)
  Lex-< = Lex ⊥
  
  -- Properties

  module _ {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} where
  
    private
      _≋_ = Pointwise.Rel _≈_
      _≺_ = Lex-< _≈_ _<_
    
    ¬[]<[] : ¬ [] ≺ []
    ¬[]<[] (base ())

    <-irreflexive : Irreflexive _≈_ _<_ → Irreflexive _≋_ _≺_
    <-irreflexive irr []            (base ())
    <-irreflexive irr (x≈y ∷ xs≋ys) (this x<y)     = irr x≈y x<y
    <-irreflexive irr (x≈y ∷ xs≋ys) (next _ xs⊴ys) =
      <-irreflexive irr xs≋ys xs⊴ys

    <-asymmetric : Symmetric _≈_ → _<_ Respects₂ _≈_ → Asymmetric _<_ →
                   Asymmetric _≺_
    <-asymmetric sym resp as = asym
      where
      irrefl : Irreflexive _≈_ _<_
      irrefl = asym⟶irr resp sym as

      asym : Asymmetric _≺_
      asym (halt)           ()
      asym (base bot)       _                = bot
      asym (this x<y)       (this y<x)       = as x<y y<x
      asym (this x<y)       (next y≈x ys⊴xs) = irrefl (sym y≈x) x<y
      asym (next x≈y xs⊴ys) (this y<x)       = irrefl (sym x≈y) y<x
      asym (next x≈y xs⊴ys) (next y≈x ys⊴xs) = asym xs⊴ys ys⊴xs

    <-antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _<_ →  Asymmetric _<_ →
                      Antisymmetric _≋_ _≺_
    <-antisymmetric = antisymmetric
    
    <-transitive : IsEquivalence _≈_ → _<_ Respects₂ _≈_ → Transitive _<_ →
                   Transitive _≺_
    <-transitive = transitive
    
    <-decidable : Decidable _≈_ → Decidable _<_ → Decidable _≺_
    <-decidable = decidable (no id)

    <-respects₂ : IsEquivalence _≈_ → _<_ Respects₂ _≈_ → _≺_ Respects₂ _≋_
    <-respects₂ = respects₂
    
    <-compare : Symmetric _≈_ → Trichotomous _≈_ _<_ → Trichotomous _≋_ _≺_
    <-compare sym tri = cmp
      where
      cmp : Trichotomous _≋_ _≺_
      cmp []       []       = tri≈ ¬[]<[] []    ¬[]<[]
      cmp []       (y ∷ ys) = tri< halt   (λ()) (λ())
      cmp (x ∷ xs) []       = tri> (λ())  (λ()) halt
      cmp (x ∷ xs) (y ∷ ys) with tri x y
      ... | tri< x<y x≉y y≮x =
            tri< (this x<y) (x≉y ∘ head) (¬≤-this (x≉y ∘ sym) y≮x)
      ... | tri> x≮y x≉y y<x =
            tri> (¬≤-this x≉y x≮y) (x≉y ∘ head) (this y<x)
      ... | tri≈ x≮y x≈y y≮x with cmp xs ys
      ...   | tri< xs<ys xs≉ys ys≮xs =
              tri< (next x≈y xs<ys) (xs≉ys ∘ tail) (¬≤-next y≮x ys≮xs)
      ...   | tri≈ ¬xs<ys xs≈ys ys≮xs =
              tri≈ (¬≤-next x≮y ¬xs<ys) (x≈y ∷ xs≈ys) (¬≤-next y≮x ys≮xs)
      ...   | tri> ¬xs<ys xs≉ys ys<xs =
              tri> (¬≤-next x≮y ¬xs<ys) (xs≉ys ∘ tail) (next (sym x≈y) ys<xs)

    
    <-isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_ →
                           IsStrictPartialOrder _≋_ _≺_
    <-isStrictPartialOrder spo = record
      { isEquivalence = Pointwise.isEquivalence isEquivalence
      ; irrefl        = <-irreflexive irrefl
      ; trans         = transitive isEquivalence <-resp-≈ trans
      ; <-resp-≈      = respects₂ isEquivalence <-resp-≈
      } where open IsStrictPartialOrder spo

    <-isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_ →
                         IsStrictTotalOrder _≋_ _≺_
    <-isStrictTotalOrder sto = record
      { isEquivalence = Pointwise.isEquivalence isEquivalence
      ; trans         = <-transitive isEquivalence <-resp-≈ trans
      ; compare       = <-compare Eq.sym compare
      } where open IsStrictTotalOrder sto

<-strictPartialOrder : ∀ {a ℓ₁ ℓ₂} → StrictPartialOrder a ℓ₁ ℓ₂ → StrictPartialOrder _ _ _
<-strictPartialOrder spo = record
  { isStrictPartialOrder = <-isStrictPartialOrder isStrictPartialOrder
  } where open StrictPartialOrder spo
  
<-strictTotalOrder : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ → StrictTotalOrder _ _ _
<-strictTotalOrder sto = record
  { isStrictTotalOrder = <-isStrictTotalOrder isStrictTotalOrder
  } where open StrictTotalOrder sto

----------------------------------------------------------------------
-- Non-strict lexicographic ordering.

module _ {a ℓ₁ ℓ₂} {A : Set a} where

  Lex-≤ : (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) → Rel (List A) (ℓ₁ ⊔ ℓ₂)
  Lex-≤ = Lex ⊤

  -- Properties

  ≤-reflexive : (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) → Pointwise.Rel _≈_ ⇒ Lex-≤ _≈_ _<_
  ≤-reflexive _≈_ _<_ []            = base tt
  ≤-reflexive _≈_ _<_ (x≈y ∷ xs≈ys) =
    next x≈y (≤-reflexive _≈_ _<_ xs≈ys)

  module _ {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} where

    private
      _≋_ = Pointwise.Rel _≈_
      _≼_ = Lex-≤ _≈_ _<_

    ≤-antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _<_ →  Asymmetric _<_ →
                      Antisymmetric _≋_ _≼_
    ≤-antisymmetric = antisymmetric
    
    ≤-transitive : IsEquivalence _≈_ → _<_ Respects₂ _≈_ → Transitive _<_ →
                   Transitive _≼_
    ≤-transitive = transitive

    -- Note that trichotomy is an unnecessarily strong precondition for
    -- the following lemma.

    ≤-total : Symmetric _≈_ → Trichotomous _≈_ _<_ → Total _≼_
    ≤-total _   _   []       []       = inj₁ (base tt)
    ≤-total _   _   []       (x ∷ xs) = inj₁ halt
    ≤-total _   _   (x ∷ xs) []       = inj₂ halt
    ≤-total sym tri (x ∷ xs) (y ∷ ys) with tri x y
    ... | tri< x<y _ _ = inj₁ (this x<y)
    ... | tri> _ _ y<x = inj₂ (this y<x)
    ... | tri≈ _ x≈y _ with ≤-total sym tri xs ys
    ...   | inj₁ xs≲ys = inj₁ (next      x≈y  xs≲ys)
    ...   | inj₂ ys≲xs = inj₂ (next (sym x≈y) ys≲xs)
    
    ≤-decidable : Decidable _≈_ → Decidable _<_ → Decidable _≼_
    ≤-decidable = decidable (yes tt)

    ≤-respects₂ : IsEquivalence _≈_ → _<_ Respects₂ _≈_ → _≼_ Respects₂ _≋_
    ≤-respects₂ = respects₂
    
    ≤-isPreorder : IsEquivalence _≈_ → Transitive _<_ → _<_ Respects₂ _≈_ →
                   IsPreorder _≋_ _≼_
    ≤-isPreorder eq tr resp = record
      { isEquivalence = Pointwise.isEquivalence eq
      ; reflexive     = ≤-reflexive _≈_ _<_
      ; trans         = transitive eq resp tr
      }

    ≤-isPartialOrder : IsStrictPartialOrder _≈_ _<_ → IsPartialOrder _≋_ _≼_
    ≤-isPartialOrder  spo = record
      { isPreorder = ≤-isPreorder isEquivalence trans <-resp-≈
      ; antisym    = antisymmetric Eq.sym irrefl
                                   (trans∧irr⟶asym {_≈_ = _≈_} Eq.refl trans irrefl)
      }
      where open IsStrictPartialOrder spo

    ≤-isTotalOrder : IsStrictTotalOrder _≈_ _<_ → IsTotalOrder _≋_ _≼_
    ≤-isTotalOrder sto = record
      { isPartialOrder = ≤-isPartialOrder isStrictPartialOrder
      ; total          = ≤-total Eq.sym compare
      }
      where open IsStrictTotalOrder sto

    ≤-isDecTotalOrder : IsStrictTotalOrder _≈_ _<_ → IsDecTotalOrder _≋_ _≼_
    ≤-isDecTotalOrder sto = record
      { isTotalOrder = ≤-isTotalOrder sto
      ; _≟_          = Pointwise.decidable _≟_
      ; _≤?_         = ≤-decidable _≟_ _<?_
      }
      where open IsStrictTotalOrder sto

-- "Packages" (e.g. preorders) can also be handled.

≤-preorder : ∀ {a ℓ₁ ℓ₂} → Preorder a ℓ₁ ℓ₂ → Preorder _ _ _
≤-preorder pre = record
  { isPreorder = ≤-isPreorder isEquivalence trans ∼-resp-≈
  } where open Preorder pre

≤-partialOrder : ∀ {a ℓ₁ ℓ₂} → StrictPartialOrder a ℓ₁ ℓ₂ → Poset _ _ _
≤-partialOrder spo = record
  { isPartialOrder = ≤-isPartialOrder isStrictPartialOrder
  } where open StrictPartialOrder spo

≤-decTotalOrder : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ → DecTotalOrder _ _ _
≤-decTotalOrder sto = record
  { isDecTotalOrder = ≤-isDecTotalOrder isStrictTotalOrder
  } where open StrictTotalOrder sto
