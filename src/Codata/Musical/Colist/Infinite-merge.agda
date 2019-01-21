------------------------------------------------------------------------
-- The Agda standard library
--
-- Infinite merge operation for coinductive lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module Codata.Musical.Colist.Infinite-merge where

open import Codata.Musical.Notation
open import Codata.Musical.Colist as Colist hiding (_⋎_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as Prod
open import Data.Sum
open import Data.Sum.Properties
open import Data.Sum.Relation.Binary.Pointwise
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; Inverse; inverse)
import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Induction.Nat using (<′-wellFounded)
import Induction.WellFounded as WF
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Some code that is used to work around Agda's syntactic guardedness
-- checker.

private

  infixr 5 _∷_ _⋎_

  data ColistP {a} (A : Set a) : Set a where
    []  : ColistP A
    _∷_ : A → ∞ (ColistP A) → ColistP A
    _⋎_ : ColistP A → ColistP A → ColistP A

  data ColistW {a} (A : Set a) : Set a where
    []  : ColistW A
    _∷_ : A → ColistP A → ColistW A

  program : ∀ {a} {A : Set a} → Colist A → ColistP A
  program []       = []
  program (x ∷ xs) = x ∷ ♯ program (♭ xs)

  mutual

    _⋎W_ : ∀ {a} {A : Set a} → ColistW A → ColistP A → ColistW A
    []       ⋎W ys = whnf ys
    (x ∷ xs) ⋎W ys = x ∷ (ys ⋎ xs)

    whnf : ∀ {a} {A : Set a} → ColistP A → ColistW A
    whnf []        = []
    whnf (x ∷ xs)  = x ∷ ♭ xs
    whnf (xs ⋎ ys) = whnf xs ⋎W ys

  mutual

    ⟦_⟧P : ∀ {a} {A : Set a} → ColistP A → Colist A
    ⟦ xs ⟧P = ⟦ whnf xs ⟧W

    ⟦_⟧W : ∀ {a} {A : Set a} → ColistW A → Colist A
    ⟦ [] ⟧W     = []
    ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P

  mutual

    ⋎-homP : ∀ {a} {A : Set a} (xs : ColistP A) {ys} →
             ⟦ xs ⋎ ys ⟧P ≈ ⟦ xs ⟧P Colist.⋎ ⟦ ys ⟧P
    ⋎-homP xs = ⋎-homW (whnf xs) _

    ⋎-homW : ∀ {a} {A : Set a} (xs : ColistW A) ys →
             ⟦ xs ⋎W ys ⟧W ≈ ⟦ xs ⟧W Colist.⋎ ⟦ ys ⟧P
    ⋎-homW (x ∷ xs) ys = x ∷ ♯ ⋎-homP ys
    ⋎-homW []       ys = begin ⟦ ys ⟧P ∎
      where open ≈-Reasoning

  ⟦program⟧P : ∀ {a} {A : Set a} (xs : Colist A) →
               ⟦ program xs ⟧P ≈ xs
  ⟦program⟧P []       = []
  ⟦program⟧P (x ∷ xs) = x ∷ ♯ ⟦program⟧P (♭ xs)

  Any-⋎P : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} →
           Any P ⟦ program xs ⋎ ys ⟧P ↔ (Any P xs ⊎ Any P ⟦ ys ⟧P)
  Any-⋎P {P = P} xs {ys} =
    Any P ⟦ program xs ⋎ ys ⟧P                ↔⟨ Any-cong Inv.id (⋎-homP (program xs)) ⟩
    Any P (⟦ program xs ⟧P Colist.⋎ ⟦ ys ⟧P)  ↔⟨ Any-⋎ _ ⟩
    (Any P ⟦ program xs ⟧P ⊎ Any P ⟦ ys ⟧P)   ↔⟨ Any-cong Inv.id (⟦program⟧P _) ⊎-cong (_ ∎) ⟩
    (Any P xs ⊎ Any P ⟦ ys ⟧P)                ∎
    where open Related.EquationalReasoning

  index-Any-⋎P :
    ∀ {a p} {A : Set a} {P : A → Set p} xs {ys}
    (p : Any P ⟦ program xs ⋎ ys ⟧P) →
    index p ≥′ [ index , index ]′ (Inverse.to (Any-⋎P xs) ⟨$⟩ p)
  index-Any-⋎P xs p
    with       Any-resp      id  (⋎-homW (whnf (program xs)) _) p
       | index-Any-resp {f = id} (⋎-homW (whnf (program xs)) _) p
  index-Any-⋎P xs p | q | q≡p
    with Inverse.to (Any-⋎ ⟦ program xs ⟧P) ⟨$⟩ q
       |       index-Any-⋎ ⟦ program xs ⟧P      q
  index-Any-⋎P xs p | q | q≡p | inj₂ r | r≤q rewrite q≡p = r≤q
  index-Any-⋎P xs p | q | q≡p | inj₁ r | r≤q
    with       Any-resp      id  (⟦program⟧P xs) r
       | index-Any-resp {f = id} (⟦program⟧P xs) r
  index-Any-⋎P xs p | q | q≡p | inj₁ r | r≤q | s | s≡r
    rewrite s≡r | q≡p = r≤q

------------------------------------------------------------------------
-- Infinite variant of _⋎_.

private

  merge′ : ∀ {a} {A : Set a} → Colist (A × Colist A) → ColistP A
  merge′ []               = []
  merge′ ((x , xs) ∷ xss) = x ∷ ♯ (program xs ⋎ merge′ (♭ xss))

merge : ∀ {a} {A : Set a} → Colist (A × Colist A) → Colist A
merge xss = ⟦ merge′ xss ⟧P

------------------------------------------------------------------------
-- Any lemma for merge.

module _ {a p} {A : Set a} {P : A → Set p} where

  Any-merge : ∀ xss → Any P (merge xss) ↔ Any (λ { (x , xs) → P x ⊎ Any P xs }) xss
  Any-merge xss = inverse (proj₁ ∘ to xss) from (proj₂ ∘ to xss) to∘from
    where
    open P.≡-Reasoning

    -- The from function.

    Q = λ { (x , xs) → P x ⊎ Any P xs }

    from : ∀ {xss} → Any Q xss → Any P (merge xss)
    from (here (inj₁ p))        = here p
    from (here (inj₂ p))        = there (Inverse.from (Any-⋎P _)  ⟨$⟩ inj₁ p)
    from (there {x = _ , xs} p) = there (Inverse.from (Any-⋎P xs) ⟨$⟩ inj₂ (from p))

    -- The from function is injective.

    from-injective : ∀ {xss} (p₁ p₂ : Any Q xss) →
                     from p₁ ≡ from p₂ → p₁ ≡ p₂
    from-injective (here (inj₁ p))  (here (inj₁ .p)) P.refl = P.refl
    from-injective (here (inj₁ _))  (here (inj₂ _))  ()
    from-injective (here (inj₂ _))  (here (inj₁ _))  ()
    from-injective (here (inj₂ p₁)) (here (inj₂ p₂)) eq     =
      P.cong (here ∘ inj₂) $
      inj₁-injective $
      Inverse.injective (Inv.sym (Any-⋎P _)) {x = inj₁ p₁} {y = inj₁ p₂} $
      there-injective eq
    from-injective (here (inj₁ _))  (there _)  ()
    from-injective (here (inj₂ p₁)) (there p₂) eq
      with Inverse.injective (Inv.sym (Any-⋎P _))
                             {x = inj₁ p₁} {y = inj₂ (from p₂)}
                             (there-injective eq)
    ... | ()
    from-injective (there _)  (here (inj₁ _))  ()
    from-injective (there p₁) (here (inj₂ p₂)) eq
      with Inverse.injective (Inv.sym (Any-⋎P _))
                             {x = inj₂ (from p₁)} {y = inj₁ p₂}
                             (there-injective eq)
    ... | ()
    from-injective (there {x = _ , xs} p₁) (there p₂) eq =
      P.cong there $
      from-injective p₁ p₂ $
      inj₂-injective $
      Inverse.injective (Inv.sym (Any-⋎P xs))
                        {x = inj₂ (from p₁)} {y = inj₂ (from p₂)} $
      there-injective eq

    -- The to function (defined as a right inverse of from).

    Input = ∃ λ xss → Any P (merge xss)

    Pred : Input → Set _
    Pred (xss , p) = ∃ λ (q : Any Q xss) → from q ≡ p

    to : ∀ xss p → Pred (xss , p)
    to = λ xss p →
      WF.All.wfRec (WF.Inverse-image.wellFounded size <′-wellFounded) _
                   Pred step (xss , p)
      where
      size : Input → ℕ
      size (_ , p) = index p

      step : ∀ p → WF.WfRec (_<′_ on size) Pred p → Pred p
      step ([]             , ())      rec
      step ((x , xs) ∷ xss , here  p) rec = here (inj₁ p) , P.refl
      step ((x , xs) ∷ xss , there p) rec
        with Inverse.to (Any-⋎P xs) ⟨$⟩ p
           | Inverse.left-inverse-of (Any-⋎P xs) p
           | index-Any-⋎P xs p
      ... | inj₁ q | P.refl | _   = here (inj₂ q) , P.refl
      ... | inj₂ q | P.refl | q≤p =
        Prod.map there
                 (P.cong (there ∘ _⟨$⟩_ (Inverse.from (Any-⋎P xs)) ∘ inj₂))
                 (rec (♭ xss , q) (s≤′s q≤p))

    to∘from = λ p → from-injective _ _ (proj₂ (to xss (from p)))

-- Every member of xss is a member of merge xss, and vice versa (with
-- equal multiplicities).

∈-merge : ∀ {a} {A : Set a} {y : A} xss →
          y ∈ merge xss ↔ ∃₂ λ x xs → (x , xs) ∈ xss × (y ≡ x ⊎ y ∈ xs)
∈-merge {y = y} xss =
  y ∈ merge xss                                           ↔⟨ Any-merge _ ⟩
  Any (λ { (x , xs) → y ≡ x ⊎ y ∈ xs }) xss               ↔⟨ Any-∈ ⟩
  (∃ λ { (x , xs) → (x , xs) ∈ xss × (y ≡ x ⊎ y ∈ xs) })  ↔⟨ Σ-assoc ⟩
  (∃₂ λ x xs → (x , xs) ∈ xss × (y ≡ x ⊎ y ∈ xs))         ∎
  where open Related.EquationalReasoning
