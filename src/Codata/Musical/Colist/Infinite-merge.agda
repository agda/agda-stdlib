------------------------------------------------------------------------
-- The Agda standard library
--
-- Infinite merge operation for coinductive lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module Codata.Musical.Colist.Infinite-merge where

open import Codata.Musical.Notation
open import Codata.Musical.Colist as Colist hiding (_⋎_)
open import Data.Nat.Base
open import Data.Nat.Induction using (<′-wellFounded)
open import Data.Nat.Properties
open import Data.Product.Base as Product using (_×_; _,_; ∃; ∃₂; proj₁; proj₂)
open import Data.Sum.Base
open import Data.Sum.Properties
open import Data.Sum.Function.Propositional using (_⊎-cong_)
open import Function.Base
open import Function.Bundles
open import Function.Properties.Inverse using (↔-refl; ↔-sym; ↔⇒↣)
import Function.Related.Propositional as Related
open import Function.Related.TypeIsomorphisms
open import Level
open import Relation.Unary using (Pred)
import Induction.WellFounded as WF
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
import Relation.Binary.Construct.On as On

private
  variable
    a p : Level
    A : Set a
    P : Pred A p

------------------------------------------------------------------------
-- Some code that is used to work around Agda's syntactic guardedness
-- checker.

private

  infixr 5 _∷_ _⋎_

  data ColistP (A : Set a) : Set a where
    []  : ColistP A
    _∷_ : A → ∞ (ColistP A) → ColistP A
    _⋎_ : ColistP A → ColistP A → ColistP A

  data ColistW (A : Set a) : Set a where
    []  : ColistW A
    _∷_ : A → ColistP A → ColistW A

  program : Colist A → ColistP A
  program []       = []
  program (x ∷ xs) = x ∷ ♯ program (♭ xs)

  mutual

    _⋎W_ : ColistW A → ColistP A → ColistW A
    []       ⋎W ys = whnf ys
    (x ∷ xs) ⋎W ys = x ∷ (ys ⋎ xs)

    whnf : ColistP A → ColistW A
    whnf []        = []
    whnf (x ∷ xs)  = x ∷ ♭ xs
    whnf (xs ⋎ ys) = whnf xs ⋎W ys

  mutual

    ⟦_⟧P : ColistP A → Colist A
    ⟦ xs ⟧P = ⟦ whnf xs ⟧W

    ⟦_⟧W : ColistW A → Colist A
    ⟦ [] ⟧W     = []
    ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P

  mutual

    ⋎-homP : ∀ (xs : ColistP A) {ys} → ⟦ xs ⋎ ys ⟧P ≈ ⟦ xs ⟧P Colist.⋎ ⟦ ys ⟧P
    ⋎-homP xs = ⋎-homW (whnf xs) _

    ⋎-homW : ∀ (xs : ColistW A) ys → ⟦ xs ⋎W ys ⟧W ≈ ⟦ xs ⟧W Colist.⋎ ⟦ ys ⟧P
    ⋎-homW (x ∷ xs) ys = x ∷ ♯ ⋎-homP ys
    ⋎-homW []       ys = begin ⟦ ys ⟧P ∎
      where open ≈-Reasoning

  ⟦program⟧P : ∀ (xs : Colist A) → ⟦ program xs ⟧P ≈ xs
  ⟦program⟧P []       = []
  ⟦program⟧P (x ∷ xs) = x ∷ ♯ ⟦program⟧P (♭ xs)

  Any-⋎P : ∀ xs {ys} →
           Any P ⟦ program xs ⋎ ys ⟧P ↔ (Any P xs ⊎ Any P ⟦ ys ⟧P)
  Any-⋎P {P = P} xs {ys} =
    Any P ⟦ program xs ⋎ ys ⟧P                ↔⟨ Any-cong ↔-refl (⋎-homP (program xs)) ⟩
    Any P (⟦ program xs ⟧P Colist.⋎ ⟦ ys ⟧P)  ↔⟨ Any-⋎ _ ⟩
    (Any P ⟦ program xs ⟧P ⊎ Any P ⟦ ys ⟧P)   ↔⟨ Any-cong ↔-refl (⟦program⟧P _) ⊎-cong (_ ∎) ⟩
    (Any P xs ⊎ Any P ⟦ ys ⟧P)                ∎
    where open Related.EquationalReasoning

  index-Any-⋎P :
    ∀ xs {ys} (p : Any P ⟦ program xs ⋎ ys ⟧P) →
    index p ≥′ [ index , index ]′ (Inverse.to (Any-⋎P xs) p)
  index-Any-⋎P xs p
    with       Any-resp      id  (⋎-homW (whnf (program xs)) _) p
       | index-Any-resp {f = id} (⋎-homW (whnf (program xs)) _) p
  index-Any-⋎P xs p | q | q≡p
    with Inverse.to (Any-⋎ ⟦ program xs ⟧P)  q
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

  merge′ : Colist (A × Colist A) → ColistP A
  merge′ []               = []
  merge′ ((x , xs) ∷ xss) = x ∷ ♯ (program xs ⋎ merge′ (♭ xss))

merge : Colist (A × Colist A) → Colist A
merge xss = ⟦ merge′ xss ⟧P

------------------------------------------------------------------------
-- Any lemma for merge.

Any-merge : ∀ xss → Any P (merge xss) ↔ Any (λ { (x , xs) → P x ⊎ Any P xs }) xss
Any-merge {P = P} xss = mk↔ₛ′ (proj₁ ∘ to xss) from to∘from (proj₂ ∘ to xss)
  where
  open ≡-Reasoning

  -- The from function.

  Q = λ { (x , xs) → P x ⊎ Any P xs }

  from : ∀ {xss} → Any Q xss → Any P (merge xss)
  from (here (inj₁ p))        = here p
  from (here (inj₂ p))        = there (Inverse.from (Any-⋎P _)  (inj₁ p))
  from (there {x = _ , xs} p) = there (Inverse.from (Any-⋎P xs) (inj₂ (from p)))

  -- The from function is injective.

  from-injective : ∀ {xss} (p₁ p₂ : Any Q xss) →
                   from p₁ ≡ from p₂ → p₁ ≡ p₂
  from-injective (here (inj₁ p))  (here (inj₁ .p)) refl = refl
  from-injective (here (inj₂ p₁)) (here (inj₂ p₂)) eq     =
    cong (here ∘ inj₂) $
    inj₁-injective $
    Injection.injective (↔⇒↣ (↔-sym (Any-⋎P _))) $
    there-injective eq
  from-injective (here (inj₂ p₁)) (there p₂) eq with
    Injection.injective (↔⇒↣ (↔-sym (Any-⋎P _)))
                        {x = inj₁ p₁} {y = inj₂ (from p₂)}
                        (there-injective eq)
  ... | ()
  from-injective (there p₁) (here (inj₂ p₂)) eq with
    Injection.injective (↔⇒↣ (↔-sym (Any-⋎P _)))
                           {x = inj₂ (from p₁)} {y = inj₁ p₂}
                           (there-injective eq)
  ... | ()
  from-injective (there {x = _ , xs} p₁) (there p₂) eq =
    cong there $
    from-injective p₁ p₂ $
    inj₂-injective $
    Injection.injective (↔⇒↣ (↔-sym (Any-⋎P xs))) $
    there-injective eq
  -- The to function (defined as a right inverse of from).

  Input = ∃ λ xss → Any P (merge xss)

  InputPred : Input → Set _
  InputPred (xss , p) = ∃ λ (q : Any Q xss) → from q ≡ p

  to : ∀ xss p → InputPred (xss , p)
  to xss p =
    WF.All.wfRec (On.wellFounded size <′-wellFounded) _
                 InputPred step (xss , p)
    where
    size : Input → ℕ
    size (_ , p) = index p

    step : ∀ p → WF.WfRec (_<′_ on size) InputPred p → InputPred p
    step ([]             , ())      rec
    step ((x , xs) ∷ xss , here  p) rec = here (inj₁ p) , refl
    step ((x , xs) ∷ xss , there p) rec
      with Inverse.to (Any-⋎P xs) p
         | Inverse.strictlyInverseʳ (Any-⋎P xs) p
         | index-Any-⋎P xs p
    ... | inj₁ q | refl | _   = here (inj₂ q) , refl
    ... | inj₂ q | refl | q≤p =
      Product.map there
               (cong (there ∘ (Inverse.from (Any-⋎P xs)) ∘ inj₂))
               (rec (s≤′s q≤p))

  to∘from = λ p → from-injective _ _ (proj₂ (to xss (from p)))

-- Every member of xss is a member of merge xss, and vice versa (with
-- equal multiplicities).

∈-merge : ∀ {y : A} xss → y ∈ merge xss ↔ ∃₂ λ x xs → (x , xs) ∈ xss × (y ≡ x ⊎ y ∈ xs)
∈-merge {y = y} xss =
  y ∈ merge xss                                           ↔⟨ Any-merge _ ⟩
  Any (λ { (x , xs) → y ≡ x ⊎ y ∈ xs }) xss               ↔⟨ Any-∈ ⟩
  (∃ λ { (x , xs) → (x , xs) ∈ xss × (y ≡ x ⊎ y ∈ xs) })  ↔⟨ Σ-assoc ⟩
  (∃₂ λ x xs → (x , xs) ∈ xss × (y ≡ x ⊎ y ∈ xs))         ∎
  where open Related.EquationalReasoning
