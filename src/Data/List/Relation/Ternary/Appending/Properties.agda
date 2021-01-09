------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the generalised view of appending two lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Ternary.Appending.Properties where

open import Data.List.Base using (List; [])
open import Data.List.Relation.Ternary.Appending
open import Data.List.Relation.Binary.Pointwise as Pw using (Pointwise; []; _∷_)
open import Level using (Level)
open import Relation.Binary using (REL; Rel; Trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    a a′ b b′ c c′ l r : Level
    A : Set a
    A′ : Set a′
    B : Set b
    B′ : Set b′
    C : Set c
    C′ : Set c′
    L : REL A C l
    R : REL A B r
    as : List A
    bs : List B
    cs : List C

module _  {e} {E : REL C C′ e} {L′ : REL A C′ l} {R′ : REL B C′ r}
          (LEL′ : Trans L E L′) (RER′ : Trans R E R′)
          where

  respʳ-≋ : ∀ {cs′} → Appending L R as bs cs → Pointwise E cs cs′ → Appending L′ R′ as bs cs′
  respʳ-≋ ([]++ rs) es       = []++ Pw.transitive RER′ rs es
  respʳ-≋ (l ∷ lrs) (e ∷ es) = LEL′ l e ∷ respʳ-≋ lrs es

module _  {eᴬ eᴮ} {Eᴬ : REL A′ A eᴬ} {Eᴮ : REL B′ B eᴮ}
          {L′ : REL A′ C l} (ELL′ : Trans Eᴬ L L′)
          {R′ : REL B′ C r} (ERR′ : Trans Eᴮ R R′)
          where

  respˡ-≋ : ∀ {as′ bs′} → Pointwise Eᴬ as′ as → Pointwise Eᴮ bs′ bs →
            Appending L R as bs cs → Appending L′ R′ as′ bs′ cs
  respˡ-≋ []         esʳ ([]++ rs) = []++ Pw.transitive ERR′ esʳ rs
  respˡ-≋ (eˡ ∷ esˡ) esʳ (l ∷ lrs) = ELL′ eˡ l ∷ respˡ-≋ esˡ esʳ lrs

conicalˡ : Appending L R as bs [] → as ≡ []
conicalˡ ([]++ rs) = refl

conicalʳ : Appending L R as bs [] → bs ≡ []
conicalʳ ([]++ []) = refl
