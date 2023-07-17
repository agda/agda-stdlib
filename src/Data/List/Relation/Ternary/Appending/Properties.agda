------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the generalised view of appending two lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Ternary.Appending.Properties where

open import Data.List.Base using (List; [])
open import Data.List.Relation.Ternary.Appending
open import Data.List.Relation.Binary.Pointwise as Pw using (Pointwise; []; _∷_)
open import Data.Product.Base as Σ using (∃-syntax; _×_; _,_)
open import Function.Base using (id)
open import Level using (Level)
open import Relation.Binary using (REL; Rel; Trans)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

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
    R : REL B C r
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

module _ {a b c x y p l r p′ l′ r′}
         {A : Set a} {B : Set b} {C : Set c} {X : Set x} {Y : Set y}
         {P : REL A X p} {L : REL X C l} {R : REL B C r}
         {P′ : REL Y C p′} {L′ : REL A Y l′} {R′ : REL B Y r′}
         where

  module _ (f : ∀ {b c} → R b c → ∃[ y ] R′ b y × P′ y c)
           (g : ∀ {a c} → ∃[ x ] P a x × L x c → ∃[ y ] L′ a y × P′ y c)
           where

    through→ : ∀ {as bs cs} →
      ∃[ xs ] Pointwise P as xs × Appending L R xs bs cs →
      ∃[ ys ] Appending L′ R′ as bs ys × Pointwise P′ ys cs
    through→ (_ , [] , []++ rs) =
      let _ , rs′ , ps′ = Pw.unzip (Pw.map f rs) in
      _ , []++ rs′ , ps′
    through→ (_ , p ∷ ps , l ∷ lrs) =
      let _ , l′ , p′ = g (_ , p , l) in
      Σ.map _ (Σ.map (l′ ∷_) (p′ ∷_)) (through→ (_ , ps , lrs))

  module _ (f : ∀ {b c} → ∃[ y ] R′ b y × P′ y c → R b c)
           (g : ∀ {a c} → ∃[ y ] L′ a y × P′ y c → ∃[ x ] P a x × L x c)
           where

    through← : ∀ {as bs cs} →
      ∃[ ys ] Appending L′ R′ as bs ys × Pointwise P′ ys cs →
      ∃[ xs ] Pointwise P as xs × Appending L R xs bs cs
    through← (_ , []++ rs′ , ps′) =
      _ , [] , []++ (Pw.transitive (λ r′ p′ → f (_ , r′ , p′)) rs′ ps′)
    through← (_ , l′ ∷ lrs′ , p′ ∷ ps′) =
      let _ , p , l = g (_ , l′ , p′) in
      Σ.map _ (Σ.map (p ∷_) (l ∷_)) (through← (_ , lrs′ , ps′))

module _ {a b c d x y l m r s l′ m′ r′ s′}
         {A : Set a} {B : Set b} {C : Set c} {D : Set d} {X : Set x} {Y : Set y}
         {L : REL A X l} {R : REL B X r} {L′ : REL X D l′} {R′ : REL C D r′}
         {M : REL B Y m} {S : REL C Y s} {M′ : REL A D m′} {S′ : REL Y D s′}
         where

  module _ (f : ∀ {c d} → R′ c d → ∃[ y ] S c y × S′ y d)
           (g : ∀ {b d} → ∃[ x ] R b x × L′ x d → ∃[ y ] M b y × S′ y d)
           (h : ∀ {a d} → ∃[ x ] L a x × L′ x d → M′ a d)
           where

    assoc→ : ∀ {as bs cs ds} →
      ∃[ xs ] Appending L R as bs xs × Appending L′ R′ xs cs ds →
      ∃[ ys ] Appending M S bs cs ys × Appending M′ S′ as ys ds
    assoc→ (_ , []++ rs , lrs′) =
      let _ , mss , ss′ = through→ f g (_ , rs , lrs′) in
      _ , mss , []++ ss′
    assoc→ (_ , l ∷ lrs , l′ ∷ lrs′) =
      Σ.map id (Σ.map id (h (_ , l , l′) ∷_)) (assoc→ (_ , lrs , lrs′))

  module _ (f : ∀ {c d} → ∃[ y ] S c y × S′ y d → R′ c d)
           (g : ∀ {b d} → ∃[ y ] M b y × S′ y d → ∃[ x ] R b x × L′ x d)
           (h : ∀ {a d} → M′ a d → ∃[ x ] L a x × L′ x d)
           where

    assoc← : ∀ {as bs cs ds} →
      ∃[ ys ] Appending M S bs cs ys × Appending M′ S′ as ys ds →
      ∃[ xs ] Appending L R as bs xs × Appending L′ R′ xs cs ds
    assoc← (_ , mss , []++ ss′) =
      let _ , rs , lrs′ = through← f g (_ , mss , ss′) in
      _ , []++ rs , lrs′
    assoc← (_ , mss , m′ ∷ mss′) =
      let _ , l , l′ = h m′ in
      Σ.map _ (Σ.map (l ∷_) (l′ ∷_)) (assoc← (_ , mss , mss′))
