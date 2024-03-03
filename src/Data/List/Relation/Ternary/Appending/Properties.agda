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
open import Data.Product.Base as Product using (∃-syntax; _×_; _,_)
open import Function.Base using (id)
open import Data.List.Relation.Binary.Pointwise.Base as Pw using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Properties as Pw using (transitive)
open import Level using (Level)
open import Relation.Binary.Core using (REL; Rel; _⇒_)
open import Relation.Binary.Definitions using (Trans)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Binary.Construct.Composition using (_;_)

private
  variable
    a ℓ l r : Level
    A A′ B B′ C C′ D D′ : Set a
    R S T U V W X Y : REL A B ℓ
    as bs cs ds : List A

module _  (RST : Trans R S T) (USV : Trans U S V) where

  respʳ-≋ : Appending R U as bs cs → Pointwise S cs ds → Appending T V as bs ds
  respʳ-≋ ([]++ rs) es       = []++ Pw.transitive USV rs es
  respʳ-≋ (l ∷ lrs) (e ∷ es) = RST l e ∷ respʳ-≋ lrs es

module _  {T : REL A B l} (RST : Trans R S T)
          {W : REL A B r} (ERW : Trans U V W)
          where

  respˡ-≋ : ∀ {as′ bs′} → Pointwise R as′ as → Pointwise U bs′ bs →
            Appending S V as bs cs → Appending T W as′ bs′ cs
  respˡ-≋ []         esʳ ([]++ rs) = []++ Pw.transitive ERW esʳ rs
  respˡ-≋ (eˡ ∷ esˡ) esʳ (l ∷ lrs) = RST eˡ l ∷ respˡ-≋ esˡ esʳ lrs

conicalˡ : Appending R S as bs [] → as ≡ []
conicalˡ ([]++ rs) = refl

conicalʳ : Appending R S as bs [] → bs ≡ []
conicalʳ ([]++ []) = refl

through→ :
  (R ⇒ (S ; T)) →
  ((U ; V) ⇒ (W ; T)) →
  ∃[ xs ] Pointwise U as xs × Appending V R xs bs cs →
  ∃[ ys ] Appending W S as bs ys × Pointwise T ys cs
through→ f g (_ , [] , []++ rs) =
  let _ , rs′ , ps′ = Pw.unzip (Pw.map f rs) in
  _ , []++ rs′ , ps′
through→ f g (_ , p ∷ ps , l ∷ lrs) =
  let _ , l′ , p′ = g (_ , p , l) in
  Product.map _ (Product.map (l′ ∷_) (p′ ∷_)) (through→ f g (_ , ps , lrs))

through← :
  ((R ; S) ⇒ T) →
  ((U ; S) ⇒ (V ; W)) →
  ∃[ ys ] Appending U R as bs ys × Pointwise S ys cs →
  ∃[ xs ] Pointwise V as xs × Appending W T xs bs cs
through← f g (_ , []++ rs′ , ps′) =
  _ , [] , []++ (Pw.transitive (λ r′ p′ → f (_ , r′ , p′)) rs′ ps′)
through← f g (_ , l′ ∷ lrs′ , p′ ∷ ps′) =
  let _ , p , l = g (_ , l′ , p′) in
  Product.map _ (Product.map (p ∷_) (l ∷_)) (through← f g (_ , lrs′ , ps′))

assoc→ :
  (R ⇒ (S ; T)) →
  ((U ; V) ⇒ (W ; T)) →
  ((Y ; V) ⇒ X) →
  ∃[ xs ] Appending Y U as bs xs × Appending V R xs cs ds →
  ∃[ ys ] Appending W S bs cs ys × Appending X T as ys ds
assoc→ f g h (_ , []++ rs , lrs′) =
  let _ , mss , ss′ = through→ f g (_ , rs , lrs′) in
  _ , mss , []++ ss′
assoc→ f g h (_ , l ∷ lrs , l′ ∷ lrs′) =
  Product.map₂ (Product.map₂ (h (_ , l , l′) ∷_)) (assoc→ f g h (_ , lrs , lrs′))

assoc← :
  ((S ; T) ⇒ R) →
  ((W ; T) ⇒ (U ; V)) →
  (X ⇒ (Y ; V)) →
  ∃[ ys ] Appending W S bs cs ys × Appending X T as ys ds →
  ∃[ xs ] Appending Y U as bs xs × Appending V R xs cs ds
assoc← f g h (_ , mss , []++ ss′) =
  let _ , rs , lrs′ = through← f g (_ , mss , ss′) in
  _ , []++ rs , lrs′
assoc← f g h (_ , mss , m′ ∷ mss′) =
  let _ , l , l′ = h m′ in
  Product.map _ (Product.map (l ∷_) (l′ ∷_)) (assoc← f g h (_ , mss , mss′))
