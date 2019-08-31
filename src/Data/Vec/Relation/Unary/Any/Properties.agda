------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of vector's Any
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Unary.Any.Properties where

open import Data.Nat using (suc; zero)
open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.Any as List
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Function.Propositional using (_⊎-cong_)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Vec hiding (here; there)
open import Data.Vec.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Vec.Membership.Propositional
  using (_∈_; mapWith∈; find; lose)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; []; _∷_)
open import Function.Core
open import Function.Inverse using (_↔_; inverse)
  renaming (_∘_ to _∘↔_; id to id↔)
open import Level using (Level)
open import Relation.Nullary using (¬_)
open import Relation.Unary hiding (_∈_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_; refl)

private
  variable
    a b p q r ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Equality properties

module _ {P : Pred A p} {_≈_ : Rel A ℓ} where

  lift-resp : ∀ {n} → P Respects _≈_ → (Any P {n}) Respects (Pointwise _≈_)
  lift-resp resp (x∼y ∷ xs∼ys) (here px)   = here (resp x∼y px)
  lift-resp resp (x∼y ∷ xs∼ys) (there pxs) = there (lift-resp resp xs∼ys pxs)

module _ {P : Pred A p} where

  here-injective : ∀ {n x xs} {p q : P x} →
                   here {P = P} {n = n} {xs = xs} p ≡ here q → p ≡ q
  here-injective refl = refl

  there-injective : ∀ {n x xs} {p q : Any P xs} →
                    there {n = n} {x = x} p ≡ there q → p ≡ q
  there-injective refl = refl

------------------------------------------------------------------------
-- Misc

  ¬Any[] : ¬ Any P []
  ¬Any[] ()

  lookup-index : ∀ {m} {xs : Vec A m} (p : Any P xs) →
                 P (lookup xs (Any.index p))
  lookup-index (here px) = px
  lookup-index (there p) = lookup-index p

------------------------------------------------------------------------
-- Convert from/to List.Any

  fromList⁺ : ∀ {xs} → List.Any P xs → Any P (fromList xs)
  fromList⁺ (List.here px) = here px
  fromList⁺ (List.there v) = there (fromList⁺ v)

  fromList⁻ : ∀ {xs} → Any P (fromList xs) → List.Any P xs
  fromList⁻ {x ∷ xs} (here px)   = List.here px
  fromList⁻ {x ∷ xs} (there pxs) = List.there (fromList⁻ pxs)

  toList⁺ : ∀ {n} {xs : Vec A n} → Any P xs → List.Any P (toList xs)
  toList⁺ (here px) = List.here px
  toList⁺ (there v) = List.there (toList⁺ v)

  toList⁻ : ∀ {n} {xs : Vec A n} → List.Any P (toList xs) → Any P xs
  toList⁻ {xs = x ∷ xs} (List.here px)   = here px
  toList⁻ {xs = x ∷ xs} (List.there pxs) = there (toList⁻ pxs)

------------------------------------------------------------------------
-- map

map-id : ∀ {P : Pred A p} (f : P ⊆ P) {n xs} →
         (∀ {x} (p : P x) → f p ≡ p) →
         (p : Any P {n} xs) → Any.map f p ≡ p
map-id f hyp (here  p) = P.cong here (hyp p)
map-id f hyp (there p) = P.cong there $ map-id f hyp p

map-∘ : ∀ {P : Pred A p} {Q : A → Set q} {R : A → Set r}
        (f : Q ⊆ R) (g : P ⊆ Q)
        {n xs} (p : Any P {n} xs) →
        Any.map (f ∘ g) p ≡ Any.map f (Any.map g p)
map-∘ f g (here  p) = refl
map-∘ f g (there p) = P.cong there $ map-∘ f g p

------------------------------------------------------------------------
-- Swapping

module _ {P : A → B → Set ℓ} where

  swap : ∀ {n m} {xs : Vec A n} {ys : Vec B m} →
         Any (λ x → Any (P x) ys) xs →
         Any (λ y → Any (flip P y) xs) ys
  swap (here  pys)  = Any.map here pys
  swap (there pxys) = Any.map there (swap pxys)

  swap-there : ∀ {n m x xs ys} → (any : Any (λ x → Any (P x) {n} ys) {m} xs) →
               swap (Any.map (there {x = x}) any) ≡ there (swap any)
  swap-there (here  pys)  = refl
  swap-there (there pxys) = P.cong (Any.map there) (swap-there pxys)

module _ {P : A → B → Set ℓ} where

  swap-invol : ∀ {n m} {xs : Vec A n} {ys : Vec B m} →
               (any : Any (λ x → Any (P x) ys) xs) →
               swap (swap any) ≡ any
  swap-invol (here (here _)) = refl
  swap-invol (here (there pys)) = P.cong (Any.map there) (swap-invol (here pys))
  swap-invol (there pxys) = P.trans (swap-there (swap pxys))
                          $ P.cong there (swap-invol pxys)

module _ {P : A → B → Set ℓ} where

  swap↔ : ∀ {n m} {xs : Vec A n} {ys : Vec B m} →
          Any (λ x → Any (P x) ys) xs ↔ Any (λ y → Any (flip P y) xs) ys
  swap↔ = inverse swap swap swap-invol swap-invol

------------------------------------------------------------------------
-- Lemmas relating Any to ⊥

⊥↔Any⊥ : ∀ {n} {xs : Vec A n} → ⊥ ↔ Any (const ⊥) xs
⊥↔Any⊥ = inverse (λ ()) (λ p → from p) (λ ()) (λ p → from p)
  where
  from : ∀ {n xs} → Any (const ⊥) {n} xs → ∀ {b} {B : Set b} → B
  from (there p) = from p

⊥↔Any[] : ∀ {P : Pred A p} → ⊥ ↔ Any P []
⊥↔Any[] = inverse (λ()) (λ()) (λ()) (λ())

------------------------------------------------------------------------
-- Sums commute with Any

module _ {P : Pred A p} {Q : A → Set q} where

  Any-⊎⁺ : ∀ {n} {xs : Vec A n} → Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
  Any-⊎⁺ = [ Any.map inj₁ , Any.map inj₂ ]′

  Any-⊎⁻ : ∀ {n} {xs : Vec A n} → Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs
  Any-⊎⁻ (here (inj₁ p)) = inj₁ (here p)
  Any-⊎⁻ (here (inj₂ q)) = inj₂ (here q)
  Any-⊎⁻ (there p)       = Sum.map there there (Any-⊎⁻ p)

  ⊎↔ : ∀ {n} {xs : Vec A n} → (Any P xs ⊎ Any Q xs) ↔ Any (λ x → P x ⊎ Q x) xs
  ⊎↔ = inverse Any-⊎⁺ Any-⊎⁻ from∘to to∘from
    where
    from∘to : ∀ {n} {xs : Vec A n} (p : Any P xs ⊎ Any Q xs) → Any-⊎⁻ (Any-⊎⁺ p) ≡ p
    from∘to (inj₁ (here  p)) = refl
    from∘to (inj₁ (there p)) rewrite from∘to (inj₁ p) = refl
    from∘to (inj₂ (here  q)) = refl
    from∘to (inj₂ (there q)) rewrite from∘to (inj₂ q) = refl

    to∘from : ∀ {n} {xs : Vec A n} (p : Any (λ x → P x ⊎ Q x) xs) →
              Any-⊎⁺ (Any-⊎⁻ p) ≡ p
    to∘from (here (inj₁ p)) = refl
    to∘from (here (inj₂ q)) = refl
    to∘from (there p) with Any-⊎⁻ p | to∘from p
    to∘from (there .(Any.map inj₁ p)) | inj₁ p | refl = refl
    to∘from (there .(Any.map inj₂ q)) | inj₂ q | refl = refl

------------------------------------------------------------------------
-- Products "commute" with Any.

module _ {P : Pred A p} {Q : Pred B q} where

  Any-×⁺ : ∀ {n m} {xs : Vec A n} {ys : Vec B m} → Any P xs × Any Q ys →
           Any (λ x → Any (λ y → P x × Q y) ys) xs
  Any-×⁺ (p , q) = Any.map (λ p → Any.map (p ,_) q) p

  Any-×⁻ : ∀ {n m} {xs : Vec A n} {ys : Vec B m} →
           Any (λ x → Any (λ y → P x × Q y) ys) xs →
           Any P xs × Any Q ys
  Any-×⁻ pq with find pq
  ... | x , x∈xs , pxys with find pxys
  ...   | y , y∈ys , px , py = lose x∈xs px , lose y∈ys py

------------------------------------------------------------------------
-- Invertible introduction (⁺) and elimination (⁻) rules for various
-- vector functions

------------------------------------------------------------------------
-- Singleton ([_])

module _ {P : Pred A p} where

  singleton⁺ : ∀ {x} → P x → Any P [ x ]
  singleton⁺ Px = here Px

  singleton⁻ : ∀ {x} → Any P [ x ] → P x
  singleton⁻ (here Px) = Px

  singleton⁺∘singleton⁻ : ∀ {x} (p : Any P [ x ]) →
                          singleton⁺ (singleton⁻ p) ≡ p
  singleton⁺∘singleton⁻ (here px) = refl

  singleton⁻∘singleton⁺ : ∀ {x} (p : P x) →
                          singleton⁻ (singleton⁺ p) ≡ p
  singleton⁻∘singleton⁺ p = refl

  singleton↔ : ∀ {x} → P x ↔ Any P [ x ]
  singleton↔ = inverse singleton⁺ singleton⁻ singleton⁻∘singleton⁺ singleton⁺∘singleton⁻

------------------------------------------------------------------------
-- map

module _ {f : A → B} where

  map⁺ : ∀ {P : Pred B p} {n} {xs : Vec A n} →
         Any (P ∘ f) xs → Any P (map f xs)
  map⁺ (here p)  = here p
  map⁺ (there p) = there $ map⁺ p

  map⁻ : ∀ {P : Pred B p} {n} {xs : Vec A n} →
         Any P (map f xs) → Any (P ∘ f) xs
  map⁻ {xs = x ∷ xs} (here p)  = here p
  map⁻ {xs = x ∷ xs} (there p) = there $ map⁻ p

  map⁺∘map⁻ : ∀ {P : Pred B p} {n} {xs : Vec A n} →
              (p : Any P (map f xs)) → map⁺ (map⁻ p) ≡ p
  map⁺∘map⁻ {xs = x ∷ xs} (here  p) = refl
  map⁺∘map⁻ {xs = x ∷ xs} (there p) = P.cong there (map⁺∘map⁻ p)

  map⁻∘map⁺ : ∀ (P : Pred B p) {n} {xs : Vec A n} →
              (p : Any (P ∘ f) xs) → map⁻ {P = P} (map⁺ p) ≡ p
  map⁻∘map⁺ P (here  p) = refl
  map⁻∘map⁺ P (there p) = P.cong there (map⁻∘map⁺ P p)

  map↔ : ∀ {P : Pred B p} {n} {xs : Vec A n} →
         Any (P ∘ f) xs ↔ Any P (map f xs)
  map↔ = inverse map⁺ map⁻ (map⁻∘map⁺ _) map⁺∘map⁻

------------------------------------------------------------------------
-- _++_

module _ {P : Pred A p} where

  ++⁺ˡ : ∀ {n m} {xs : Vec A n} {ys : Vec A m} → Any P xs → Any P (xs ++ ys)
  ++⁺ˡ (here p)  = here p
  ++⁺ˡ (there p) = there (++⁺ˡ p)

  ++⁺ʳ : ∀ {n m} (xs : Vec A n) {ys : Vec A m} → Any P ys → Any P (xs ++ ys)
  ++⁺ʳ []       p = p
  ++⁺ʳ (x ∷ xs) p = there (++⁺ʳ xs p)

  ++⁻ : ∀ {n m} (xs : Vec A n) {ys : Vec A m} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁻ []       p         = inj₂ p
  ++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
  ++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

  ++⁺∘++⁻ : ∀ {n m} (xs : Vec A n) {ys : Vec A m} (p : Any P (xs ++ ys)) →
           [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs p) ≡ p
  ++⁺∘++⁻ []       p         = refl
  ++⁺∘++⁻ (x ∷ xs) (here  p) = refl
  ++⁺∘++⁻ (x ∷ xs) (there p) with ++⁻ xs p | ++⁺∘++⁻ xs p
  ++⁺∘++⁻ (x ∷ xs) (there p) | inj₁ p′ | ih = P.cong there ih
  ++⁺∘++⁻ (x ∷ xs) (there p) | inj₂ p′ | ih = P.cong there ih

  ++⁻∘++⁺ : ∀ {n m} (xs : Vec A n) {ys : Vec A m} (p : Any P xs ⊎ Any P ys) →
            ++⁻ xs ([ ++⁺ˡ , ++⁺ʳ xs ]′ p) ≡ p
  ++⁻∘++⁺ []            (inj₂ p)         = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₁ (here  p)) = refl
  ++⁻∘++⁺ (x ∷ xs) {ys} (inj₁ (there p)) rewrite ++⁻∘++⁺ xs {ys} (inj₁ p) = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₂ p)         rewrite ++⁻∘++⁺ xs      (inj₂ p) = refl

  ++↔ : ∀ {n m} {xs : Vec A n} {ys : Vec A m} →
        (Any P xs ⊎ Any P ys) ↔ Any P (xs ++ ys)
  ++↔ {xs = xs} = inverse [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs) (++⁻∘++⁺ xs) (++⁺∘++⁻ xs)

  ++-comm : ∀ {n m} (xs : Vec A n) (ys : Vec A m) →
            Any P (xs ++ ys) → Any P (ys ++ xs)
  ++-comm xs ys = [ ++⁺ʳ ys , ++⁺ˡ ]′ ∘ ++⁻ xs

  ++-comm∘++-comm : ∀ {n m} (xs : Vec A n) {ys : Vec A m} (p : Any P (xs ++ ys)) →
                    ++-comm ys xs (++-comm xs ys p) ≡ p
  ++-comm∘++-comm [] {ys} p
    rewrite ++⁻∘++⁺ ys {ys = []} (inj₁ p) = refl
  ++-comm∘++-comm (x ∷ xs) {ys} (here p)
    rewrite ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₂ (here p)) = refl
  ++-comm∘++-comm (x ∷ xs)      (there p) with ++⁻ xs p | ++-comm∘++-comm xs p
  ++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ʳ ys p))))
    | inj₁ p | refl
    rewrite ++⁻∘++⁺ ys (inj₂                 p)
            | ++⁻∘++⁺ ys (inj₂ $ there {x = x} p) = refl
  ++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ˡ p))))
    | inj₂ p | refl
    rewrite ++⁻∘++⁺ ys {ys =     xs} (inj₁ p)
            | ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₁ p) = refl

  ++↔++ : ∀ {n m} (xs : Vec A n) (ys : Vec A m) → Any P (xs ++ ys) ↔ Any P (ys ++ xs)
  ++↔++ xs ys = inverse (++-comm xs ys) (++-comm ys xs)
                        (++-comm∘++-comm xs) (++-comm∘++-comm ys)

  ++-insert : ∀ {n m x} (xs : Vec A n) {ys : Vec A m} → P x → Any P (xs ++ [ x ] ++ ys)
  ++-insert xs Px = ++⁺ʳ xs (++⁺ˡ (singleton⁺ Px))

------------------------------------------------------------------------
-- concat

module _ {P : Pred A p} where

  concat⁺ : ∀ {n m} {xss : Vec (Vec A n) m} → Any (Any P) xss → Any P (concat xss)
  concat⁺ (here p)           = ++⁺ˡ p
  concat⁺ (there {x = xs} p) = ++⁺ʳ xs (concat⁺ p)

  concat⁻ : ∀ {n m} (xss : Vec (Vec A n) m) → Any P (concat xss) → Any (Any P) xss
  concat⁻ (xs ∷ xss) p = [ here , there ∘ concat⁻ xss ]′ (++⁻ xs p)

  concat⁻∘++⁺ˡ : ∀ {n m xs} (xss : Vec (Vec A n) m) (p : Any P xs) →
                concat⁻ (xs ∷ xss) (++⁺ˡ p) ≡ here p
  concat⁻∘++⁺ˡ xss p rewrite ++⁻∘++⁺ _ {concat xss} (inj₁ p) = refl

  concat⁻∘++⁺ʳ : ∀ {n m} xs (xss : Vec (Vec A n) m) (p : Any P (concat xss)) →
                concat⁻ (xs ∷ xss) (++⁺ʳ xs p) ≡ there (concat⁻ xss p)
  concat⁻∘++⁺ʳ xs xss p rewrite ++⁻∘++⁺ xs (inj₂ p) = refl

  concat⁺∘concat⁻ : ∀ {n m} (xss : Vec (Vec A n) m) (p : Any P (concat xss)) →
                   concat⁺ (concat⁻ xss p) ≡ p
  concat⁺∘concat⁻ (xs ∷ xss) p  with ++⁻ xs p | P.inspect (++⁻ xs) p
  ... | inj₁ pxs | P.[ p=inj₁ ]
    = P.trans (P.cong [ ++⁺ˡ , ++⁺ʳ xs ]′ (P.sym p=inj₁))
    $ ++⁺∘++⁻ xs p
  ... | inj₂ pxss | P.[ p=inj₂ ] rewrite concat⁺∘concat⁻ xss pxss
    = P.trans (P.cong [ ++⁺ˡ , ++⁺ʳ xs ]′ (P.sym p=inj₂))
    $ ++⁺∘++⁻ xs p

  concat⁻∘concat⁺ : ∀ {n m} {xss : Vec (Vec A n) m} (p : Any (Any P) xss) →
                    concat⁻ xss (concat⁺ p) ≡ p
  concat⁻∘concat⁺ {xss = xs ∷ xss} (here p)
    rewrite ++⁻∘++⁺ xs {concat xss} (inj₁ p) = refl
  concat⁻∘concat⁺ {xss = xs ∷ xss} (there p)
    rewrite ++⁻∘++⁺ xs {concat xss} (inj₂ (concat⁺ p))
            | concat⁻∘concat⁺ p = refl

  concat↔ : ∀ {n m} {xss : Vec (Vec A n) m} → Any (Any P) xss ↔ Any P (concat xss)
  concat↔ {xss = xss} = inverse concat⁺ (concat⁻ xss) concat⁻∘concat⁺ (concat⁺∘concat⁻ xss)

------------------------------------------------------------------------
-- tabulate

module _ {P : Pred A p} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} i → P (f i) → Any P (tabulate f)
  tabulate⁺ zero    p = here p
  tabulate⁺ (suc i) p = there (tabulate⁺ i p)

  tabulate⁻ : ∀ {n} {f : Fin n → A} →
              Any P (tabulate f) → ∃ λ i → P (f i)
  tabulate⁻ {suc n} (here p)  = zero , p
  tabulate⁻ {suc n} (there p) = Prod.map suc id (tabulate⁻ p)

------------------------------------------------------------------------
-- mapWith∈

module _ {P : Pred B p} where

  mapWith∈⁺ : ∀ {n} {xs : Vec A n} (f : ∀ {x} → x ∈ xs → B) →
              (∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) →
              Any P (mapWith∈ xs f)
  mapWith∈⁺ f (_ , here refl  , p) = here p
  mapWith∈⁺ f (_ , there x∈xs , p) =
    there $ mapWith∈⁺ (f ∘ there) (_ , x∈xs , p)

  mapWith∈⁻ : ∀ {n} (xs : Vec A n) (f : ∀ {x} → x ∈ xs → B) →
              Any P (mapWith∈ xs f) →
              ∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)
  mapWith∈⁻ (y ∷ xs) f (here  p) = (y , here refl , p)
  mapWith∈⁻ (y ∷ xs) f (there p) =
    Prod.map id (Prod.map there id) $ mapWith∈⁻ xs (f ∘ there) p

  mapWith∈↔ : ∀ {n} {xs : Vec A n} {f : ∀ {x} → x ∈ xs → B} →
    (∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) ↔ Any P (mapWith∈ xs f)
  mapWith∈↔ = inverse (mapWith∈⁺ _) (mapWith∈⁻ _ _) (from∘to _) (to∘from _ _)
    where
    from∘to : ∀ {n} {xs : Vec A n} (f : ∀ {x} → x ∈ xs → B)
              (p : ∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) →
              mapWith∈⁻ xs f (mapWith∈⁺ f p) ≡ p
    from∘to f (_ , here refl  , p) = refl
    from∘to f (_ , there x∈xs , p)
      rewrite from∘to (f ∘ there) (_ , x∈xs , p) = refl

    to∘from : ∀ {n} (xs : Vec A n) (f : ∀ {x} → x ∈ xs → B)
              (p : Any P (mapWith∈ xs f)) →
              mapWith∈⁺ f (mapWith∈⁻ xs f p) ≡ p
    to∘from (y ∷ xs) f (here  p) = refl
    to∘from (y ∷ xs) f (there p) =
      P.cong there $ to∘from xs (f ∘ there) p

------------------------------------------------------------------------
-- _∷_

∷↔ : ∀ {n} (P : Pred A p) {x} {xs : Vec A n} →
     (P x ⊎ Any P xs) ↔ Any P (x ∷ xs)
∷↔ P {x} {xs} = ++↔ ∘↔ (singleton↔ ⊎-cong id↔)

------------------------------------------------------------------------
-- _>>=_

module _ {A B : Set a} {P : Pred B p} {m} {f : A → Vec B m} where

  >>=↔ : ∀ {n} {xs : Vec A n} → Any (Any P ∘ f) xs ↔ Any P (xs >>= f)
  >>=↔ = concat↔ ∘↔ map↔
