------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Any
------------------------------------------------------------------------

-- The other modules under Data.List.Any also contain properties
-- related to Any.

module Data.List.Any.Properties where

open import Category.Monad
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Bool.Properties
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List as List
open import Data.List.Categorical using (monad)
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties.Core
  using (Any↔; find∘map; map∘find; lose∘find)
open import Data.List.Relation.Pointwise
  using (Pointwise; []; _∷_)
open import Data.Nat using (zero; suc; _<_; z≤n; s≤s)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Any as MAny using (just)
open import Data.Product as Prod
  using (_×_; _,_; ∃; ∃₂; proj₁; proj₂; uncurry′)
open import Data.Product.Properties
open import Data.Product.Relation.Pointwise.NonDependent
  using (_×-cong_)
import Data.Product.Relation.Pointwise.Dependent as Σ
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Relation.Pointwise using (_⊎-cong_)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; equivalence; Equivalence)
open import Function.Inverse as Inv using (_↔_; inverse; Inverse)
open import Function.Related as Related using (Related; SK-sym)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; inspect)
open import Relation.Unary
  using (Pred; _⟨×⟩_; _⟨→⟩_) renaming (_⊆_ to _⋐_)
open import Relation.Nullary using (¬_)
open Related.EquationalReasoning

private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

------------------------------------------------------------------------
-- Equality properties

module _ {a p ℓ} {A : Set a} {P : A → Set p} {_≈_ : Rel A ℓ} where

  lift-resp : P Respects _≈_ → (Any P) Respects (Pointwise _≈_)
  lift-resp resp []            ()
  lift-resp resp (x≈y ∷ xs≈ys) (here px)   = here (resp x≈y px)
  lift-resp resp (x≈y ∷ xs≈ys) (there pxs) =
    there (lift-resp resp xs≈ys pxs)

module _ {a p} {A : Set a} {P : A → Set p} where

  here-injective : ∀ {x xs} {p q : P x} →
                   here {P = P} {xs = xs} p ≡ here q → p ≡ q
  here-injective refl = refl

  there-injective : ∀ {x xs} {p q : Any P xs} →
                    there {x = x} p ≡ there q → p ≡ q
  there-injective refl = refl

------------------------------------------------------------------------
-- Misc

module _ {a p} {A : Set a} {P : A → Set p} where

  ¬Any[] : ¬ Any P []
  ¬Any[] ()

------------------------------------------------------------------------
-- Any is a congruence

module _ {a k p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where

  Any-cong : ∀ {xs ys : List A} →
             (∀ x → Related k (P x) (Q x)) →
             Preorder._∼_ (Related.InducedPreorder₂ k {A = A} _∈_) xs ys →
             Related k (Any P xs) (Any Q ys)
  Any-cong {xs} {ys} P↔Q xs≈ys =
    Any P xs                ↔⟨ SK-sym Any↔ ⟩
    (∃ λ x → x ∈ xs × P x)  ∼⟨ Σ.cong Inv.id (xs≈ys ×-cong P↔Q _) ⟩
    (∃ λ x → x ∈ ys × Q x)  ↔⟨ Any↔ ⟩
    Any Q ys                ∎

------------------------------------------------------------------------
-- map

map-id : ∀ {a p} {A : Set a} {P : A → Set p} (f : P ⋐ P) {xs} →
         (∀ {x} (p : P x) → f p ≡ p) →
         (p : Any P xs) → Any.map f p ≡ p
map-id f hyp (here  p) = P.cong here (hyp p)
map-id f hyp (there p) = P.cong there $ map-id f hyp p

map-∘ : ∀ {a p q r}
          {A : Set a} {P : A → Set p} {Q : A → Set q} {R : A → Set r}
        (f : Q ⋐ R) (g : P ⋐ Q)
        {xs} (p : Any P xs) →
        Any.map (f ∘ g) p ≡ Any.map f (Any.map g p)
map-∘ f g (here  p) = refl
map-∘ f g (there p) = P.cong there $ map-∘ f g p

------------------------------------------------------------------------
-- Swapping

-- Nested occurrences of Any can sometimes be swapped. See also ×↔.

swap : ∀ {a b ℓ} {A : Set a} {B : Set b} {P : A → B → Set ℓ} {xs ys} →
        Any (λ x → Any (P x) ys) xs → Any (λ y → Any (flip P y) xs) ys
swap (here  pys)  = Any.map here pys
swap (there pxys) = Any.map there (swap pxys)

swap-there : ∀ {a b ℓ} {A : Set a} {B : Set b} {P : A → B → Set ℓ}
             {x xs ys} → (any : Any (λ x → Any (P x) ys) xs) →
             swap (Any.map (there {x = x}) any) ≡ there (swap any)
swap-there (here  pys)  = refl
swap-there (there pxys) = P.cong (Any.map there) (swap-there pxys)

swap-invol : ∀ {a b ℓ} {A : Set a} {B : Set b} {P : A → B → Set ℓ}
             {xs ys} → (any : Any (λ x → Any (P x) ys) xs) →
             swap (swap any) ≡ any
swap-invol (here (here px))   = refl
swap-invol (here (there pys)) =
  P.cong (Any.map there) (swap-invol (here pys))
swap-invol (there pxys)       =
  P.trans (swap-there (swap pxys)) (P.cong there (swap-invol pxys))

swap↔ : ∀ {ℓ} {A B : Set ℓ} {P : A → B → Set ℓ} {xs ys} →
       Any (λ x → Any (P x) ys) xs ↔ Any (λ y → Any (flip P y) xs) ys
swap↔ {P = P} = inverse swap swap swap-invol swap-invol

------------------------------------------------------------------------
-- Lemmas relating Any to ⊥

⊥↔Any⊥ : ∀ {a} {A : Set a} {xs : List A} → ⊥ ↔ Any (const ⊥) xs
⊥↔Any⊥ {A = A} = inverse (λ()) (λ p → from p) (λ()) (λ p → from p)
  where
  from : {xs : List A} → Any (const ⊥) xs → ∀ {b} {B : Set b} → B
  from (here ())
  from (there p) = from p

⊥↔Any[] : ∀ {a p} {A : Set a} {P : A → Set p} → ⊥ ↔ Any P []
⊥↔Any[] = inverse (λ()) (λ()) (λ()) (λ())

------------------------------------------------------------------------
-- Lemmas relating Any to ⊤

-- These introduction and elimination rules are not inverses, though.

module _ {a} {A : Set a} where

  any⁺ : ∀ (p : A → Bool) {xs} → Any (T ∘ p) xs → T (any p xs)
  any⁺ p (here  px)          = Equivalence.from T-∨ ⟨$⟩ inj₁ px
  any⁺ p (there {x = x} pxs) with p x
  ... | true  = _
  ... | false = any⁺ p pxs

  any⁻ : ∀ (p : A → Bool) xs → T (any p xs) → Any (T ∘ p) xs
  any⁻ p []       ()
  any⁻ p (x ∷ xs) px∷xs with p x | inspect p x
  any⁻ p (x ∷ xs) px∷xs | true  | P.[ eq ] = here (Equivalence.from T-≡ ⟨$⟩ eq)
  any⁻ p (x ∷ xs) px∷xs | false | _       = there (any⁻ p xs px∷xs)

  any⇔ : ∀ {p : A → Bool} {xs} → Any (T ∘ p) xs ⇔ T (any p xs)
  any⇔ = equivalence (any⁺ _) (any⁻ _ _)

------------------------------------------------------------------------
-- Sums commute with Any

module _ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} where

  Any-⊎⁺ : ∀ {xs} → Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
  Any-⊎⁺ = [ Any.map inj₁ , Any.map inj₂ ]′

  Any-⊎⁻ : ∀ {xs} → Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs
  Any-⊎⁻ (here (inj₁ p)) = inj₁ (here p)
  Any-⊎⁻ (here (inj₂ q)) = inj₂ (here q)
  Any-⊎⁻ (there p)       = Sum.map there there (Any-⊎⁻ p)

  ⊎↔ : ∀ {xs} → (Any P xs ⊎ Any Q xs) ↔ Any (λ x → P x ⊎ Q x) xs
  ⊎↔ = inverse Any-⊎⁺ Any-⊎⁻ from∘to to∘from
    where
    from∘to : ∀ {xs} (p : Any P xs ⊎ Any Q xs) → Any-⊎⁻ (Any-⊎⁺ p) ≡ p
    from∘to (inj₁ (here  p)) = refl
    from∘to (inj₁ (there p)) rewrite from∘to (inj₁ p) = refl
    from∘to (inj₂ (here  q)) = refl
    from∘to (inj₂ (there q)) rewrite from∘to (inj₂ q) = refl

    to∘from : ∀ {xs} (p : Any (λ x → P x ⊎ Q x) xs) →
              Any-⊎⁺ (Any-⊎⁻ p) ≡ p
    to∘from (here (inj₁ p)) = refl
    to∘from (here (inj₂ q)) = refl
    to∘from (there p) with Any-⊎⁻ p | to∘from p
    to∘from (there .(Any.map inj₁ p)) | inj₁ p | refl = refl
    to∘from (there .(Any.map inj₂ q)) | inj₂ q | refl = refl

------------------------------------------------------------------------
-- Products "commute" with Any.

module _ {a b p q} {A : Set a} {B : Set b}
         {P : Pred A p} {Q : Pred B q} where

  Any-×⁺ : ∀ {xs ys} → Any P xs × Any Q ys →
           Any (λ x → Any (λ y → P x × Q y) ys) xs
  Any-×⁺ (p , q) = Any.map (λ p → Any.map (λ q → (p , q)) q) p

  Any-×⁻ : ∀ {xs ys} → Any (λ x → Any (λ y → P x × Q y) ys) xs →
           Any P xs × Any Q ys
  Any-×⁻ pq with Prod.map id (Prod.map id find) (find pq)
  ... | (x , x∈xs , y , y∈ys , p , q) = (lose x∈xs p , lose y∈ys q)

  ×↔ : ∀ {xs ys} →
       (Any P xs × Any Q ys) ↔ Any (λ x → Any (λ y → P x × Q y) ys) xs
  ×↔ {xs} {ys} = inverse Any-×⁺ Any-×⁻ from∘to to∘from
    where
    from∘to : ∀ pq → Any-×⁻ (Any-×⁺ pq) ≡ pq
    from∘to (p , q) rewrite
        find∘map p (λ p → Any.map (λ q → (p , q)) q)
      | find∘map q (λ q → proj₂ (proj₂ (find p)) , q)
      | lose∘find p
      | lose∘find q
      = refl

    to∘from : ∀ pq → Any-×⁺ (Any-×⁻ pq) ≡ pq
    to∘from pq
      with find pq
        | (λ (f : (proj₁ (find pq) ≡_) ⋐ _) → map∘find pq {f})
    ... | (x , x∈xs , pq′) | lem₁
      with find pq′
        | (λ (f : (proj₁ (find pq′) ≡_) ⋐ _) → map∘find pq′ {f})
    ... | (y , y∈ys , p , q) | lem₂
      rewrite P.sym $ map-∘ {R = λ x → Any (λ y → P x × Q y) ys}
                            (λ p → Any.map (λ q → p , q) (lose y∈ys q))
                            (λ y → P.subst P y p)
                            x∈xs
              = lem₁ _ helper
      where
      helper : Any.map (λ q → p , q) (lose y∈ys q) ≡ pq′
      helper rewrite P.sym $ map-∘ (λ q → p , q)
                                   (λ y → P.subst Q y q)
                                   y∈ys
             = lem₂ _ refl

------------------------------------------------------------------------
-- Invertible introduction (⁺) and elimination (⁻) rules for various
-- list functions

------------------------------------------------------------------------
-- map

module _ {a p} {A : Set a} {P : Pred A p} where

  singleton⁺ : ∀ {x} → P x → Any P [ x ]
  singleton⁺ Px = here Px

  singleton⁻ : ∀ {x} → Any P [ x ] → P x
  singleton⁻ (here Px) = Px
  singleton⁻ (there ())

------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} {f : A → B} where

  map⁺ : ∀ {p} {P : B → Set p}  {xs} →
         Any (P ∘ f) xs → Any P (List.map f xs)
  map⁺ (here p)  = here p
  map⁺ (there p) = there $ map⁺ p

  map⁻ : ∀ {p} {P : B → Set p} {xs} →
         Any P (List.map f xs) → Any (P ∘ f) xs
  map⁻ {xs = []}     ()
  map⁻ {xs = x ∷ xs} (here p)  = here p
  map⁻ {xs = x ∷ xs} (there p) = there $ map⁻ p

  map⁺∘map⁻ : ∀ {p} {P : B → Set p} {xs} →
              (p : Any P (List.map f xs)) → map⁺ (map⁻ p) ≡ p
  map⁺∘map⁻ {xs = []}     ()
  map⁺∘map⁻ {xs = x ∷ xs} (here  p) = refl
  map⁺∘map⁻ {xs = x ∷ xs} (there p) = P.cong there (map⁺∘map⁻ p)

  map⁻∘map⁺ : ∀ {p} (P : B → Set p) {xs} →
              (p : Any (P ∘ f) xs) → map⁻ {P = P} (map⁺ p) ≡ p
  map⁻∘map⁺ P (here  p) = refl
  map⁻∘map⁺ P (there p) = P.cong there (map⁻∘map⁺ P p)

  map↔ : ∀ {p} {P : B → Set p} {xs} →
         Any (P ∘ f) xs ↔ Any P (List.map f xs)
  map↔ = inverse map⁺ map⁻ (map⁻∘map⁺ _) map⁺∘map⁻

------------------------------------------------------------------------
-- mapMaybe

module _ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
         (f : A → Maybe B) where

  mapMaybe⁺ : ∀ xs → Any (MAny.Any P) (map f xs) →
              Any P (mapMaybe f xs)
  mapMaybe⁺ []       ()
  mapMaybe⁺ (x ∷ xs) ps with f x | ps
  ... | nothing | here  ()
  ... | nothing | there pxs      = mapMaybe⁺ xs pxs
  ... | just _  | here (just py) = here py
  ... | just _  | there pxs      = there (mapMaybe⁺ xs pxs)

------------------------------------------------------------------------
-- _++_

module _ {a p} {A : Set a} {P : A → Set p} where

  ++⁺ˡ : ∀ {xs ys} → Any P xs → Any P (xs ++ ys)
  ++⁺ˡ (here p)  = here p
  ++⁺ˡ (there p) = there (++⁺ˡ p)

  ++⁺ʳ : ∀ xs {ys} → Any P ys → Any P (xs ++ ys)
  ++⁺ʳ []       p = p
  ++⁺ʳ (x ∷ xs) p = there (++⁺ʳ xs p)

  ++⁻ : ∀ xs {ys} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁻ []       p         = inj₂ p
  ++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
  ++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

  ++⁺∘++⁻ : ∀ xs {ys} (p : Any P (xs ++ ys)) →
            [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs p) ≡ p
  ++⁺∘++⁻ []       p         = refl
  ++⁺∘++⁻ (x ∷ xs) (here  p) = refl
  ++⁺∘++⁻ (x ∷ xs) (there p) with ++⁻ xs p | ++⁺∘++⁻ xs p
  ++⁺∘++⁻ (x ∷ xs) (there p) | inj₁ p′ | ih = P.cong there ih
  ++⁺∘++⁻ (x ∷ xs) (there p) | inj₂ p′ | ih = P.cong there ih

  ++⁻∘++⁺ : ∀ xs {ys} (p : Any P xs ⊎ Any P ys) →
            ++⁻ xs ([ ++⁺ˡ , ++⁺ʳ xs ]′ p) ≡ p
  ++⁻∘++⁺ []            (inj₁ ())
  ++⁻∘++⁺ []            (inj₂ p)         = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₁ (here  p)) = refl
  ++⁻∘++⁺ (x ∷ xs) {ys} (inj₁ (there p)) rewrite ++⁻∘++⁺ xs {ys} (inj₁ p) = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₂ p)         rewrite ++⁻∘++⁺ xs      (inj₂ p) = refl

  ++↔ : ∀ {xs ys} → (Any P xs ⊎ Any P ys) ↔ Any P (xs ++ ys)
  ++↔ {xs = xs} = inverse [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs) (++⁻∘++⁺ xs) (++⁺∘++⁻ xs)

  ++-comm : ∀ xs ys → Any P (xs ++ ys) → Any P (ys ++ xs)
  ++-comm xs ys = [ ++⁺ʳ ys , ++⁺ˡ ]′ ∘ ++⁻ xs

  ++-comm∘++-comm : ∀ xs {ys} (p : Any P (xs ++ ys)) →
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

  ++↔++ : ∀ xs ys → Any P (xs ++ ys) ↔ Any P (ys ++ xs)
  ++↔++ xs ys = inverse (++-comm xs ys) (++-comm ys xs)
                        (++-comm∘++-comm xs) (++-comm∘++-comm ys)

  ++-insert : ∀ xs {ys x} → P x → Any P (xs ++ [ x ] ++ ys)
  ++-insert xs Px = ++⁺ʳ xs (++⁺ˡ (singleton⁺ Px))

------------------------------------------------------------------------
-- concat

module _ {a p} {A : Set a} {P : A → Set p} where

  concat⁺ : ∀ {xss} → Any (Any P) xss → Any P (concat xss)
  concat⁺ (here p)           = ++⁺ˡ p
  concat⁺ (there {x = xs} p) = ++⁺ʳ xs (concat⁺ p)

  concat⁻ : ∀ xss → Any P (concat xss) → Any (Any P) xss
  concat⁻ []               ()
  concat⁻ ([]       ∷ xss) p         = there $ concat⁻ xss p
  concat⁻ ((x ∷ xs) ∷ xss) (here  p) = here (here p)
  concat⁻ ((x ∷ xs) ∷ xss) (there p) with concat⁻ (xs ∷ xss) p
  ... | here  p′ = here (there p′)
  ... | there p′ = there p′

  concat⁻∘++⁺ˡ : ∀ {xs} xss (p : Any P xs) →
                 concat⁻ (xs ∷ xss) (++⁺ˡ p) ≡ here p
  concat⁻∘++⁺ˡ xss (here  p) = refl
  concat⁻∘++⁺ˡ xss (there p) rewrite concat⁻∘++⁺ˡ xss p = refl

  concat⁻∘++⁺ʳ : ∀ xs xss (p : Any P (concat xss)) →
                   concat⁻ (xs ∷ xss) (++⁺ʳ xs p) ≡ there (concat⁻ xss p)
  concat⁻∘++⁺ʳ []       xss p = refl
  concat⁻∘++⁺ʳ (x ∷ xs) xss p rewrite concat⁻∘++⁺ʳ xs xss p = refl

  concat⁺∘concat⁻ : ∀ xss (p : Any P (concat xss)) →
                      concat⁺ (concat⁻ xss p) ≡ p
  concat⁺∘concat⁻ []               ()
  concat⁺∘concat⁻ ([]       ∷ xss) p         = concat⁺∘concat⁻ xss p
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (here p)  = refl
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there p)
                with concat⁻ (xs ∷ xss) p | concat⁺∘concat⁻ (xs ∷ xss) p
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there .(++⁺ˡ p′))              | here  p′ | refl = refl
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there .(++⁺ʳ xs (concat⁺ p′))) | there p′ | refl = refl

  concat⁻∘concat⁺ : ∀ {xss} (p : Any (Any P) xss) → concat⁻ xss (concat⁺ p) ≡ p
  concat⁻∘concat⁺ (here                      p) = concat⁻∘++⁺ˡ _ p
  concat⁻∘concat⁺ (there {x = xs} {xs = xss} p)
    rewrite concat⁻∘++⁺ʳ xs xss (concat⁺ p) =
      P.cong there $ concat⁻∘concat⁺ p

  concat↔ : ∀ {xss} → Any (Any P) xss ↔ Any P (concat xss)
  concat↔ {xss} = inverse concat⁺ (concat⁻ xss) concat⁻∘concat⁺ (concat⁺∘concat⁻ xss)

------------------------------------------------------------------------
-- applyUpTo

module _ {a p} {A : Set a} {P : A → Set p} where

  applyUpTo⁺ : ∀ f {i n} → P (f i) → i < n → Any P (applyUpTo f n)
  applyUpTo⁺ _ p (s≤s z≤n)       = here p
  applyUpTo⁺ f p (s≤s (s≤s i<n)) =
    there (applyUpTo⁺ (f ∘ suc) p (s≤s i<n))

  applyUpTo⁻ : ∀ f {n} → Any P (applyUpTo f n) →
               ∃ λ i → i < n × P (f i)
  applyUpTo⁻ f {zero}  ()
  applyUpTo⁻ f {suc n} (here p)  = zero , s≤s z≤n , p
  applyUpTo⁻ f {suc n} (there p) with applyUpTo⁻ (f ∘ suc) p
  ... | i , i<n , q = suc i , s≤s i<n , q

------------------------------------------------------------------------
-- tabulate

module _ {a p} {A : Set a} {P : A → Set p} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} i → P (f i) → Any P (tabulate f)
  tabulate⁺ fzero    p = here p
  tabulate⁺ (fsuc i) p = there (tabulate⁺ i p)

  tabulate⁻ : ∀ {n} {f : Fin n → A} →
              Any P (tabulate f) → ∃ λ i → P (f i)
  tabulate⁻ {zero}  ()
  tabulate⁻ {suc n} (here p)   = fzero , p
  tabulate⁻ {suc n} (there p) = Prod.map fsuc id (tabulate⁻ p)

------------------------------------------------------------------------
-- map-with-∈.

module _ {a b p} {A : Set a} {B : Set b} {P : B → Set p} where

  map-with-∈⁺ : ∀ {xs : List A} (f : ∀ {x} → x ∈ xs → B) →
                (∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) →
                Any P (map-with-∈ xs f)
  map-with-∈⁺ f (_ , here refl  , p) = here p
  map-with-∈⁺ f (_ , there x∈xs , p) =
    there $ map-with-∈⁺ (f ∘ there) (_ , x∈xs , p)

  map-with-∈⁻ : ∀ (xs : List A) (f : ∀ {x} → x ∈ xs → B) →
                Any P (map-with-∈ xs f) →
                ∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)
  map-with-∈⁻ []       f ()
  map-with-∈⁻ (y ∷ xs) f (here  p) = (y , here refl , p)
  map-with-∈⁻ (y ∷ xs) f (there p) =
    Prod.map id (Prod.map there id) $ map-with-∈⁻ xs (f ∘ there) p

  map-with-∈↔ : ∀  {xs : List A} {f : ∀ {x} → x ∈ xs → B} →
    (∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) ↔ Any P (map-with-∈ xs f)
  map-with-∈↔ = inverse (map-with-∈⁺ _) (map-with-∈⁻ _ _) (from∘to _) (to∘from _ _)
    where
    from∘to : ∀ {xs : List A} (f : ∀ {x} → x ∈ xs → B)
              (p : ∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) →
              map-with-∈⁻ xs f (map-with-∈⁺ f p) ≡ p
    from∘to f (_ , here refl  , p) = refl
    from∘to f (_ , there x∈xs , p)
      rewrite from∘to (f ∘ there) (_ , x∈xs , p) = refl

    to∘from : ∀ (xs : List A) (f : ∀ {x} → x ∈ xs → B)
              (p : Any P (map-with-∈ xs f)) →
              map-with-∈⁺ f (map-with-∈⁻ xs f p) ≡ p
    to∘from []       f ()
    to∘from (y ∷ xs) f (here  p) = refl
    to∘from (y ∷ xs) f (there p) =
      P.cong there $ to∘from xs (f ∘ there) p


------------------------------------------------------------------------
-- return

module _ {a p} {A : Set a} {P : A → Set p} where

  return⁺ : ∀ {x} → P x → Any P (return x)
  return⁺ = here

  return⁻ : ∀ {x} → Any P (return x) → P x
  return⁻ (here p)   = p
  return⁻ (there ())

  return⁺∘return⁻ : ∀ {x} (p : Any P (return x)) →
                    return⁺ (return⁻ p) ≡ p
  return⁺∘return⁻ (here p)   = refl
  return⁺∘return⁻ (there ())

  return⁻∘return⁺ : ∀ {x} (p : P x) → return⁻ (return⁺ p) ≡ p
  return⁻∘return⁺ p = refl

  return↔ : ∀ {x} → P x ↔ Any P (return x)
  return↔ = inverse return⁺ return⁻ return⁻∘return⁺ return⁺∘return⁻

------------------------------------------------------------------------
-- _∷_

module _ {a p} {A : Set a} where

  ∷↔ : ∀ (P : Pred A p) {x xs} → (P x ⊎ Any P xs) ↔ Any P (x ∷ xs)
  ∷↔ P {x} {xs} =
    (P x         ⊎ Any P xs)  ↔⟨ return↔ {P = P} ⊎-cong (Any P xs ∎) ⟩
    (Any P [ x ] ⊎ Any P xs)  ↔⟨ ++↔ {P = P} {xs = [ x ]} ⟩
    Any P (x ∷ xs)            ∎

------------------------------------------------------------------------
-- _>>=_

module _ {ℓ p} {A B : Set ℓ} {P : B → Set p} {f : A → List B} where

  >>=↔ : ∀ {xs} → Any (Any P ∘ f) xs ↔ Any P (xs >>= f)
  >>=↔ {xs} =
    Any (Any P ∘ f) xs           ↔⟨ map↔ ⟩
    Any (Any P) (List.map f xs)  ↔⟨ concat↔ ⟩
    Any P (xs >>= f)             ∎

------------------------------------------------------------------------
-- _⊛_

module _ {ℓ} {A B : Set ℓ} where

  ⊛↔ : ∀ {P : B → Set ℓ} {fs : List (A → B)} {xs : List A} →
       Any (λ f → Any (P ∘ f) xs) fs ↔ Any P (fs ⊛ xs)
  ⊛↔ {P = P} {fs} {xs} =
    Any (λ f → Any (P ∘ f) xs) fs               ↔⟨ Any-cong (λ _ → Any-cong (λ _ → return↔) (_ ∎)) (_ ∎) ⟩
    Any (λ f → Any (Any P ∘ return ∘ f) xs) fs  ↔⟨ Any-cong (λ _ → >>=↔ ) (_ ∎) ⟩
    Any (λ f → Any P (xs >>= return ∘ f)) fs    ↔⟨ >>=↔ ⟩
    Any P (fs ⊛ xs)                             ∎

-- An alternative introduction rule for _⊛_

  ⊛⁺′ : ∀ {P : A → Set ℓ} {Q : B → Set ℓ} {fs : List (A → B)} {xs} →
        Any (P ⟨→⟩ Q) fs → Any P xs → Any Q (fs ⊛ xs)
  ⊛⁺′ pq p =
    Inverse.to ⊛↔ ⟨$⟩
      Any.map (λ pq → Any.map (λ {x} → pq {x}) p) pq

------------------------------------------------------------------------
-- _⊗_

module _ {ℓ} {A B : Set ℓ} where

  ⊗↔ : {P : A × B → Set ℓ} {xs : List A} {ys : List B} →
       Any (λ x → Any (λ y → P (x , y)) ys) xs ↔ Any P (xs ⊗ ys)
  ⊗↔ {P} {xs} {ys} =
    Any (λ x → Any (λ y → P (x , y)) ys) xs                             ↔⟨ return↔ ⟩
    Any (λ _,_ → Any (λ x → Any (λ y → P (x , y)) ys) xs) (return _,_)  ↔⟨ ⊛↔ ⟩
    Any (λ x, → Any (P ∘ x,) ys) (_,_ <$> xs)                           ↔⟨ ⊛↔ ⟩
    Any P (xs ⊗ ys)                                                     ∎

  ⊗↔′ : {P : A → Set ℓ} {Q : B → Set ℓ} {xs : List A} {ys : List B} →
        (Any P xs × Any Q ys) ↔ Any (P ⟨×⟩ Q) (xs ⊗ ys)
  ⊗↔′ {P} {Q} {xs} {ys} =
    (Any P xs × Any Q ys)                    ↔⟨ ×↔ ⟩
    Any (λ x → Any (λ y → P x × Q y) ys) xs  ↔⟨ ⊗↔ ⟩
    Any (P ⟨×⟩ Q) (xs ⊗ ys)                  ∎

------------------------------------------------------------------------
-- Prefix

module _ {a r p} {A : Set a} {R : Rel A r} {P : Pred A p}
         (resp : P Respects R) where

 open import Data.List.Relation.Prefix.Heterogeneous as Prefix

 prefix⁺ : ∀ {xs ys} → Prefix R xs ys → Any P xs → Any P ys
 prefix⁺ rs e with toView rs
 prefix⁺ rs e | ss Prefix.++ ts = ++⁺ˡ (lift-resp resp ss e)
