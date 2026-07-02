-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to setoid list membership
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Membership.Setoid.Properties where

open import Algebra using (Op₂; Selective)
open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (suc-injective)
open import Data.List.Base hiding (find)
import Data.List.Membership.Setoid as Membership
import Data.List.Relation.Binary.Equality.Setoid as Equality
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Unary.All.Properties.Core as All
import Data.List.Relation.Unary.Any.Properties as Any
import Data.List.Relation.Unary.Unique.Setoid as Unique
open import Data.Nat.Base using (suc; z<s; _<_)
open import Data.Product.Base as Product using (∃; _×_; _,_ ; ∃₂; ∃-syntax)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (_$_; flip; _∘_; _∘′_; id)
open import Function.Bundles using (_↔_; mk↔; _⇔_; mk⇔)
open import Level using (Level)
open import Relation.Binary.Core using (Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_)
open import Relation.Binary.Definitions as Binary hiding (Decidable)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Nullary.Decidable using (does; _because_; yes; no)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Relation.Nullary.Reflects using (invert)
open import Relation.Unary as Unary using (Decidable; Pred)

open Setoid using (Carrier)

private
  variable
    c c₁ c₂ c₃ p ℓ ℓ₁ ℓ₂ ℓ₃ : Level

------------------------------------------------------------------------
-- Basics

module _ (S : Setoid c ℓ) where

  open Membership S

  ∉[] : ∀ {x} → x ∉ []
  ∉[] ()

------------------------------------------------------------------------
-- Equality properties

module _ (S : Setoid c ℓ) where

  open Setoid S
  open Equality S
  open Membership S

  -- _∈_ respects the underlying equality

  ∈-resp-≈ : ∀ {xs} → (_∈ xs) Respects _≈_
  ∈-resp-≈ x≈y x∈xs = Any.map (trans (sym x≈y)) x∈xs

  ∉-resp-≈ : ∀ {xs} → (_∉ xs) Respects _≈_
  ∉-resp-≈ v≈w v∉xs w∈xs = v∉xs (∈-resp-≈ (sym v≈w) w∈xs)

  ∈-resp-≋ : ∀ {x} → (x ∈_) Respects _≋_
  ∈-resp-≋ = Any.lift-resp (flip trans)

  ∉-resp-≋ : ∀ {x} → (x ∉_) Respects _≋_
  ∉-resp-≋ xs≋ys v∉xs v∈ys = v∉xs (∈-resp-≋ (≋-sym xs≋ys) v∈ys)

  -- x ∉_ is equivalent to All (x ≉_)

  ∉⇒All[≉] : ∀ {x xs} → x ∉ xs → All (x ≉_) xs
  ∉⇒All[≉] = All.¬Any⇒All¬ _

  All[≉]⇒∉ : ∀ {x xs} → All (x ≉_) xs → x ∉ xs
  All[≉]⇒∉ = All.All¬⇒¬Any

  -- index is injective in its first argument.

  index-injective : ∀ {x₁ x₂ xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
                    Any.index x₁∈xs ≡ Any.index x₂∈xs → x₁ ≈ x₂
  index-injective (here x₁≈x)   (here x₂≈x)   _  = trans x₁≈x (sym x₂≈x)
  index-injective (there x₁∈xs) (there x₂∈xs) eq = index-injective x₁∈xs x₂∈xs (suc-injective eq)

------------------------------------------------------------------------
-- Irrelevance

module _ (S : Setoid c ℓ) where

  open Setoid S
  open Unique S
  open Membership S

  private
    ∉×∈⇒≉ : ∀ {x y xs} → All (y ≉_) xs → x ∈ xs → x ≉ y
    ∉×∈⇒≉ ≉s x∈xs x≈y = All[≉]⇒∉ S ≉s (∈-resp-≈ S x≈y x∈xs)

  unique⇒irrelevant : Binary.Irrelevant _≈_ → ∀ {xs} → Unique xs → Unary.Irrelevant (_∈ xs)
  unique⇒irrelevant ≈-irr _        (here p)  (here q)  =
    ≡.cong here (≈-irr p q)
  unique⇒irrelevant ≈-irr (_  ∷ u) (there p) (there q) =
    ≡.cong there (unique⇒irrelevant ≈-irr u p q)
  unique⇒irrelevant ≈-irr (≉s ∷ _) (here p)  (there q) =
    contradiction p (∉×∈⇒≉ ≉s q)
  unique⇒irrelevant ≈-irr (≉s ∷ _) (there p) (here q)  =
    contradiction q (∉×∈⇒≉ ≉s p)

------------------------------------------------------------------------
-- mapWith∈

module _ (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) where

  open Setoid S₁ renaming (Carrier to A₁; _≈_ to _≈₁_; refl to refl₁)
  open Setoid S₂ renaming (Carrier to A₂; _≈_ to _≈₂_; refl to refl₂)
  open Equality S₁ using ([]; _∷_) renaming (_≋_ to _≋₁_)
  open Equality S₂ using () renaming (_≋_ to _≋₂_)
  open Membership S₁

  mapWith∈-cong : ∀ {xs ys} → xs ≋₁ ys →
                  (f : ∀ {x} → x ∈ xs → A₂) →
                  (g : ∀ {y} → y ∈ ys → A₂) →
                  (∀ {x y} → x ≈₁ y → (x∈xs : x ∈ xs) (y∈ys : y ∈ ys) →
                     f x∈xs ≈₂ g y∈ys) →
                  mapWith∈ xs f ≋₂ mapWith∈ ys g
  mapWith∈-cong []            f g cong = []
  mapWith∈-cong (x≈y ∷ xs≋ys) f g cong =
    cong x≈y (here refl₁) (here refl₁) ∷
    mapWith∈-cong xs≋ys (f ∘ there) (g ∘ there)
      (λ x≈y x∈xs y∈ys → cong x≈y (there x∈xs) (there y∈ys))

  mapWith∈≗map : ∀ f xs → mapWith∈ xs (λ {x} _ → f x) ≋₂ map f xs
  mapWith∈≗map f []       = []
  mapWith∈≗map f (x ∷ xs) = refl₂ ∷ mapWith∈≗map f xs


module _ (S : Setoid c ℓ) where

  open Setoid S
  open Membership S

  length-mapWith∈ : ∀ {a} {A : Set a} xs {f : ∀ {x} → x ∈ xs → A} →
                    length (mapWith∈ xs f) ≡ length xs
  length-mapWith∈ []       = ≡.refl
  length-mapWith∈ (x ∷ xs) = ≡.cong suc (length-mapWith∈ xs)

  mapWith∈-id : ∀ xs → mapWith∈ xs (λ {x} _ → x) ≡ xs
  mapWith∈-id []       = ≡.refl
  mapWith∈-id (x ∷ xs) = ≡.cong (x ∷_) (mapWith∈-id xs)

  map-mapWith∈ : ∀ {a b} {A : Set a} {B : Set b} →
                 ∀ xs (f : ∀ {x} → x ∈ xs → A) (g : A → B) →
                 map g (mapWith∈ xs f) ≡ mapWith∈ xs (g ∘′ f)
  map-mapWith∈ []       f g = ≡.refl
  map-mapWith∈ (x ∷ xs) f g = ≡.cong (_ ∷_) (map-mapWith∈ xs (f ∘ there) g)

------------------------------------------------------------------------
-- map

module _ (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) where

  open Setoid S₁ renaming (_≈_ to _≈₁_)
  open Setoid S₂ renaming (_≈_ to _≈₂_)
  private module M₁ = Membership S₁; open M₁ using (find) renaming (_∈_ to _∈₁_)
  private module M₂ = Membership S₂; open M₂ using () renaming (_∈_ to _∈₂_)

  ∈-map⁺ : ∀ {f} → f Preserves _≈₁_ ⟶ _≈₂_ →
           ∀ {v xs} → v ∈₁ xs → f v ∈₂ map f xs
  ∈-map⁺ pres x∈xs = Any.map⁺ (Any.map pres x∈xs)

  ∈-map⁻ : ∀ {v xs f} → v ∈₂ map f xs →
           ∃ λ x → x ∈₁ xs × v ≈₂ f x
  ∈-map⁻ x∈map = find (Any.map⁻ x∈map)

  map-∷= : ∀ {f} (pres : f Preserves _≈₁_ ⟶ _≈₂_) →
           ∀ {xs x v} → (x∈xs : x ∈₁ xs) →
           map f (x∈xs M₁.∷= v) ≡ ∈-map⁺ pres x∈xs M₂.∷= f v
  map-∷= pres (here x≈y)   = ≡.refl
  map-∷= pres (there x∈xs) = ≡.cong (_ ∷_) (map-∷= pres x∈xs)

------------------------------------------------------------------------
-- _++_

module _ (S : Setoid c ℓ) where

  open Membership S using (_∈_)
  open Setoid S
  open Equality S using (_≋_; _∷_; ≋-refl)

  ∈-++⁺ˡ : ∀ {v xs ys} → v ∈ xs → v ∈ xs ++ ys
  ∈-++⁺ˡ = Any.++⁺ˡ

  ∈-++⁺ʳ : ∀ {v} xs {ys} → v ∈ ys → v ∈ xs ++ ys
  ∈-++⁺ʳ = Any.++⁺ʳ

  ∈-++⁻ : ∀ {v} xs {ys} → v ∈ xs ++ ys → (v ∈ xs) ⊎ (v ∈ ys)
  ∈-++⁻ = Any.++⁻

  ∈-++⁺∘++⁻ : ∀ {v} xs {ys} (p : v ∈ xs ++ ys) →
              [ ∈-++⁺ˡ , ∈-++⁺ʳ xs ]′ (∈-++⁻ xs p) ≡ p
  ∈-++⁺∘++⁻ = Any.++⁺∘++⁻

  ∈-++⁻∘++⁺ : ∀ {v} xs {ys} (p : v ∈ xs ⊎ v ∈ ys) →
              ∈-++⁻ xs ([ ∈-++⁺ˡ , ∈-++⁺ʳ xs ]′ p) ≡ p
  ∈-++⁻∘++⁺ = Any.++⁻∘++⁺

  ∈-++↔ : ∀ {v xs ys} → (v ∈ xs ⊎ v ∈ ys) ↔ v ∈ xs ++ ys
  ∈-++↔ = Any.++↔

  ∈-++-comm : ∀ {v} xs ys → v ∈ xs ++ ys → v ∈ ys ++ xs
  ∈-++-comm = Any.++-comm

  ∈-++-comm∘++-comm : ∀ {v} xs {ys} (p : v ∈ xs ++ ys) →
                      ∈-++-comm ys xs (∈-++-comm xs ys p) ≡ p
  ∈-++-comm∘++-comm = Any.++-comm∘++-comm

  ∈-++↔++ : ∀ {v} xs ys → v ∈ xs ++ ys ↔ v ∈ ys ++ xs
  ∈-++↔++ = Any.++↔++

  ∈-insert : ∀ xs {ys v w} → v ≈ w → v ∈ xs ++ [ w ] ++ ys
  ∈-insert xs = Any.++-insert xs

  ∈-∃++ : ∀ {v xs} → v ∈ xs → ∃₂ λ ys zs → ∃ λ w →
          v ≈ w × xs ≋ ys ++ [ w ] ++ zs
  ∈-∃++ (here px)        = [] , _ , _ , px , ≋-refl
  ∈-∃++ (there {d} v∈xs) =
    let hs , _ , _ , v≈v′ , eq = ∈-∃++ v∈xs
    in d ∷ hs , _ , _ , v≈v′ , refl ∷ eq

------------------------------------------------------------------------
-- concat

module _ (S : Setoid c ℓ) where

  open Setoid S using (_≈_)
  open Membership S using (_∈_)
  open Equality S using (≋-setoid)
  open Membership ≋-setoid using (find) renaming (_∈_ to _∈ₗ_)

  ∈-concat⁺ : ∀ {v xss} → Any (v ∈_) xss → v ∈ concat xss
  ∈-concat⁺ = Any.concat⁺

  ∈-concat⁻ : ∀ {v} xss → v ∈ concat xss → Any (v ∈_) xss
  ∈-concat⁻ = Any.concat⁻

  ∈-concat⁺′ : ∀ {v vs xss} → v ∈ vs → vs ∈ₗ xss → v ∈ concat xss
  ∈-concat⁺′ v∈vs = ∈-concat⁺ ∘ Any.map (flip (∈-resp-≋ S) v∈vs)

  ∈-concat⁻′ : ∀ {v} xss → v ∈ concat xss → ∃ λ xs → v ∈ xs × xs ∈ₗ xss
  ∈-concat⁻′ xss v∈c[xss] =
    let xs , xs∈xss , v∈xs = find (∈-concat⁻ xss v∈c[xss]) in xs , v∈xs , xs∈xss

------------------------------------------------------------------------
-- concatMap

module _
  (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂)
  {f : Carrier S₁ → List (Carrier S₂)} {xs y} where

  open Membership S₂ using (_∈_)

  ∈-concatMap⁺ : Any ((y ∈_) ∘ f) xs → y ∈ concatMap f xs
  ∈-concatMap⁺ = Any.concatMap⁺ f

  ∈-concatMap⁻ : y ∈ concatMap f xs → Any ((y ∈_) ∘ f) xs
  ∈-concatMap⁻ = Any.concatMap⁻ f

------------------------------------------------------------------------
-- reverse

module _ (S : Setoid c ℓ) where

  open Membership S using (_∈_)

  reverse⁺ : ∀ {x xs} → x ∈ xs → x ∈ reverse xs
  reverse⁺ = Any.reverse⁺

  reverse⁻ : ∀ {x xs} → x ∈ reverse xs → x ∈ xs
  reverse⁻ = Any.reverse⁻

------------------------------------------------------------------------
-- cartesianProductWith

module _ (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) (S₃ : Setoid c₃ ℓ₃) where

  open Setoid S₁ renaming (_≈_ to _≈₁_; refl to refl₁)
  open Setoid S₂ renaming (_≈_ to _≈₂_)
  open Setoid S₃ renaming (_≈_ to _≈₃_)
  open Membership S₁ renaming (_∈_ to _∈₁_)
  open Membership S₂ renaming (_∈_ to _∈₂_)
  open Membership S₃ renaming (_∈_ to _∈₃_)

  ∈-cartesianProductWith⁺ : ∀ {f} → f Preserves₂ _≈₁_ ⟶ _≈₂_ ⟶ _≈₃_ →
                            ∀ {xs ys a b} → a ∈₁ xs → b ∈₂ ys →
                            f a b ∈₃ cartesianProductWith f xs ys
  ∈-cartesianProductWith⁺ pres = Any.cartesianProductWith⁺ _ pres

  ∈-cartesianProductWith⁻ : ∀ f xs ys {v} → v ∈₃ cartesianProductWith f xs ys →
                            ∃₂ λ a b → a ∈₁ xs × b ∈₂ ys × v ≈₃ f a b
  ∈-cartesianProductWith⁻ f (x ∷ xs) ys v∈c with ∈-++⁻ S₃ (map (f x) ys) v∈c
  ... | inj₁ v∈map =
    let b , b∈ys , v≈fxb = ∈-map⁻ S₂ S₃ v∈map
    in x , b , here refl₁ , b∈ys , v≈fxb
  ... | inj₂ v∈com =
    let a , b , a∈xs , b∈ys , v≈fab = ∈-cartesianProductWith⁻ f xs ys v∈com
    in  a , b , there a∈xs , b∈ys , v≈fab

------------------------------------------------------------------------
-- cartesianProduct

module _ (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) where

  open Setoid S₁ renaming (Carrier to A)
  open Setoid S₂ renaming (Carrier to B)
  open Membership S₁ renaming (_∈_ to _∈₁_)
  open Membership S₂ renaming (_∈_ to _∈₂_)
  open Membership (S₁ ×ₛ S₂) renaming (_∈_ to _∈₁₂_)

  ∈-cartesianProduct⁺ : ∀ {x y xs ys} → x ∈₁ xs → y ∈₂ ys →
                        (x , y) ∈₁₂ cartesianProduct xs ys
  ∈-cartesianProduct⁺ = Any.cartesianProduct⁺

  ∈-cartesianProduct⁻ : ∀ xs ys {xy@(x , y) : A × B} →
                        xy ∈₁₂ cartesianProduct xs ys →
                        x ∈₁ xs × y ∈₂ ys
  ∈-cartesianProduct⁻ xs ys = Any.cartesianProduct⁻ xs ys

------------------------------------------------------------------------
-- applyUpTo

module _ (S : Setoid c ℓ) where

  open Setoid S using (_≈_; refl)
  open Membership S using (_∈_)

  ∈-applyUpTo⁺ : ∀ f {i n} → i < n → f i ∈ applyUpTo f n
  ∈-applyUpTo⁺ f = Any.applyUpTo⁺ f refl

  ∈-applyUpTo⁻ : ∀ {v} f {n} → v ∈ applyUpTo f n →
                 ∃ λ i → i < n × v ≈ f i
  ∈-applyUpTo⁻ = Any.applyUpTo⁻

------------------------------------------------------------------------
-- applyDownFrom

  ∈-applyDownFrom⁺ : ∀ f {i n} → i < n → f i ∈ applyDownFrom f n
  ∈-applyDownFrom⁺ f = Any.applyDownFrom⁺ f refl

  ∈-applyDownFrom⁻ : ∀ {v} f {n} → v ∈ applyDownFrom f n →
                     ∃ λ i → i < n × v ≈ f i
  ∈-applyDownFrom⁻ = Any.applyDownFrom⁻

------------------------------------------------------------------------
-- tabulate

module _ (S : Setoid c ℓ) where

  open Setoid S using (_≈_; refl) renaming (Carrier to A)
  open Membership S using (_∈_)

  ∈-tabulate⁺ : ∀ {n} {f : Fin n → A} i → f i ∈ tabulate f
  ∈-tabulate⁺ i = Any.tabulate⁺ i refl

  ∈-tabulate⁻ : ∀ {n} {f : Fin n → A} {v} →
                v ∈ tabulate f → ∃ λ i → v ≈ f i
  ∈-tabulate⁻ = Any.tabulate⁻

------------------------------------------------------------------------
-- filter

module _ (S : Setoid c ℓ) {P : Pred (Carrier S) p}
         (P? : Decidable P) (resp : P Respects (Setoid._≈_ S)) where

  open Setoid S using (_≈_; sym)
  open Membership S using (_∈_)

  ∈-filter⁺ : ∀ {v xs} → v ∈ xs → P v → v ∈ filter P? xs
  ∈-filter⁺ {xs = x ∷ _} (here v≈x) Pv with P? x
  ... |  true because   _   = here v≈x
  ... | false because [¬Px] = contradiction (resp v≈x Pv) (invert [¬Px])
  ∈-filter⁺ {xs = x ∷ _} (there v∈xs) Pv with does (P? x)
  ... | true  = there (∈-filter⁺ v∈xs Pv)
  ... | false = ∈-filter⁺ v∈xs Pv

  ∈-filter⁻ : ∀ {v xs} → v ∈ filter P? xs → v ∈ xs × P v
  ∈-filter⁻ {xs = x ∷ xs} v∈f[x∷xs] with P? x
  ... | false because  _   = Product.map there id (∈-filter⁻ v∈f[x∷xs])
  ... |  true because [Px] with v∈f[x∷xs]
  ...   | here  v≈x   = here v≈x , resp (sym v≈x) (invert [Px])
  ...   | there v∈fxs = Product.map there id (∈-filter⁻ v∈fxs)

------------------------------------------------------------------------
-- map∘filter

module _
  (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂)
  {P : Pred _ p} (P? : Decidable P) (resp : P Respects _)
  {f xs y} where

  open Setoid     S₁ renaming (_≈_ to _≈₁_)
  open Setoid     S₂ renaming (_≈_ to _≈₂_; sym to sym₂)
  open Membership S₁ renaming (_∈_ to _∈₁_)
  open Membership S₂ renaming (_∈_ to _∈₂_)

  ∈-map∘filter⁻ : y ∈₂ map f (filter P? xs) →
                  ∃[ x ] x ∈₁ xs × y ≈₂ f x × P x
  ∈-map∘filter⁻ h =
    let x , x∈ , y≈ = ∈-map⁻ S₁ S₂ h
        y∈ , Py     = ∈-filter⁻ S₁ P? resp x∈
    in x , y∈ , y≈ , Py

  ∈-map∘filter⁺ : f Preserves _≈₁_ ⟶ _≈₂_ →
                  ∃[ x ] x ∈₁ xs × y ≈₂ f x × P x →
                  y ∈₂ map f (filter P? xs)
  ∈-map∘filter⁺ pres (x , x∈ , y≈ , Px)
    = ∈-resp-≈ S₂ (sym₂ y≈)
    $ ∈-map⁺ S₁ S₂ pres (∈-filter⁺ S₁ P? resp x∈ Px)

------------------------------------------------------------------------
-- derun and deduplicate

module _ (S : Setoid c ℓ) {R : Rel (Carrier S) ℓ₂} (R? : Binary.Decidable R) where

  open Setoid S using (_≈_)
  open Membership S using (_∈_)

  ∈-derun⁺ : _≈_ Respectsʳ R → ∀ {xs z} → z ∈ xs → z ∈ derun R? xs
  ∈-derun⁺ ≈-resp-R z∈xs = Any.derun⁺ R? ≈-resp-R z∈xs

  ∈-derun⁻ : ∀ xs {z} → z ∈ derun R? xs → z ∈ xs
  ∈-derun⁻ xs z∈derun[R,xs] = Any.derun⁻ R? z∈derun[R,xs]

  ∈-deduplicate⁺ : _≈_ Respectsʳ (flip R) → ∀ {xs z} →
                   z ∈ xs → z ∈ deduplicate R? xs
  ∈-deduplicate⁺ ≈-resp-R z∈xs = Any.deduplicate⁺ R? ≈-resp-R z∈xs

  ∈-deduplicate⁻ : ∀ xs {z} → z ∈ deduplicate R? xs → z ∈ xs
  ∈-deduplicate⁻ xs z∈dedup[R,xs] = Any.deduplicate⁻ R? z∈dedup[R,xs]

  deduplicate-∈⇔ : _≈_ Respectsʳ (flip R) → ∀ {xs z} →
                   z ∈ xs ⇔ z ∈ deduplicate R? xs
  deduplicate-∈⇔ p = mk⇔ (∈-deduplicate⁺ p) (∈-deduplicate⁻ _)

------------------------------------------------------------------------
-- length

module _ (S : Setoid c ℓ) where

  open Membership S using (_∈_)

  ∈-length : ∀ {x xs} → x ∈ xs → 0 < length xs
  ∈-length (here px)    = z<s
  ∈-length (there x∈xs) = z<s

------------------------------------------------------------------------
-- lookup

module _ (S : Setoid c ℓ) where

  open Setoid S using (refl)
  open Membership S using (_∈_)

  ∈-lookup : ∀ xs i → lookup xs i ∈ xs
  ∈-lookup (x ∷ xs) zero    = here refl
  ∈-lookup (x ∷ xs) (suc i) = there (∈-lookup xs i)

------------------------------------------------------------------------
-- foldr

module _ (S : Setoid c ℓ) {_•_ : Op₂ (Carrier S)} where

  open Setoid S using (_≈_; refl; sym; trans)
  open Membership S using (_∈_)

  foldr-selective : Selective _≈_ _•_ → ∀ e xs →
                    (foldr _•_ e xs ≈ e) ⊎ (foldr _•_ e xs ∈ xs)
  foldr-selective •-sel i [] = inj₁ refl
  foldr-selective •-sel i (x ∷ xs) with •-sel x (foldr _•_ i xs)
  ... | inj₁ x•f≈x = inj₂ (here x•f≈x)
  ... | inj₂ x•f≈f with foldr-selective •-sel i xs
  ...   | inj₁ f≈i  = inj₁ (trans x•f≈f f≈i)
  ...   | inj₂ f∈xs = inj₂ (∈-resp-≈ S (sym x•f≈f) (there f∈xs))

------------------------------------------------------------------------
-- foldl

module _ (S : Setoid c ℓ) {_•_ : Op₂ (Carrier S)} where

  open Setoid S using (_≈_; refl; sym; trans)
  open Membership S using (_∈_)

  foldl-selective : Selective _≈_ _•_ → ∀ e xs →
                    (foldl _•_ e xs ≈ e) ⊎ (foldl _•_ e xs ∈ xs)
  foldl-selective •-sel i [] = inj₁ refl
  foldl-selective •-sel i (x ∷ xs) with foldl-selective •-sel (i • x) xs
  ... | inj₂ f∈xs = inj₂ (there f∈xs)
  ... | inj₁ f≈i•x with •-sel i x
  ...   | inj₁ i•x≈i = inj₁ (trans f≈i•x i•x≈i)
  ...   | inj₂ i•x≈x = inj₂ (here (trans f≈i•x i•x≈x))

------------------------------------------------------------------------
-- _∷=_

module _ (S : Setoid c ℓ) where

  open Setoid S
  open Membership S

  ∈-∷=⁺-updated : ∀ {xs x v} (x∈xs : x ∈ xs) → v ∈ (x∈xs ∷= v)
  ∈-∷=⁺-updated (here  px)  = here refl
  ∈-∷=⁺-updated (there pxs) = there (∈-∷=⁺-updated pxs)

  ∈-∷=⁺-untouched : ∀ {xs x y v} (x∈xs : x ∈ xs) → (¬ x ≈ y) → y ∈ xs → y ∈ (x∈xs ∷= v)
  ∈-∷=⁺-untouched (here  x≈z)  x≉y (here  y≈z)  = contradiction (trans x≈z (sym y≈z)) x≉y
  ∈-∷=⁺-untouched (here  x≈z)  x≉y (there y∈xs) = there y∈xs
  ∈-∷=⁺-untouched (there x∈xs) x≉y (here  y≈z)  = here y≈z
  ∈-∷=⁺-untouched (there x∈xs) x≉y (there y∈xs) = there (∈-∷=⁺-untouched x∈xs x≉y y∈xs)

  ∈-∷=⁻ : ∀ {xs x y v} (x∈xs : x ∈ xs) → (¬ y ≈ v) → y ∈ (x∈xs ∷= v) → y ∈ xs
  ∈-∷=⁻ (here x≈z)   y≉v (here y≈v) = contradiction y≈v y≉v
  ∈-∷=⁻ (here x≈z)   y≉v (there y∈) = there y∈
  ∈-∷=⁻ (there x∈xs) y≉v (here y≈z) = here y≈z
  ∈-∷=⁻ (there x∈xs) y≉v (there y∈) = there (∈-∷=⁻ x∈xs y≉v y∈)

------------------------------------------------------------------------
-- Any/All symmetry wrt _∈_/_∉_

module _ (S : Setoid c ℓ) where

  open Setoid S using (sym)
  open Membership S

  Any-∈-swap :  ∀ {xs ys} → Any (_∈ ys) xs → Any (_∈ xs) ys
  Any-∈-swap = Any.swap ∘ Any.map (Any.map sym)

  All-∉-swap :  ∀ {xs ys} → All (_∉ ys) xs → All (_∉ xs) ys
  All-∉-swap p = All.¬Any⇒All¬ _ ((All.All¬⇒¬Any p) ∘ Any-∈-swap)
