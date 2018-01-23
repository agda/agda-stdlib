module Data.Table.Properties where

open import Data.Table

private
  module List where
    open import Data.List.Properties public
    open import Data.List public
open List using (List; _∷_; [])
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.List.Any using (here; there; index)
open import Data.Fin as Fin using (Fin)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Data.Product as Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Data.Product.Relation.SigmaPropositional as OverΣ using (OverΣ)

module _ {a} {A : Set a} where

  fromList-∈ : ∀ {xs : List A} (i : Fin (List.length xs)) → lookup (fromList xs) i ∈ xs
  fromList-∈ {[]} ()
  fromList-∈ {x ∷ xs} Fin.zero = here P.refl
  fromList-∈ {x ∷ xs} (Fin.suc i) = there (fromList-∈ i)

  index-fromList-∈ : ∀ {xs i} → index (fromList-∈ {xs} i) ≡ i
  index-fromList-∈ {[]} {()}
  index-fromList-∈ {x ∷ xs} {Fin.zero} = P.refl
  index-fromList-∈ {x ∷ xs} {Fin.suc i} = P.cong Fin.suc index-fromList-∈

  fromList-index : ∀ {xs} {x : A} (x∈xs : x ∈ xs) → lookup (fromList xs) (index x∈xs) ≡ x
  fromList-index (here px) = P.sym px
  fromList-index (there x∈xs) = fromList-index x∈xs

  lookup∈ : ∀ {xs : List A} (i : Fin (List.length xs)) → ∃ λ x → x ∈ xs
  lookup∈ i = _ , fromList-∈ i

  lookup∈-index : ∀ {xs x} (x∈xs : x ∈ xs) → lookup∈ (index x∈xs) ≡ (x , x∈xs)
  lookup∈-index x∈xs = OverΣ.to-≡ (fromList-lookup∈ x∈xs)
    where
      fromList-lookup∈ : ∀ {xs x} (x∈xs : x ∈ xs) → OverΣ _≡_ (lookup∈ (index x∈xs)) (x , x∈xs)
      fromList-lookup∈ (here P.refl) = P.refl , P.refl
      fromList-lookup∈ (there x∈xs) = OverΣ.hom (P.cong there) (fromList-lookup∈ x∈xs)
