------------------------------------------------------------------------
-- The Agda standard library
--
-- List Zipper-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Zipper.Properties where

open import Data.List.Base as List using (List ; [] ; _∷_)
open import Data.List.Properties
open import Data.List.Zipper
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All using (All; just; nothing)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

-- Invariant: Zipper represents a given list
------------------------------------------------------------------------

module _ {a} {A : Set a} where

 -- Stability under moving left or right

 toList-left-identity : (zp : Zipper A) → All ((_≡_ on toList) zp) (left zp)
 toList-left-identity (mkZipper []        val) = nothing
 toList-left-identity (mkZipper (x ∷ ctx) val) = just $′ begin
   List.reverse (x ∷ ctx) List.++ val
     ≡⟨ cong (List._++ val) (unfold-reverse x ctx) ⟩
   (List.reverse ctx List.++ List.[ x ]) List.++ val
     ≡⟨ ++-assoc (List.reverse ctx) List.[ x ] val ⟩
   toList (mkZipper ctx (x ∷ val))
     ∎

 toList-right-identity : (zp : Zipper A) → All ((_≡_ on toList) zp) (right zp)
 toList-right-identity (mkZipper ctx [])        = nothing
 toList-right-identity (mkZipper ctx (x ∷ val)) = just $′ begin
   List.reverse ctx List.++ x ∷ val
     ≡⟨ sym (++-assoc (List.reverse ctx) List.[ x ] val) ⟩
   (List.reverse ctx List.++ List.[ x ]) List.++ val
     ≡⟨ cong (List._++ val) (sym (unfold-reverse x ctx)) ⟩
   List.reverse (x ∷ ctx) List.++ val
     ∎

 -- Applying reverse does correspond to reversing the represented list

 toList-reverse-commute : (zp : Zipper A) → toList (reverse zp) ≡ List.reverse (toList zp)
 toList-reverse-commute (mkZipper ctx val) = begin
   List.reverse val List.++ ctx
     ≡⟨ cong (List.reverse val List.++_) (sym (reverse-involutive ctx)) ⟩
   List.reverse val List.++ List.reverse (List.reverse ctx)
     ≡⟨ sym (reverse-++-commute (List.reverse ctx) val) ⟩
   List.reverse (List.reverse ctx List.++ val)
     ∎


-- Properties of the insertion functions
------------------------------------------------------------------------

 -- _ˡ++_ properties

 toList-ˡ++-commute : ∀ xs (zp : Zipper A) → toList (xs ˡ++ zp) ≡ xs List.++ toList zp
 toList-ˡ++-commute xs (mkZipper ctx val) = begin
   List.reverse (ctx List.++ List.reverse xs) List.++ val
     ≡⟨ cong (List._++ _) (reverse-++-commute ctx (List.reverse xs)) ⟩
   (List.reverse (List.reverse xs) List.++ List.reverse ctx) List.++ val
     ≡⟨ ++-assoc (List.reverse (List.reverse xs)) (List.reverse ctx) val ⟩
   List.reverse (List.reverse xs) List.++ List.reverse ctx List.++ val
     ≡⟨ cong (List._++ _) (reverse-involutive xs) ⟩
   xs List.++ List.reverse ctx List.++ val
     ∎

 ˡ++-assoc : ∀ xs ys (zp : Zipper A) → xs ˡ++ (ys ˡ++ zp) ≡ (xs List.++ ys) ˡ++ zp
 ˡ++-assoc xs ys (mkZipper ctx val) = cong (λ ctx → mkZipper ctx val) $ begin
   (ctx List.++ List.reverse ys) List.++ List.reverse xs
     ≡⟨ ++-assoc ctx _ _ ⟩
   ctx List.++ List.reverse ys List.++ List.reverse xs
     ≡⟨ cong (ctx List.++_) (sym (reverse-++-commute xs ys)) ⟩
   ctx List.++ List.reverse (xs List.++ ys)
     ∎

 -- _ʳ++_ properties

 ʳ++-assoc : ∀ xs ys (zp : Zipper A) → xs ʳ++ (ys ʳ++ zp) ≡ (ys List.++ xs) ʳ++ zp
 ʳ++-assoc xs ys (mkZipper ctx val) =  cong (λ ctx → mkZipper ctx val) $ begin
   List.reverse xs List.++ List.reverse ys List.++ ctx
     ≡⟨ sym (++-assoc (List.reverse xs) (List.reverse ys) ctx) ⟩
   (List.reverse xs List.++ List.reverse ys) List.++ ctx
     ≡⟨ cong (List._++ ctx) (sym (reverse-++-commute ys xs)) ⟩
   List.reverse (ys List.++ xs) List.++ ctx
     ∎

 -- _++ˡ_ properties

 ++ˡ-assoc : ∀ xs ys (zp : Zipper A) → zp ++ˡ xs ++ˡ ys ≡ zp ++ˡ (ys List.++ xs)
 ++ˡ-assoc xs ys (mkZipper ctx val) =  cong (mkZipper ctx) $ sym $ ++-assoc ys xs val

 -- _++ʳ_ properties

 toList-++ʳ-commute : ∀ (zp : Zipper A) xs → toList (zp ++ʳ xs) ≡ toList zp List.++ xs
 toList-++ʳ-commute (mkZipper ctx val) xs = begin
   List.reverse ctx List.++ val List.++ xs
     ≡⟨ sym (++-assoc (List.reverse ctx) val xs) ⟩
   (List.reverse ctx List.++ val) List.++ xs
     ∎

 ++ʳ-assoc : ∀ xs ys (zp : Zipper A) → zp ++ʳ xs ++ʳ ys ≡ zp ++ʳ (xs List.++ ys)
 ++ʳ-assoc xs ys (mkZipper ctx val) = cong (mkZipper ctx) $ ++-assoc val xs ys


-- List-like operations indeed correspond to their counterparts
------------------------------------------------------------------------

module _ {a b} {A : Set a} {B : Set b} where

 toList-map-commute : ∀ (f : A → B) zp → toList (map f zp) ≡ List.map f (toList zp)
 toList-map-commute f zp@(mkZipper ctx val) = begin
   List.reverse (List.map f ctx) List.++ List.map f val
     ≡⟨ cong (List._++ _) (sym (reverse-map-commute f ctx)) ⟩
   List.map f (List.reverse ctx) List.++ List.map f val
     ≡⟨ sym (map-++-commute f (List.reverse ctx) val) ⟩
   List.map f (List.reverse ctx List.++ val)
     ∎

 toList-foldr-commute : ∀ (c : A → B → B) n zp → foldr c n zp ≡ List.foldr c n (toList zp)
 toList-foldr-commute c n (mkZipper ctx val) = begin
   List.foldl (flip c) (List.foldr c n val) ctx
     ≡⟨ sym (reverse-foldr c (List.foldr c n val) ctx) ⟩
   List.foldr c (List.foldr c n val) (List.reverse ctx)
     ≡⟨ sym (foldr-++ c n (List.reverse ctx) val) ⟩
   List.foldr c n (List.reverse ctx List.++ val)
     ∎
