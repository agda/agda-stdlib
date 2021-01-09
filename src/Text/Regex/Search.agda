------------------------------------------------------------------------
-- The Agda standard library
--
-- Regular expressions: search algorithms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecPoset)

module Text.Regex.Search {a e r} (P? : DecPoset a e r) where

open import Level using (_⊔_)
open import Data.Bool.Base using (if_then_else_; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (id; _∘′_; _∘_)

open import Data.List.Relation.Binary.Prefix.Heterogeneous
  using (Prefix; []; _∷_) hiding (module Prefix)
open import Data.List.Relation.Binary.Infix.Heterogeneous
  using (Infix; here; there) hiding (module Infix)
import Data.List.Relation.Binary.Infix.Heterogeneous.Properties as Infixₚ
open import Data.List.Relation.Binary.Pointwise
  as Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Suffix.Heterogeneous
  using (Suffix; here; there) hiding (module Suffix)

open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; Decidable; _⇒_)
open import Relation.Binary.PropositionalEquality hiding (preorder)

open DecPoset P? using (preorder) renaming (Carrier to A)
open import Text.Regex.Base preorder
open import Text.Regex.Properties P?
open import Text.Regex.Derivative.Brzozowski P?

------------------------------------------------------------------------
-- Type corresponding to a match

-- Users have control over whether the match should start at the beginning
-- or stop at the end. So we have a precise type of spans ensuring their
-- demands are respected
Span : ∀ {r} → Regex → Rel A r → Rel (List A) (a ⊔ r)
Span regex =
  if Regex.fromStart regex
  then if Regex.tillEnd regex
       then Pointwise
       else Prefix
  else if Regex.tillEnd regex
       then Suffix
       else Infix

-- All matches are selecting an infix sublist
toInfix : ∀ {r} {R : Rel A r} e → Span e R ⇒ Infix R
toInfix e with Regex.fromStart e | Regex.tillEnd e
... | true  | true  = Infixₚ.fromPointwise
... | true  | false = here
... | false | true  = Infixₚ.fromSuffix
... | false | false = id

-- A match is a list, a proof it matches the regular expression,
-- and a proof it is the right sort of sublist.
record Match {s} (R : Rel (List A) s) (xs : List A) (exp : Exp)
       : Set (a ⊔ e ⊔ r ⊔ s) where
  constructor mkMatch
  field
    list    : List A
    match   : list ∈ exp
    related : R list xs
open Match public

map : ∀ {r s} {R : Rel (List A) r} {S : Rel (List A) s} {xs ys e} →
      (∀ {a} → R a xs → S a ys) → Match R xs e → Match S ys e
map f (mkMatch ys ys∈e pys) = mkMatch ys ys∈e (f pys)

------------------------------------------------------------------------
-- Search algorithms

module Prefix where

  []ᴹ : ∀ {xs e} → [] ∈ e → Match (Prefix _≡_) xs e
  []ᴹ p = mkMatch [] p []

  []⁻¹ᴹ : ∀ {e} → Match (Prefix _≡_) [] e → [] ∈ e
  []⁻¹ᴹ (mkMatch .[] p []) = p

  _∷ᴹ_ : ∀ {xs e} x → Match (Prefix _≡_) xs (eat x e) → Match (Prefix _≡_) (x ∷ xs) e
  x ∷ᴹ (mkMatch ys ys∈e\x ys≤xs) = mkMatch (x ∷ ys) (eat-sound x _ ys∈e\x) (refl ∷ ys≤xs)

  _∷⁻¹ᴹ_ : ∀ {xs x e} → [] ∉ e →
           Match (Prefix _≡_) (x ∷ xs) e → Match (Prefix _≡_) xs (eat x e)
  []∉e ∷⁻¹ᴹ (mkMatch .[]       []∈e [])             = contradiction []∈e []∉e
  []∉e ∷⁻¹ᴹ (mkMatch (._ ∷ ys) ys∈e (refl ∷ ys≤xs)) = mkMatch ys (eat-complete _ _ ys∈e) ys≤xs

  shortest : Decidable (Match (Prefix _≡_))
  shortest xs e with []∈? e
  ... | yes []∈e = yes ([]ᴹ []∈e)
  shortest []       e | no []∉e = no ([]∉e ∘′ []⁻¹ᴹ)
  shortest (x ∷ xs) e | no []∉e with shortest xs (eat x e)
  ... | yes p = yes (x ∷ᴹ p)
  ... | no ¬p = no (¬p ∘ ([]∉e ∷⁻¹ᴹ_))

  longest : Decidable (Match (Prefix _≡_))
  longest []       e = map′ []ᴹ []⁻¹ᴹ ([]∈? e)
  longest (x ∷ xs) e with longest xs (eat x e)
  ... | yes p = yes (x ∷ᴹ p)
  ... | no ¬p with []∈? e
  ... | yes []∈e = yes ([]ᴹ []∈e)
  ... | no []∉e  = no (¬p ∘ ([]∉e ∷⁻¹ᴹ_))

module Infix where

  []⁻¹ᴹ : ∀ {e acc} → Match (Infix _≡_) [] e ⊎ Match (Prefix _≡_) [] acc → [] ∈ e ⊎ [] ∈ acc
  []⁻¹ᴹ (inj₁ (mkMatch .[] []∈e (here []))) = inj₁ []∈e
  []⁻¹ᴹ (inj₂ (mkMatch .[] []∈acc []))      = inj₂ []∈acc

  step : ∀ {e acc} x {xs} → Match (Infix _≡_) xs e ⊎ Match (Prefix _≡_) xs (eat x (e ∣ acc)) →
                            Match (Infix _≡_) (x ∷ xs) e ⊎ Match (Prefix _≡_) (x ∷ xs) acc
  step x (inj₁ (mkMatch ys ys∈e p)) = inj₁ (mkMatch ys ys∈e (there p))
  step {e} {acc} x (inj₂ (mkMatch ys ys∈e p)) with eat-sound x (e ∣ acc) ys∈e
  ... | sum (inj₁ xys∈e) = inj₁ (mkMatch (x ∷ ys) xys∈e (here (refl ∷ p)))
  ... | sum (inj₂ xys∈e) = inj₂ (mkMatch (x ∷ ys) xys∈e (refl ∷ p))

  step⁻¹ : ∀ {e acc} x {xs} →
           [] ∉ e → [] ∉ acc →
           Match (Infix _≡_) (x ∷ xs) e ⊎ Match (Prefix _≡_) (x ∷ xs) acc →
           Match (Infix _≡_) xs e ⊎ Match (Prefix _≡_) xs (eat x (e ∣ acc))
  -- can't possibly be the empty match
  step⁻¹ x []∉e []∉acc (inj₁ (mkMatch .[] ys∈e (here []))) = contradiction ys∈e []∉e
  step⁻¹ x []∉e []∉acc (inj₂ (mkMatch .[] ys∈e []))        = contradiction ys∈e []∉acc
  -- if it starts 'there', it's an infix solution
  step⁻¹ x []∉e []∉acc (inj₁ (mkMatch ys ys∈e (there p))) = inj₁ (mkMatch ys ys∈e p)
  -- if it starts 'here' we're in prefix territory
  step⁻¹ {e} {acc} x []∉e []∉acc (inj₁ (mkMatch (.x ∷ ys) ys∈e (here (refl ∷ p))))
    = inj₂ (mkMatch ys (eat-complete x (e ∣ acc) (sum (inj₁ ys∈e))) p)
  step⁻¹ {e} {acc} x []∉e []∉acc (inj₂ (mkMatch (.x ∷ ys) ys∈e (refl ∷ p)))
    = inj₂ (mkMatch ys (eat-complete x (e ∣ acc) (sum (inj₂ ys∈e))) p)

  -- search non-deterministically: at each step, the `acc` regex is changed
  -- to accomodate the fact the match may be starting just now
  searchND : ∀ xs e acc → [] ∉ e → Dec (Match (Infix _≡_) xs e ⊎ Match (Prefix _≡_) xs acc)
  searchND xs e acc []∉e with []∈? acc
  ... | yes []∈acc = yes (inj₂ (mkMatch [] []∈acc []))
  searchND [] e acc []∉e | no []∉acc = no ([ []∉e , []∉acc ]′ ∘′ []⁻¹ᴹ)
  searchND (x ∷ xs) e acc []∉e | no []∉acc
    = map′ (step x) (step⁻¹ x []∉e []∉acc) (searchND xs e (eat x (e ∣ acc)) []∉e)

  search : Decidable (Match (Infix _≡_))
  search xs e with []∈? e
  ... | yes []∈e = yes (mkMatch [] []∈e (here []))
  ... | no []∉e with searchND xs e ∅ []∉e
  ... | no ¬p        = no (¬p ∘′ inj₁)
  ... | yes (inj₁ p) = yes p
  ... | yes (inj₂ p) = contradiction (match p) ∉∅

module Whole where

  whole : ∀ xs e → xs ∈ e → Match (Pointwise _≡_) xs e
  whole xs e p = mkMatch xs p (Pointwise.refl refl)

  whole⁻¹ : ∀ xs e → Match (Pointwise _≡_) xs e → xs ∈ e
  whole⁻¹ xs e (mkMatch ys ys∈e p) with Pointwise.Pointwise-≡⇒≡ p
  whole⁻¹ xs e (mkMatch .xs xs∈e p) | refl = xs∈e

  search : Decidable (Match (Pointwise _≡_))
  search xs e = map′ (whole xs e) (whole⁻¹ xs e) (xs ∈? e)

module Suffix where

  []⁻¹ᴹ : ∀ {e acc} → Match (Suffix _≡_) [] e ⊎ Match (Pointwise _≡_) [] acc → [] ∈ e ⊎ [] ∈ acc
  []⁻¹ᴹ (inj₁ (mkMatch .[] ys∈e (here []))) = inj₁ ys∈e
  []⁻¹ᴹ (inj₂ (mkMatch .[] ys∈acc []))      = inj₂ ys∈acc

  step : ∀ {e acc} x {xs} →
         Match (Suffix _≡_) xs e ⊎ Match (Pointwise _≡_) xs (eat x (e ∣ acc)) →
         Match (Suffix _≡_) (x ∷ xs) e ⊎ Match (Pointwise _≡_) (x ∷ xs) acc
  step x (inj₁ (mkMatch ys ys∈e p)) = inj₁ (mkMatch ys ys∈e (there p))
  step {e} {acc} x (inj₂ (mkMatch ys ys∈e p)) with eat-sound x (e ∣ acc) ys∈e
  ... | sum (inj₁ xys∈e)   = inj₁ (mkMatch (x ∷ ys) xys∈e (here (refl ∷ p)))
  ... | sum (inj₂ xys∈acc) = inj₂ (mkMatch (x ∷ ys) xys∈acc (refl ∷ p))

  step⁻¹ : ∀ {e acc} x {xs} →
           Match (Suffix _≡_) (x ∷ xs) e ⊎ Match (Pointwise _≡_) (x ∷ xs) acc →
           Match (Suffix _≡_) xs e ⊎ Match (Pointwise _≡_) xs (eat x (e ∣ acc))
  -- match starts later
  step⁻¹ x (inj₁ (mkMatch ys ys∈e (there p))) = inj₁ (mkMatch ys ys∈e p)
  -- match starts here!
  step⁻¹ {e} {acc} x (inj₁ (mkMatch (.x ∷ ys) ys∈e (here (refl ∷ p))))
    = inj₂ (mkMatch ys (eat-complete x (e ∣ acc) (sum (inj₁ ys∈e))) p)
  step⁻¹ {e} {acc} x (inj₂ (mkMatch (.x ∷ ys) ys∈e (refl ∷ p)))
    = inj₂ (mkMatch ys (eat-complete x (e ∣ acc) (sum (inj₂ ys∈e))) p)

  searchND : ∀ xs e acc → Dec (Match (Suffix _≡_) xs e ⊎ Match (Pointwise _≡_) xs acc)
  searchND []       e acc with []∈? e | []∈? acc
  ... | yes []∈e | _          = yes (inj₁ (mkMatch [] []∈e (here [])))
  ... | _        | yes []∈acc = yes (inj₂ (mkMatch [] []∈acc []))
  ... | no []∉e  | no []∉acc  = no ([ []∉e , []∉acc ]′ ∘′ []⁻¹ᴹ)
  searchND (x ∷ xs) e acc
    = map′ (step x) (step⁻¹ x) (searchND xs e (eat x (e ∣ acc)))

  search : Decidable (Match (Suffix _≡_))
  search xs e with searchND xs e ∅
  ... | no ¬p        = no (¬p ∘′ inj₁)
  ... | yes (inj₁ p) = yes p
  ... | yes (inj₂ p) = contradiction (match p) ∉∅

------------------------------------------------------------------------
-- Search for the user-specified span

search : ∀ xs e → Dec (Match (Span e _≡_) xs (Regex.expression e))
search xs e with Regex.fromStart e | Regex.tillEnd e
... | true  | true  = Whole.search    xs (Regex.expression e)
... | true  | false = Prefix.shortest xs (Regex.expression e)
... | false | true  = Suffix.search   xs (Regex.expression e)
... | false | false = Infix.search    xs (Regex.expression e)
