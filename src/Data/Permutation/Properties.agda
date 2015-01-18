------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of permutations
------------------------------------------------------------------------


module Data.Permutation.Properties where

open import Data.Empty

open import Data.Nat
  renaming
    (ℕ to Nat ; zero to nz ; suc to ns)

open import Data.Fin
  renaming
    (zero to fz ; suc to fs)

open import Data.Fin.Properties

open import Data.Product

open import Data.Permutation

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  hiding ([_])

-- Properties of injective functions

∷-injective : {n m : Nat}{f g : Inj n m}{x y : Fin (ns m)}
  (e : _≡_ {A = Inj (ns n) (ns m)} (x ∷ f) (y ∷ g)) → (x ≡ y) × (f ≡ g)
∷-injective refl = refl , refl

inj-injective : {n m : Nat}{f : Inj n m}{x y : Fin n} → (< f > x ≡ < f > y) → x ≡ y
inj-injective {.0}      {m}       {[]}              {()}          e
inj-injective {.(ns n)} {.(ns m)} {_∷_ {n} {m} z p} {fz}   {fz}   e = refl
inj-injective {.(ns n)} {.(ns m)} {_∷_ {n} {m} z p} {fz}   {fs y} e = ⊥-elim (thin-no-confusion e)
inj-injective {.(ns n)} {.(ns m)} {_∷_ {n} {m} z p} {fs x} {fz}   e = ⊥-elim (thin-no-confusion (sym e))
inj-injective {.(ns n)} {.(ns m)} {_∷_ {n} {m} z p} {fs x} {fs y} e = cong fs (inj-injective {f = p} (thin-injective {z = z} e))

insert-lemma : {n m : Nat}(x : Fin (ns n))(y : Fin (ns m))(p : Inj n m) →
  < insert x y p > x ≡ y
insert-lemma fz      y []      = refl
insert-lemma (fs ()) y []
insert-lemma fz      y (z ∷ p) = refl
insert-lemma (fs x)  y (z ∷ p) = trans (cong (thin (thin y z)) (insert-lemma x (thick y z) p)) (thin-thin-thick y z)

delete-insert : {n m : Nat}(x : Fin (ns n))(y : Fin (ns m))(p : Inj n m) -> delete x (insert x y p) ≡ p
delete-insert fz      y []      = refl
delete-insert (fs ()) y []
delete-insert fz      y (z ∷ p) = refl
delete-insert (fs x)  y (z ∷ p) =
  cong₂ _∷_
    (trans (cong (thick (thin y z)) (insert-lemma x (thick y z) p)) (thick-thin-thick y z))
    (delete-insert x (thick y z) p)

insert-delete : {n m : Nat}(x : Fin (ns n))(p : Inj (ns n) (ns m)) -> insert x (< p > x) (delete x p) ≡ p
insert-delete fz            (x ∷ [])      = refl
insert-delete fz            (x ∷ (y ∷ p)) = refl
insert-delete (fs {nz} ())  (y ∷ p)
insert-delete (fs {ns n} x) (_∷_ {.(ns n)} {nz} y ())
insert-delete (fs {ns n} x) (_∷_ {.(ns n)} {ns m} y p) =
  cong₂ _∷_
    (thin-thin-thick y (< p > x))
    (trans (cong (λ z → insert x z (delete x p)) (thick-thin-thick y (< p > x))) (insert-delete x p))

id-is-id : {n : Nat}(x : Fin n) → < id > x ≡ x
id-is-id fz     = refl
id-is-id (fs x) = cong fs (id-is-id x)

id-left : {n m : Nat}(f : Inj n m) → id ∘ f ≡ f
id-left []      = refl
id-left (x ∷ p) = cong (_∷_ x) (id-left p)

delete-id : {n : Nat}(x : Fin (ns n)) → delete x id ≡ id
delete-id fz            = refl
delete-id (fs {nz} ())
delete-id (fs {ns n} x) = cong (_∷_ fz) (delete-id x)

id-right : {n m : Nat}(f : Inj n m) → f ∘ id ≡ f
id-right []                  = refl
id-right (fz ∷ p)            = cong (_∷_ fz) (id-right p)
id-right ((fs {nz} ()) ∷ p)
id-right ((fs {ns n} x) ∷ p) =
  cong₂ _∷_
    (id-is-id (fs x))
    (trans (cong (λ f → p ∘ (fz ∷ f)) (delete-id x)) (id-right p))

private
  fs-injective : {n : Nat}{f0 f1 : Fin n}(e : fs f0 ≡ fs f1) → f0 ≡ f1
  fs-injective refl = refl

  inj-thin : {n m : Nat}(p : Inj (ns n) (ns m))(x : Fin (ns n))(y : Fin n) →
    thin (< p > x) (< delete x p > y) ≡ < p > (thin x y)
  inj-thin (x ∷ p)                 fz     z      = refl
  inj-thin (_∷_ {nz} x p)          (fs y) ()
  inj-thin (_∷_ {ns n} {nz} x ())  (fs y) z
  inj-thin (_∷_ {ns n} {ns m} x p) (fs y) fz     = thin-thin-thick x (< p > y)
  inj-thin (_∷_ {ns n} {ns m} x p) (fs y) (fs z) =
    helper x (< p > y) (< p > (thin y z)) (< delete y p > z) (inj-thin p y z)
    where
    helper : {n : Nat}(x : Fin (ns (ns n)))(a c : Fin (ns n))
      (b : Fin n)(e : thin a b ≡ c) ->
      thin (thin x a) (thin (thick x a) b) ≡ thin x c
    helper fz     a      c      b      e = cong fs e
    helper (fs x) fz     c      b      e = cong (thin (fs x)) e
    helper (fs x) (fs a) fz     fz     e = refl
    helper (fs x) (fs a) fz     (fs b) ()
    helper (fs x) (fs a) (fs c) fz     ()
    helper (fs x) (fs a) (fs c) (fs b) e = cong fs (helper x a c b (fs-injective e))

  inj-thick : {n m : Nat}(f : Inj (ns n) (ns m))(x : Fin (ns n))(y : Fin n) →
    thick (< f > x) (< (delete x f) > y) ≡ < (delete (thin x y) f) > (thick x y)
  inj-thick (_∷_ {nz} x p)          y      ()
  inj-thick (_∷_ {ns n} {nz} x ())  y      z
  inj-thick (_∷_ {ns n} {ns m} x p) fz     z      = refl
  inj-thick (_∷_ {ns n} {ns m} x p) (fs y) fz     = thick-thin-thick x (< p > y)
  inj-thick (_∷_ {ns n} {ns m} x p) (fs y) (fs z) =
    trans (helper x (< p > y) (< delete y p > z))
      (cong₂ (λ a b → thin (thick x a) b) (inj-thin p y z) (inj-thick p y z))
    where
    helper : {n : Nat}(a : Fin (ns (ns n)))(b : Fin (ns n))(c : Fin n) ->
      thick (thin a b) (thin (thick a b) c) ≡ thin (thick a (thin b c)) (thick b c)
    helper fz     b      c      = refl
    helper (fs a) fz     fz     = refl
    helper (fs a) fz     (fs c) = refl
    helper (fs a) (fs b) fz     = refl
    helper (fs a) (fs b) (fs c) = cong fs (helper a b c)

  delete-swap : {n m : Nat}(x : Fin (ns (ns n)))(y : Fin (ns n))(f : Inj (ns (ns n)) (ns (ns m))) ->
    delete y (delete x f) ≡ delete (thick x y) (delete (thin x y) f)
  delete-swap                fz     fz      (z ∷ p) = refl
  delete-swap                fz     (fs y)  (z ∷ p) = refl
  delete-swap                (fs x) fz      (z ∷ p) = refl
  delete-swap {nz}           (fs x) (fs ()) (z ∷ p)
  delete-swap {ns n} {nz}    (fs x) (fs y)  (z ∷ x' ∷ ())
  delete-swap {ns n} {ns n'} (fs x) (fs y)  (z ∷ p) =
    cong₂ _∷_
      (trans (helper z (< p > x) (< delete x p > y)) (cong₂ (λ a b → thick (thick z a) b) (inj-thin p x y) (inj-thick p x y)))
      (delete-swap x y p)
    where
    helper : {n : Nat}(a : Fin (ns (ns n)))(b : Fin (ns n))(c : Fin n) →
      thick (thick a b) c ≡ thick (thick a (thin b c)) (thick b c)
    helper fz     fz     fz     = refl
    helper fz     fz     (fs c) = refl
    helper fz     (fs b) fz     = refl
    helper fz     (fs b) (fs c) = refl
    helper (fs a) fz     fz     = refl
    helper (fs a) fz     (fs c) = refl
    helper (fs a) (fs b) fz     = refl
    helper (fs a) (fs b) (fs c) = cong fs (helper a b c)

-- Injection is defined correctly w.r.t. composition

inj-correct : {n m k : Nat}(f : Inj n m)(g : Inj m k)(x : Fin n) →
  < f ∘ g > x ≡ < g > (< f > x)
inj-correct []      g       ()
inj-correct (x ∷ p) (y ∷ g) fz     = refl
inj-correct (x ∷ p) (y ∷ g) (fs z) =
  trans (cong (thin (< y ∷ g > x)) (inj-correct p _ z)) (inj-thin (y ∷ g) x (< p > z))

private
  ∘-rw : {n m k : Nat}(x : Fin (ns m))(f : Inj n m)(g : Inj (ns m) (ns k)) →
    (x ∷ f) ∘ g ≡ (< g > x) ∷ (f ∘ (delete x g))
  ∘-rw x f (y ∷ g) = refl

chain-rule : {n m k : Nat}(x : Fin (ns n))(f : Inj (ns n) (ns m))(g : Inj (ns m) (ns k)) → delete x (f ∘ g) ≡ (delete x f) ∘ (delete (< f > x) g)
chain-rule fz      (x ∷ f)                 (y ∷ g)                    = refl
chain-rule (fs ()) (_∷_ {nz} x f)          (y ∷ g)
chain-rule (fs z)  (_∷_ {ns n} {nz} x ())  (y ∷ g)
chain-rule (fs z)  (_∷_ {ns n} {ns m} x f) (_∷_ {.(ns m)} {nz} y ())
chain-rule (fs z)  (_∷_ {ns n} {ns m} x f) (_∷_ {.(ns m)} {ns k} y g) = trans
  (cong₂ _∷_
    (trans (cong (thick (< y ∷ g > x)) (inj-correct f (delete x (y ∷ g)) z)) (inj-thick (y ∷ g) x (< f > z)))
    (trans (chain-rule z f (delete x (y ∷ g))) (cong (λ w → delete z f ∘ w) (delete-swap x (< f > z) (y ∷ g)))))
  (sym (∘-rw (thick x (< f > z)) (delete z f) (delete (thin x (< f > z)) (y ∷ g))))

assoc : {n m k l : Nat}(f : Inj n m)(g : Inj m k)(h : Inj k l) →
  (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
assoc []      g       h       = refl
assoc (x ∷ p) (y ∷ g) (z ∷ h) =
  cong₂ _∷_
    (sym (inj-correct (y ∷ g) (z ∷ h) x))
    (trans (assoc p (delete x (y ∷ g)) (delete (< y ∷ g > x) (z ∷ h))) (sym (cong (_∘_ p) (chain-rule x (y ∷ g) (z ∷ h)))))

monomorphic : {n m k : Nat}(f1 f2 : Inj n m)(g : Inj m k) →
  (f1 ∘ g) ≡ (f2 ∘ g) → f1 ≡ f2
monomorphic []        []         g       e = refl
monomorphic (x1 ∷ p1) (x2 ∷ p2)  (y ∷ q) e with ∷-injective e
monomorphic (x1 ∷ p1) (x2 ∷ p2)  (y ∷ q) e | e1 , e2 with inj-injective {f = y ∷ q} {x = x1} {y = x2} e1
monomorphic (x1 ∷ p1) (.x1 ∷ p2) (y ∷ q) e | e1 , e2 | refl = cong (_∷_ x1) (monomorphic p1 p2 (delete x1 (y ∷ q)) e2)

-- Properties of permutations

-- Helper functions for epi proof

private
  epi-aux0 :
    {n : Nat}(x1 x2 : Fin n)(y1 y2 : Fin (ns n))
    (e1 :  thin y1 x1 ≡  thin y2 x2)
    (e2 : thick y1 x1 ≡ thick y2 x2) → (y1 ≡ y2) × (x1 ≡ x2)
  epi-aux0 x1             x2      fz      fz      e1 e2 = refl , (fs-injective e1)
  epi-aux0 x1             fz      fz      (fs y2) () e2
  epi-aux0 x1             (fs x2) fz      (fs y2) e1 ()
  epi-aux0 fz             x2      (fs y1) fz ()   e2
  epi-aux0 (fs i)         x2      (fs y1) fz      e1 ()
  epi-aux0 fz             fz      (fs y1) (fs y2) e1 e2 = (cong fs e2) , refl
  epi-aux0 fz             (fs x2) (fs y1) (fs y2) () e2
  epi-aux0 (fs x1)        fz      (fs y1) (fs y2) () e2
  epi-aux0 (fs {nz} ())   (fs x2) (fs y1) (fs y2) e1 e2
  epi-aux0 (fs {ns n} x1) (fs x2) (fs y1) (fs y2) e1 e2 with
    (epi-aux0 x1 x2 y1 y2 (fs-injective e1) (fs-injective e2))
  epi-aux0 (fs {ns n} x1) (fs x2) (fs y1) (fs y2) e1 e2 | ey , ex = (cong fs ey) , (cong fs ex)

  epi-aux1 :
    {n : Nat}(x : Fin (ns n))
    (g1 g2 : Permutation (ns n))
    (e1 : (< g1 > x) ≡ (< g2 > x))
    (e2 : delete x g1 ≡ delete x g2) → g1 ≡ g2
  epi-aux1 fz            (y1 ∷ g1) (y2 ∷ g2) e1 e2 = cong₂ _∷_ e1 e2
  epi-aux1 (fs {nz} ())  (y1 ∷ g1) (y2 ∷ g2) e1 e2
  epi-aux1 (fs {ns n} x) (y1 ∷ g1) (y2 ∷ g2) e1 e2 with ∷-injective e2
  epi-aux1 (fs {ns n} x) (y1 ∷ g1) (y2 ∷ g2) e1 e2 | e3 , e4 with epi-aux0 (< g1 > x) (< g2 > x) y1 y2 e1 e3
  epi-aux1 (fs {ns n} x) (y1 ∷ g1) (y2 ∷ g2) e1 e2 | e3 , e4 | e5 , e6 =
    cong₂ _∷_ e5 (epi-aux1 x g1 g2 e6 e4)

epimorphic : {n : Nat}(g : Permutation n)(f1 f2 : Permutation n) →
  (g ∘ f1) ≡ (g ∘ f2) → f1 ≡ f2
epimorphic []                  []        []        e = refl
epimorphic (x ∷ f)             (y1 ∷ g1) (y2 ∷ g2) e with ∷-injective e
epimorphic (fz ∷ f)            (y1 ∷ g1) (y2 ∷ g2) e | e1 , e2 =
  cong₂ _∷_ e1 (epimorphic f g1 g2 e2)
epimorphic ((fs {nz} ()) ∷ f)  (y1 ∷ g1) (y2 ∷ g2) e | e1 , e2
epimorphic ((fs {ns n} x) ∷ f) (y1 ∷ g1) (y2 ∷ g2) e | e1 , e2 with
  ∷-injective (epimorphic f (thick y1 (< g1 > x) ∷ delete x g1) (thick y2 (< g2 > x) ∷ delete x g2) e2)
epimorphic ((fs {ns n} x) ∷ f) (y1 ∷ g1) (y2 ∷ g2) e | e1 , e2 | e3 , e4 with
  epi-aux0 (< g1 > x) (< g2 > x) y1 y2 e1 e3
epimorphic ((fs {ns n} x) ∷ f) (y1 ∷ g1) (y2 ∷ g2) e | e1 , e2 | e3 , e4 | e5 , e6 =
  cong₂ _∷_ e5 (epi-aux1 x g1 g2 e6 e4)

-- Annihilator is defined correctly

ann-correct : {n : Nat}(p : Permutation (ns n)) → < p > (annihilator p) ≡ fz
ann-correct (fz ∷ p) = refl
ann-correct ((fs {nz} ()) ∷ p)
ann-correct ((fs {ns n} x) ∷ p) = cong (thin (fs x)) (ann-correct p)

-- Annihilator is unique

ann-unique : {n : Nat}(f : Permutation (ns n))(u : Fin (ns n))(e : < f > u ≡ fz) →
  u ≡ annihilator f
ann-unique (fz ∷ p)             fz     e = e
ann-unique (fz ∷ p)             (fs u) ()
ann-unique ((fs {nz} ()) ∷ p)   u      e
ann-unique ((fs {ns n} x)  ∷ p) fz     ()
ann-unique ((fs {ns n} x)  ∷ p) (fs u) e = cong fs (ann-unique p u (thin-zero {z = fs x} {x = < p > u} e))

-- Inverse is defined correctly w.r.t. composition

inv-left : {n : Nat}(f : Permutation n) → (f ⁻¹) ∘ f  ≡ id
inv-left [] = refl
inv-left (x ∷ p) = cong₂ _∷_ (ann-correct (x ∷ p)) (inv-left (delete (annihilator (x ∷ p)) (x ∷ p)))

inv-right : {n : Nat}(f : Permutation n) → f ∘ (f ⁻¹) ≡ id
inv-right f with inv-left f | id-left (f ⁻¹) | id-right (f ⁻¹)
inv-right f | e1 | e2 | e3 = epimorphic (f ⁻¹) (f ∘ f ⁻¹) id
  (trans (sym (assoc (f ⁻¹) f (f ⁻¹))) (trans (cong (λ g → g ∘ f ⁻¹) e1) (trans e2 (sym e3))))
