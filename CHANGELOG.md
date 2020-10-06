Version 1.5-dev
===============

The library has been tested using Agda 2.6.1 and 2.6.1.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

* The internal build utilities package `lib.cabal` has been renamed
  `agda-stdlib-utils.cabal` to avoid potential conflict or confusion.
  Please note that the package is not intended for external use.

* The definition of `Data.Integer.Base`'s `_⊖_` was changed to use
  builtin operations, making it much faster.

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

Other major changes
-------------------

Other minor additions
---------------------

* Added new proofs in `Data.Integer.Properties`:

```agda
[1+m]⊖[1+n]≡m⊖n : suc m ⊖ suc n ≡ m ⊖ n
⊖-≤             : m ≤ n → m ⊖ n ≡ - + (n ∸ m)
-m+n≡n⊖m        : - (+ m) + + n ≡ n ⊖ m
m-n≡m⊖n         : + m + (- + n) ≡ m ⊖ n
```

* Added new definition in `Data.Nat.Base`:
```agda
_≤ᵇ_ : (m n : ℕ) → Bool
```

* Added new proofs in `Data.Nat.Properties`:
```agda
≤ᵇ⇒≤ : T (m ≤ᵇ n) → m ≤ n
≤⇒≤ᵇ : m ≤ n → T (m ≤ᵇ n)

<ᵇ-reflects-< : Reflects (m < n) (m <ᵇ n)
≤ᵇ-reflects-≤ : Reflects (m ≤ n) (m ≤ᵇ n)
```

* Added new proof in `Relation.Nullary.Reflects`:
```agda
fromEquivalence : (T b → P) → (P → T b) → Reflects P b
```
