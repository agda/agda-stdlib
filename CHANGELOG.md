Version 1.4-dev
===============

The library has been tested using Agda version 2.6.1.

Highlights
----------

The library of Data.Nat.Binary  is continued.
	

	
Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

Deprecated names
----------------

	
New modules
-----------

Algebra.Morphisms.TwoMagmas, Data.Nat.Binary.Subtraction

	
Other major changes
-------------------


	
Other minor additions
---------------------

The following functions are added to Data.Nat.Properties:

∸-magma : Magma _ _  

	
The following functions are added to Data.Nat.Binary.Properties.
	

+-isSemigroup, +-semigroup,

x≡0⇒double[x]≡0 : x ≡ 0ᵇ → double x ≡ 0ᵇ                                
double-suc : double (suc x) ≡ 2ᵇ + double x                              
pred[x]+y≡x+pred[y] : x ≢ 0ᵇ → y ≢ 0ᵇ → (pred x) + y ≡  x + pred y    
x+suc[y]≡suc[x]+y : x + suc y ≡ suc x + y                               

	
       
	
