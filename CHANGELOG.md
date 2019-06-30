Version 1.2-dev
===============

The library has been tested using Agda version 2.6.0.1.

Changes since 1.1:

Highlights
----------



Bug-fixes
---------



Other non-backwards compatible changes
--------------------------------------


#### Re-implementation of `Data.Bin`

* ``Data/Bin.agda`` and ``Data.Bin/*.agda``  of lib-1.0 are removed,
  added new ``Data.Bin.Base, Data.Bin.Properties``.
  This total change of the Bin part is done for the following reasons.
  1) Many necessary functions and proofs are added.
  2) After this has been done, the author noticed (decided) that the whole
   thing is implemented much simpler with using another representation for Bin:
   the one with certain three constructors. This representation is taken
   (with renaming the constructors) from the letter by Martin Escardo to the
   e-mail list. The referred code (of 2016) resides on
   http://www.cs.bham.ac.uk/~mhe/agda-new/BinaryNaturals.html

New modules
-----------
The following new modules have been added to the library:

* The following new modules have been added to the library:
  ```
  Data.Bin
  ```

Relocated modules
-----------------
The following modules have been moved as part of a drive to improve
usability and consistency across the library. The old modules still exist and
therefore all existing code should still work, however they have been deprecated
and, although not anticipated any time soon, they may eventually
be removed in some future release of the library. After the next release of Agda
automated warnings will be attached to these modules to discourage their use.


Deprecated names
----------------
The following deprecations have occurred as part of a drive to improve
consistency across the library. The deprecated names still exist and
therefore all existing code should still work, however use of the new names
is encouraged. Although not anticipated any time soon, they may eventually
be removed in some future release of the library. Automated warnings are
attached to all deprecated names to discourage their use.



Other minor additions
---------------------
