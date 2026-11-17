Version 2.4.1
===========

The library has been tested using Agda 2.9.0.

Non-backwards compatible changes
--------------------------------

* In `Data.Irrelevant` the functions `_>>=_` and `recompute` have been removed as
  they were incompatible with the updated semantics of irrelevant record fields.

Backwards compatible changes
----------------------------

* Fixity declarations which have no effect have been removed.
