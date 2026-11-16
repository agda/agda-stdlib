Version 2.4.1
===========

The library has been tested using Agda 2.9.0.

Highlights
----------

* Certain functions incompatible with the updated semantics of irrelevant
  record fields have been removed.

* Fixity declarations which have no effect have been removed.

Non-backwards compatible changes
--------------------------------

* In `Data.Irrelevant`:
  * `_>>=_` has been removed.
