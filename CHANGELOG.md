Version TODO
============

The library has been tested using Agda version 2.5.4.1.

Important changes since 0.17:

Non-backwards compatible changes
--------------------------------

* The type family `Data.Container.ν` is now defined using `Codata.M.M` rather than `Codata.Musical.M.M`.

* Functions called `fromMusical` and `toMusical` were moved from modules under `Codata` to modules under `Codata.Musical`:
  * From `Codata.Cofin` to `Codata.Musical.Cofin`.
  * From `Codata.Colist` to `Codata.Musical.Colist`.
  * From `Codata.Conat` to `Codata.Musical.Conat`.
  * From `Codata.Covec` to `Codata.Musical.Covec`.
  * From `Codata.M` to `Codata.Musical.M`.
  * From `Codata.Stream` to `Codata.Musical.Stream`.

Other major changes
-------------------

Deprecated features
-------------------

Other minor additions
---------------------
