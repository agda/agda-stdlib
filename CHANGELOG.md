Version 1.7.3
=============

The library has been tested using Agda 2.6.3 & 2.6.4.

* To avoid _large indices_ that are by default no longer allowed in Agda 2.6.4,
  universe levels have been increased in the following definitions:
  - `Data.Star.Decoration.DecoratedWith`
  - `Data.Star.Pointer.Pointer`
  - `Reflection.AnnotatedAST.Typeₐ`
  - `Reflection.AnnotatedAST.AnnotationFun`

* The following aliases have been added:
  - `IO.Primitive.pure` as alias for `IO.Primitive.return`
  - modules `Effect.*` as aliases for modules `Category.*`

  These allow to address said objects with the new name they will have in v2.0 of the library,
  to ease the transition from v1.7.3 to v2.0.
