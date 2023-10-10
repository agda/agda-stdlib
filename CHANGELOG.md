Version 1.7.3
=============

The library has been tested using Agda 2.6.4.

* To avoid _large indices_ that are by default no longer allowed in Agda 2.6.4,
  universe levels have been increased in the following definitions:
  - `Data.Star.Decoration.DecoratedWith`
  - `Data.Star.Pointer.Pointer`
  - `Reflection.AnnotatedAST.Typeₐ`
  - `Reflection.AnnotatedAST.AnnotationFun`
