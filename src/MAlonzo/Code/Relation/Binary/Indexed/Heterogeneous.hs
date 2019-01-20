{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

name20
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedEquivalence"
d20 a0 a1 a2 a3 a4 a5 = ()
data T20
  = C43 (AgdaAny -> AgdaAny -> AgdaAny)
        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
        (AgdaAny ->
         AgdaAny ->
         AgdaAny ->
         AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
name40
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedEquivalence.refl"
d40 :: T20 -> AgdaAny -> AgdaAny -> AgdaAny
d40 v0
  = case coe v0 of
      C43 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name42
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedEquivalence.sym"
d42 ::
  T20 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d42 v0
  = case coe v0 of
      C43 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name44
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedEquivalence.trans"
d44 ::
  T20 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d44 v0
  = case coe v0 of
      C43 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name48
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedEquivalence.reflexive"
d48 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T20 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d48 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du48 v6 v7 v8
du48 :: T20 -> AgdaAny -> AgdaAny -> AgdaAny
du48 v0 v1 v2 = coe d40 v0 v1 v2
name58 = "Relation.Binary.Indexed.Heterogeneous.IndexedSetoid"
d58 a0 a1 a2 a3 = ()
newtype T58 = C581 T20
name74
  = "Relation.Binary.Indexed.Heterogeneous.IndexedSetoid.Carrier"
d74 :: T58 -> AgdaAny -> ()
d74 = erased
name76 = "Relation.Binary.Indexed.Heterogeneous.IndexedSetoid._≈_"
d76 :: T58 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d76 = erased
name78
  = "Relation.Binary.Indexed.Heterogeneous.IndexedSetoid.isEquivalence"
d78 :: T58 -> T20
d78 v0
  = case coe v0 of
      C581 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name82
  = "Relation.Binary.Indexed.Heterogeneous.IndexedSetoid._.refl"
d82 :: T58 -> AgdaAny -> AgdaAny -> AgdaAny
d82 v0 = coe (d40 (coe (d78 (coe v0))))
name84
  = "Relation.Binary.Indexed.Heterogeneous.IndexedSetoid._.reflexive"
d84 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T58 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d84 v0 v1 v2 v3 v4 = du84 v4
du84 ::
  T58 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du84 v0 = coe (\ v1 v2 v3 v4 -> du48 (coe (d78 (coe v0))) v1 v2)
name86
  = "Relation.Binary.Indexed.Heterogeneous.IndexedSetoid._.sym"
d86 ::
  T58 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d86 v0 = coe (d42 (coe (d78 (coe v0))))
name88
  = "Relation.Binary.Indexed.Heterogeneous.IndexedSetoid._.trans"
d88 ::
  T58 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d88 v0 = coe (d44 (coe (d78 (coe v0))))
name106 = "Relation.Binary.Indexed.Heterogeneous.IsIndexedPreorder"
d106 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T106
  = C799 T20
         (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
         (AgdaAny ->
          AgdaAny ->
          AgdaAny ->
          AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
name134
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedPreorder.isEquivalence"
d134 :: T106 -> T20
d134 v0
  = case coe v0 of
      C799 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name140
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedPreorder.reflexive"
d140 ::
  T106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d140 v0
  = case coe v0 of
      C799 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name142
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedPreorder.trans"
d142 ::
  T106 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d142 v0
  = case coe v0 of
      C799 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name146
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedPreorder.Eq.refl"
d146 :: T106 -> AgdaAny -> AgdaAny -> AgdaAny
d146 v0 = coe (d40 (coe (d134 (coe v0))))
name148
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedPreorder.Eq.reflexive"
d148 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T106 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d148 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du148 v8
du148 ::
  T106 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du148 v0 = coe (\ v1 v2 v3 v4 -> du48 (coe (d134 (coe v0))) v1 v2)
name150
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedPreorder.Eq.sym"
d150 ::
  T106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d150 v0 = coe (d42 (coe (d134 (coe v0))))
name152
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedPreorder.Eq.trans"
d152 ::
  T106 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d152 v0 = coe (d44 (coe (d134 (coe v0))))
name154
  = "Relation.Binary.Indexed.Heterogeneous.IsIndexedPreorder.refl"
d154 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  T106 -> AgdaAny -> AgdaAny -> AgdaAny
d154 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du154 v8 v9 v10
du154 :: T106 -> AgdaAny -> AgdaAny -> AgdaAny
du154 v0 v1 v2
  = coe d140 v0 v1 v1 v2 v2 (coe d40 (d134 (coe v0)) v1 v2)
name166 = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder"
d166 a0 a1 a2 a3 a4 = ()
newtype T166 = C1267 T106
name186
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder.Carrier"
d186 :: T166 -> AgdaAny -> ()
d186 = erased
name188
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._≈_"
d188 :: T166 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d188 = erased
name190
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._∼_"
d190 :: T166 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d190 = erased
name192
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder.isPreorder"
d192 :: T166 -> T106
d192 v0
  = case coe v0 of
      C1267 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name196
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._.isEquivalence"
d196 :: T166 -> T20
d196 v0 = coe (d134 (coe (d192 (coe v0))))
name198
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._.refl"
d198 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T166 -> AgdaAny -> AgdaAny -> AgdaAny
d198 v0 v1 v2 v3 v4 v5 = du198 v5
du198 :: T166 -> AgdaAny -> AgdaAny -> AgdaAny
du198 v0 = coe (du154 (coe (d192 (coe v0))))
name200
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._.reflexive"
d200 ::
  T166 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d200 v0 = coe (d140 (coe (d192 (coe v0))))
name202
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._.trans"
d202 ::
  T166 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d202 v0 = coe (d142 (coe (d192 (coe v0))))
name206
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._.Eq.refl"
d206 :: T166 -> AgdaAny -> AgdaAny -> AgdaAny
d206 v0 = coe (d40 (coe (d134 (coe (d192 (coe v0))))))
name208
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._.Eq.reflexive"
d208 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T166 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d208 v0 v1 v2 v3 v4 v5 = du208 v5
du208 ::
  T166 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du208 v0
  = let v1 = d192 (coe v0) in
    coe (\ v2 v3 v4 v5 -> du48 (coe (d134 (coe v1))) v2 v3)
name210
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._.Eq.sym"
d210 ::
  T166 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d210 v0 = coe (d42 (coe (d134 (coe (d192 (coe v0))))))
name212
  = "Relation.Binary.Indexed.Heterogeneous.IndexedPreorder._.Eq.trans"
d212 ::
  T166 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d212 v0 = coe (d44 (coe (d134 (coe (d192 (coe v0))))))
name214 = "Relation.Binary.Indexed.Heterogeneous.REL"
d214 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) -> MAlonzo.Code.Agda.Primitive.T4 -> ()
d214 = erased
name216 = "Relation.Binary.Indexed.Heterogeneous.Rel"
d216 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> ()) -> MAlonzo.Code.Agda.Primitive.T4 -> ()
d216 = erased
name218 = "Relation.Binary.Indexed.Heterogeneous.Setoid"
d218 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> ()
d218 = erased
name220 = "Relation.Binary.Indexed.Heterogeneous.IsEquivalence"
d220 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> ()) -> ()
d220 = erased
