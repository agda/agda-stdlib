{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous

name24
  = "Relation.Binary.Indexed.Heterogeneous.Construct.Trivial._.Aᵢ"
d24 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Primitive.T4 -> () -> AgdaAny -> ()
d24 = erased
name32
  = "Relation.Binary.Indexed.Heterogeneous.Construct.Trivial._.isIndexedEquivalence"
d32 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Core.T644 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T20
d32 v0 v1 v2 v3 v4 v5 v6 = du32 v6
du32 ::
  MAlonzo.Code.Relation.Binary.Core.T644 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T20
du32 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.C43
         (coe (\ v1 -> MAlonzo.Code.Relation.Binary.Core.d660 (coe v0)))
         (coe (\ v1 v2 -> MAlonzo.Code.Relation.Binary.Core.d662 (coe v0)))
         (coe
            (\ v1 v2 v3 -> MAlonzo.Code.Relation.Binary.Core.d664 (coe v0))))
name58
  = "Relation.Binary.Indexed.Heterogeneous.Construct.Trivial._.isIndexedPreorder"
d58 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T106
d58 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du58 v8
du58 ::
  MAlonzo.Code.Relation.Binary.T16 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T106
du58 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.C799
         (coe (du32 (coe (MAlonzo.Code.Relation.Binary.d36 (coe v0)))))
         (coe (\ v1 v2 -> MAlonzo.Code.Relation.Binary.d38 (coe v0)))
         (coe (\ v1 v2 v3 -> MAlonzo.Code.Relation.Binary.d40 (coe v0))))
name96
  = "Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.indexedSetoid"
d96 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58
d96 v0 v1 v2 v3 v4 = du96 v4
du96 ::
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58
du96 v0
  = coe
      (\ v1 v2 v3 ->
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.C581 v3)
      erased erased
      (du32 (coe (MAlonzo.Code.Relation.Binary.d144 (coe v0))))
name130
  = "Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.indexedPreorder"
d130 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T74 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T166
d130 v0 v1 v2 v3 v4 v5 = du130 v5
du130 ::
  MAlonzo.Code.Relation.Binary.T74 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T166
du130 v0
  = coe
      (\ v1 v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.C1267 v4)
      erased erased erased
      (du58 (coe (MAlonzo.Code.Relation.Binary.d96 (coe v0))))
