{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Function.Equality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial

name16 = "Function.Equality.Π"
d16 a0 a1 a2 a3 a4 a5 = ()
data T16
  = C29 (AgdaAny -> AgdaAny)
        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
name38 = "Function.Equality.Π._⟨$⟩_"
d38 :: T16 -> AgdaAny -> AgdaAny
d38 v0
  = case coe v0 of
      C29 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name40 = "Function.Equality.Π.cong"
d40 :: T16 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d40 v0
  = case coe v0 of
      C29 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name50 = "Function.Equality._⟶_"
d50 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128 -> ()
d50 = erased
name62 = "Function.Equality.id"
d62 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 -> T16
d62 v0 v1 v2 = du62
du62 :: T16
du62 = coe (C29 (coe (\ v0 -> v0)) (coe (\ v0 v1 v2 -> v2)))
name82 = "Function.Equality._∘_"
d82 ::
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 -> T16 -> T16 -> T16
d82 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du82 v7 v8
du82 :: T16 -> T16 -> T16
du82 v0 v1
  = coe
      (C29
         (coe (\ v2 -> coe d38 v0 (coe d38 v1 v2)))
         (coe
            (\ v2 v3 v4 ->
               coe d40 v0 (coe d38 v1 v2) (coe d38 v1 v3) (coe d40 v1 v2 v3 v4))))
name100 = "Function.Equality.const"
d100 ::
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 -> AgdaAny -> T16
d100 v0 v1 v2 v3 v4 = du100 v3 v4
du100 :: MAlonzo.Code.Relation.Binary.T128 -> AgdaAny -> T16
du100 v0 v1
  = coe
      (C29
         (coe (\ v2 -> v1))
         (coe
            (\ v2 v3 v4 ->
               coe
                 MAlonzo.Code.Relation.Binary.Core.d660
                 (MAlonzo.Code.Relation.Binary.d144 (coe v0)) v1)))
name116 = "Function.Equality.setoid"
d116 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58 ->
  MAlonzo.Code.Relation.Binary.T128
d116 v0 v1 v2 v3 v4 v5 = du116 v4 v5
du116 ::
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58 ->
  MAlonzo.Code.Relation.Binary.T128
du116 v0 v1
  = coe
      (\ v2 v3 v4 -> MAlonzo.Code.Relation.Binary.C971 v4) erased erased
      (MAlonzo.Code.Relation.Binary.Core.C2867
         (coe d40)
         (coe
            (\ v2 v3 v4 v5 v6 v7 ->
               coe
                 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d42
                 (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d78 (coe v1))
                 v6 v5 (coe d38 v2 v6) (coe d38 v3 v5)
                 (coe
                    v4 v6 v5
                    (coe
                       MAlonzo.Code.Relation.Binary.Core.d662
                       (MAlonzo.Code.Relation.Binary.d144 (coe v0)) v5 v6 v7))))
         (coe
            (\ v2 v3 v4 v5 v6 v7 v8 v9 ->
               coe
                 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d44
                 (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d78 (coe v1))
                 v7 v7 v8 (coe d38 v2 v7) (coe d38 v3 v7) (coe d38 v4 v8)
                 (coe
                    v5 v7 v7
                    (coe
                       MAlonzo.Code.Relation.Binary.Core.d660
                       (MAlonzo.Code.Relation.Binary.d144 (coe v0)) v7))
                 (coe v6 v7 v8 v9))))
name190 = "Function.Equality._⇨_"
d190 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128
d190 v0 v1 v2 v3 v4 v5 = du190 v4 v5
du190 ::
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128
du190 v0 v1
  = coe
      (du116
         (coe v0)
         (coe
            (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.du96
               (coe v1))))
name204 = "Function.Equality.≡-setoid"
d204 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58 ->
  MAlonzo.Code.Relation.Binary.T128
d204 v0 v1 v2 v3 v4 = du204 v4
du204 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.T58 ->
  MAlonzo.Code.Relation.Binary.T128
du204 v0
  = coe
      (\ v1 v2 v3 -> MAlonzo.Code.Relation.Binary.C971 v3) erased erased
      (MAlonzo.Code.Relation.Binary.Core.C2867
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d40
                 (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d78 (coe v0))
                 v2 (coe v1 v2)))
         (coe
            (\ v1 v2 v3 v4 ->
               coe
                 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d42
                 (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d78 (coe v0))
                 v4 v4 (coe v1 v4) (coe v2 v4) (coe v3 v4)))
         (coe
            (\ v1 v2 v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d44
                 (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.d78 (coe v0))
                 v6 v6 v6 (coe v1 v6) (coe v2 v6) (coe v3 v6) (coe v4 v6)
                 (coe v5 v6))))
name270 = "Function.Equality.flip"
d270 ::
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 -> T16 -> T16
d270 v0 v1 v2 v3 v4 v5 v6 v7 = du270 v3 v7
du270 :: MAlonzo.Code.Relation.Binary.T128 -> T16 -> T16
du270 v0 v1
  = coe
      (C29
         (coe
            (\ v2 ->
               C29
                 (coe (\ v3 -> coe d38 (coe d38 v1 v3) v2))
                 (coe
                    (\ v3 v4 v5 ->
                       coe
                         d40 v1 v3 v4 v5 v2 v2
                         (coe
                            MAlonzo.Code.Relation.Binary.Core.d660
                            (MAlonzo.Code.Relation.Binary.d144 (coe v0)) v2)))))
         (coe (\ v2 v3 v4 v5 v6 v7 -> coe d40 v1 v5 v6 v7 v2 v3 v4)))
