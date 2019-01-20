{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Nullary.Decidable where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Function.Equivalence
import qualified MAlonzo.Code.Function.Injection
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Nullary

name10 = "Relation.Nullary.Decidable.⌊_⌋"
d10 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Nullary.T14 -> Bool
d10 v0 v1 v2 = du10 v2
du10 :: MAlonzo.Code.Relation.Nullary.T14 -> Bool
du10 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.C22 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C10
      MAlonzo.Code.Relation.Nullary.C26
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C8
      _ -> MAlonzo.RTE.mazUnreachableError
name16 = "Relation.Nullary.Decidable.True"
d16 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Nullary.T14 -> ()
d16 = erased
name24 = "Relation.Nullary.Decidable.False"
d24 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Nullary.T14 -> ()
d24 = erased
name34 = "Relation.Nullary.Decidable.toWitness"
d34 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Nullary.T14 -> AgdaAny -> AgdaAny
d34 v0 v1 v2 v3 = du34 v2
du34 :: MAlonzo.Code.Relation.Nullary.T14 -> AgdaAny
du34 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.C22 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name44 = "Relation.Nullary.Decidable.fromWitness"
d44 :: MAlonzo.Code.Relation.Nullary.T14 -> AgdaAny -> AgdaAny
d44 = erased
name56 = "Relation.Nullary.Decidable.toWitnessFalse"
d56 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Relation.Nullary.T14 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d56 = erased
name66 = "Relation.Nullary.Decidable.fromWitnessFalse"
d66 ::
  MAlonzo.Code.Relation.Nullary.T14 ->
  (AgdaAny -> MAlonzo.Code.Data.Empty.T4) -> AgdaAny
d66 = erased
name80 = "Relation.Nullary.Decidable.map"
d80 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  MAlonzo.Code.Function.Equivalence.T16 ->
  MAlonzo.Code.Relation.Nullary.T14 ->
  MAlonzo.Code.Relation.Nullary.T14
d80 v0 v1 v2 v3 v4 v5 = du80 v4 v5
du80 ::
  MAlonzo.Code.Function.Equivalence.T16 ->
  MAlonzo.Code.Relation.Nullary.T14 ->
  MAlonzo.Code.Relation.Nullary.T14
du80 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.C22 v2
        -> coe
             (MAlonzo.Code.Relation.Nullary.C22
                (coe
                   MAlonzo.Code.Function.Equality.d38
                   (MAlonzo.Code.Function.Equivalence.d34 (coe v0)) v2))
      MAlonzo.Code.Relation.Nullary.C26
        -> coe (\ v3 -> MAlonzo.Code.Relation.Nullary.C26) erased
      _ -> MAlonzo.RTE.mazUnreachableError
name98 = "Relation.Nullary.Decidable.map′"
d98 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.T14 ->
  MAlonzo.Code.Relation.Nullary.T14
d98 v0 v1 v2 v3 v4 v5 = du98 v4 v5
du98 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.T14 ->
  MAlonzo.Code.Relation.Nullary.T14
du98 v0 v1
  = coe
      (du80
         (coe (MAlonzo.Code.Function.Equivalence.du56 (coe v0) (coe v1))))
name122 = "Relation.Nullary.Decidable._._._≈_"
d122 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128 -> AgdaAny -> AgdaAny -> ()
d122 = erased
name128 = "Relation.Nullary.Decidable._.via-injection"
d128 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Function.Injection.T84 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d128 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du128 v6 v7 v8 v9
du128 ::
  MAlonzo.Code.Function.Injection.T84 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du128 v0 v1 v2 v3
  = let v4
          = coe
              v1
              (coe
                 MAlonzo.Code.Function.Equality.d38
                 (MAlonzo.Code.Function.Injection.d102 (coe v0)) v2)
              (coe
                 MAlonzo.Code.Function.Equality.d38
                 (MAlonzo.Code.Function.Injection.d102 (coe v0)) v3) in
    case coe v4 of
      MAlonzo.Code.Relation.Nullary.C22 v5
        -> coe
             (MAlonzo.Code.Relation.Nullary.C22
                (coe MAlonzo.Code.Function.Injection.d104 v0 v2 v3 v5))
      MAlonzo.Code.Relation.Nullary.C26
        -> coe (\ v6 -> MAlonzo.Code.Relation.Nullary.C26) erased
      _ -> MAlonzo.RTE.mazUnreachableError
name172 = "Relation.Nullary.Decidable._.From-yes"
d172 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Nullary.T14 -> ()
d172 = erased
name176 = "Relation.Nullary.Decidable._.from-yes"
d176 :: MAlonzo.Code.Relation.Nullary.T14 -> AgdaAny
d176 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.C22 v1 -> coe v1
      MAlonzo.Code.Relation.Nullary.C26
        -> coe (MAlonzo.Code.Level.C20 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
name180 = "Relation.Nullary.Decidable._.From-no"
d180 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Nullary.T14 -> ()
d180 = erased
name184 = "Relation.Nullary.Decidable._.from-no"
d184 :: MAlonzo.Code.Relation.Nullary.T14 -> AgdaAny
d184 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.C22 v1
        -> coe (MAlonzo.Code.Level.C20 erased)
      MAlonzo.Code.Relation.Nullary.C26 -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
