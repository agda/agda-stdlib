{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Function.Injection where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Equality
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality

name16 = "Function.Injection.Injective"
d16 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Function.Equality.T16 -> ()
d16 = erased
name84 = "Function.Injection.Injection"
d84 a0 a1 a2 a3 a4 a5 = ()
data T84
  = C395 MAlonzo.Code.Function.Equality.T16
         (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
name102 = "Function.Injection.Injection.to"
d102 :: T84 -> MAlonzo.Code.Function.Equality.T16
d102 v0
  = case coe v0 of
      C395 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name104 = "Function.Injection.Injection.injective"
d104 :: T84 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d104 v0
  = case coe v0 of
      C395 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name108 = "Function.Injection.Injection._._⟨$⟩_"
d108 :: T84 -> AgdaAny -> AgdaAny
d108 v0
  = coe (MAlonzo.Code.Function.Equality.d38 (coe (d102 (coe v0))))
name110 = "Function.Injection.Injection._.cong"
d110 :: T84 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d110 v0
  = coe (MAlonzo.Code.Function.Equality.d40 (coe (d102 (coe v0))))
name116 = "Function.Injection._↣_"
d116 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> () -> () -> ()
d116 = erased
name136 = "Function.Injection.injection"
d136 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  T84
d136 v0 v1 v2 v3 v4 v5 = du136 v4 v5
du136 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T12) ->
  T84
du136 v0 v1
  = coe
      (C395
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.du246
            (coe
               (\ v2 v3 v4 -> MAlonzo.Code.Relation.Binary.C971 v4) erased erased
               (MAlonzo.Code.Relation.Binary.Core.C2867 erased erased erased))
            v0)
         (coe v1))
name148 = "Function.Injection.id"
d148 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 -> T84
d148 v0 v1 v2 = du148
du148 :: T84
du148
  = coe
      (C395
         (coe MAlonzo.Code.Function.Equality.du62) (coe (\ v0 v1 v2 -> v2)))
name168 = "Function.Injection._∘_"
d168 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128 ->
  MAlonzo.Code.Relation.Binary.T128 -> T84 -> T84 -> T84
d168 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = du168 v9 v10
du168 :: T84 -> T84 -> T84
du168 v0 v1
  = coe
      (C395
         (coe
            (MAlonzo.Code.Function.Equality.du82
               (coe (d102 (coe v0))) (coe (d102 (coe v1)))))
         (coe
            (\ v2 v3 v4 ->
               coe
                 d104 v1 v2 v3
                 (coe
                    d104 v0 (coe MAlonzo.Code.Function.Equality.d38 (d102 (coe v1)) v2)
                    (coe MAlonzo.Code.Function.Equality.d38 (d102 (coe v1)) v3) v4))))
