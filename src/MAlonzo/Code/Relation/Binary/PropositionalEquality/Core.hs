{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.PropositionalEquality.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Core

name12 = "Relation.Binary.PropositionalEquality.Core._≢_"
d12 ::
  MAlonzo.Code.Agda.Primitive.T4 -> () -> AgdaAny -> AgdaAny -> ()
d12 = erased
name26 = "Relation.Binary.PropositionalEquality.Core._.sym"
d26 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d26 = erased
name28 = "Relation.Binary.PropositionalEquality.Core._.trans"
d28 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T12
d28 = erased
name34 = "Relation.Binary.PropositionalEquality.Core._.subst"
d34 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny -> AgdaAny
d34 v0 v1 v2 v3 v4 v5 v6 v7 = du34 v7
du34 :: AgdaAny -> AgdaAny
du34 v0 = coe v0
name44 = "Relation.Binary.PropositionalEquality.Core._.respˡ"
d44 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny -> AgdaAny
d44 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du44 v8
du44 :: AgdaAny -> AgdaAny
du44 v0 = coe v0
name54 = "Relation.Binary.PropositionalEquality.Core._.respʳ"
d54 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny -> AgdaAny
d54 v0 v1 v2 v3 v4 v5 v6 v7 v8 = du54 v8
du54 :: AgdaAny -> AgdaAny
du54 v0 = coe v0
name64 = "Relation.Binary.PropositionalEquality.Core._.resp₂"
d64 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  (AgdaAny -> AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d64 v0 v1 v2 v3 = du64
du64 :: MAlonzo.Code.Agda.Builtin.Sigma.T14
du64
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32
         (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4)))
name68
  = "Relation.Binary.PropositionalEquality.Core._.isEquivalence"
d68 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Relation.Binary.Core.T644
d68 v0 v1 = du68
du68 :: MAlonzo.Code.Relation.Binary.Core.T644
du68
  = coe
      (MAlonzo.Code.Relation.Binary.Core.C2867 erased erased erased)
