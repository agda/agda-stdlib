{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Data.Unit where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Unit.Base
import qualified MAlonzo.Code.Relation.Binary
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary

name4 = "Data.Unit._≟_"
d4 ::
  MAlonzo.Code.Agda.Builtin.Unit.T6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T6 ->
  MAlonzo.Code.Relation.Nullary.T14
d4 v0 v1 = du4
du4 :: MAlonzo.Code.Relation.Nullary.T14
du4 = coe (MAlonzo.Code.Relation.Nullary.C22 erased)
name6 = "Data.Unit._≤?_"
d6 ::
  MAlonzo.Code.Agda.Builtin.Unit.T6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T6 ->
  MAlonzo.Code.Relation.Nullary.T14
d6 v0 v1 = du6
du6 :: MAlonzo.Code.Relation.Nullary.T14
du6 = coe (MAlonzo.Code.Relation.Nullary.C22 erased)
name8 = "Data.Unit.total"
d8 ::
  MAlonzo.Code.Agda.Builtin.Unit.T6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T6 ->
  MAlonzo.Code.Data.Sum.Base.T14
    AgdaAny AgdaAny MAlonzo.Code.Data.Unit.Base.T10
    MAlonzo.Code.Data.Unit.Base.T10
d8 v0 v1 = du8
du8 ::
  MAlonzo.Code.Data.Sum.Base.T14
    AgdaAny AgdaAny MAlonzo.Code.Data.Unit.Base.T10
    MAlonzo.Code.Data.Unit.Base.T10
du8 = coe (MAlonzo.Code.Data.Sum.Base.C26 erased)
name10 = "Data.Unit.preorder"
d10 :: MAlonzo.Code.Relation.Binary.T74
d10 = coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du118
name12 = "Data.Unit.setoid"
d12 :: MAlonzo.Code.Relation.Binary.T128
d12 = coe MAlonzo.Code.Relation.Binary.PropositionalEquality.du98
name14 = "Data.Unit.decTotalOrder"
d14 :: MAlonzo.Code.Relation.Binary.T1078
d14
  = coe
      (\ v0 v1 v2 v3 -> MAlonzo.Code.Relation.Binary.C6485 v3) erased
      erased erased
      (MAlonzo.Code.Relation.Binary.C5939
         (coe
            (MAlonzo.Code.Relation.Binary.C5199
               (coe
                  (MAlonzo.Code.Relation.Binary.C1491
                     (coe
                        (MAlonzo.Code.Relation.Binary.C25
                           (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du68)
                           erased erased))
                     erased))
               (coe (\ v0 v1 -> MAlonzo.Code.Data.Sum.Base.C26 erased))))
         (coe (\ v0 v1 -> MAlonzo.Code.Relation.Nullary.C22 erased))
         (coe (\ v0 v1 -> MAlonzo.Code.Relation.Nullary.C22 erased)))
name28 = "Data.Unit.decSetoid"
d28 :: MAlonzo.Code.Relation.Binary.T200
d28 = coe (MAlonzo.Code.Relation.Binary.du1158 (coe d14))
name30 = "Data.Unit.poset"
d30 :: MAlonzo.Code.Relation.Binary.T304
d30
  = coe
      (MAlonzo.Code.Relation.Binary.du986
         (coe (MAlonzo.Code.Relation.Binary.du1148 (coe d14))))
