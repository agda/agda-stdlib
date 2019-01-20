{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Nullary

name16 = "Relation.Binary.IsPreorder"
d16 a0 a1 a2 a3 a4 a5 = ()
data T16
  = C25 MAlonzo.Code.Relation.Binary.Core.T644
        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
name36 = "Relation.Binary.IsPreorder.isEquivalence"
d36 :: T16 -> MAlonzo.Code.Relation.Binary.Core.T644
d36 v0
  = case coe v0 of
      C25 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name38 = "Relation.Binary.IsPreorder.reflexive"
d38 :: T16 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d38 v0
  = case coe v0 of
      C25 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name40 = "Relation.Binary.IsPreorder.trans"
d40 ::
  T16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d40 v0
  = case coe v0 of
      C25 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name44 = "Relation.Binary.IsPreorder.Eq.refl"
d44 :: T16 -> AgdaAny -> AgdaAny
d44 v0
  = coe (MAlonzo.Code.Relation.Binary.Core.d660 (coe (d36 (coe v0))))
name46 = "Relation.Binary.IsPreorder.Eq.reflexive"
d46 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d46 v0 v1 v2 v3 v4 v5 v6 = du46 v6
du46 ::
  T16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du46 v0
  = coe
      (\ v1 v2 v3 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d36 (coe v0))) v1)
name48 = "Relation.Binary.IsPreorder.Eq.sym"
d48 :: T16 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d48 v0
  = coe (MAlonzo.Code.Relation.Binary.Core.d662 (coe (d36 (coe v0))))
name50 = "Relation.Binary.IsPreorder.Eq.trans"
d50 ::
  T16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d50 v0
  = coe (MAlonzo.Code.Relation.Binary.Core.d664 (coe (d36 (coe v0))))
name52 = "Relation.Binary.IsPreorder.refl"
d52 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T16 -> AgdaAny -> AgdaAny
d52 v0 v1 v2 v3 v4 v5 v6 v7 = du52 v6 v7
du52 :: T16 -> AgdaAny -> AgdaAny
du52 v0 v1
  = coe
      d38 v0 v1 v1
      (coe MAlonzo.Code.Relation.Binary.Core.d660 (d36 (coe v0)) v1)
name54 = "Relation.Binary.IsPreorder.∼-respˡ-≈"
d54 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d54 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du54 v6 v7 v8 v9 v10 v11
du54 ::
  T16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du54 v0 v1 v2 v3 v4 v5
  = coe
      d40 v0 v3 v2 v1
      (coe
         d38 v0 v3 v2
         (coe
            MAlonzo.Code.Relation.Binary.Core.d662 (d36 (coe v0)) v2 v3 v4))
      v5
name60 = "Relation.Binary.IsPreorder.∼-respʳ-≈"
d60 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d60 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du60 v6 v7 v8 v9 v10 v11
du60 ::
  T16 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du60 v0 v1 v2 v3 v4 v5
  = coe d40 v0 v1 v2 v3 v5 (coe d38 v0 v2 v3 v4)
name66 = "Relation.Binary.IsPreorder.∼-resp-≈"
d66 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T16 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d66 v0 v1 v2 v3 v4 v5 v6 = du66 v6
du66 :: T16 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du66 v0
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32
         (coe (du60 (coe v0))) (coe (du54 (coe v0))))
name74 = "Relation.Binary.Preorder"
d74 a0 a1 a2 = ()
newtype T74 = C739 T16
name90 = "Relation.Binary.Preorder.Carrier"
d90 :: T74 -> ()
d90 = erased
name92 = "Relation.Binary.Preorder._≈_"
d92 :: T74 -> AgdaAny -> AgdaAny -> ()
d92 = erased
name94 = "Relation.Binary.Preorder._∼_"
d94 :: T74 -> AgdaAny -> AgdaAny -> ()
d94 = erased
name96 = "Relation.Binary.Preorder.isPreorder"
d96 :: T74 -> T16
d96 v0
  = case coe v0 of
      C739 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name100 = "Relation.Binary.Preorder._.isEquivalence"
d100 :: T74 -> MAlonzo.Code.Relation.Binary.Core.T644
d100 v0 = coe (d36 (coe (d96 (coe v0))))
name102 = "Relation.Binary.Preorder._.refl"
d102 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T74 -> AgdaAny -> AgdaAny
d102 v0 v1 v2 v3 = du102 v3
du102 :: T74 -> AgdaAny -> AgdaAny
du102 v0 = coe (du52 (coe (d96 (coe v0))))
name104 = "Relation.Binary.Preorder._.reflexive"
d104 :: T74 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d104 v0 = coe (d38 (coe (d96 (coe v0))))
name106 = "Relation.Binary.Preorder._.trans"
d106 ::
  T74 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d106 v0 = coe (d40 (coe (d96 (coe v0))))
name108 = "Relation.Binary.Preorder._.∼-resp-≈"
d108 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T74 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d108 v0 v1 v2 v3 = du108 v3
du108 :: T74 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du108 v0 = coe (du66 (coe (d96 (coe v0))))
name110 = "Relation.Binary.Preorder._.∼-respʳ-≈"
d110 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T74 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d110 v0 v1 v2 v3 = du110 v3
du110 ::
  T74 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du110 v0 = coe (du60 (coe (d96 (coe v0))))
name112 = "Relation.Binary.Preorder._.∼-respˡ-≈"
d112 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T74 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d112 v0 v1 v2 v3 = du112 v3
du112 ::
  T74 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du112 v0 = coe (du54 (coe (d96 (coe v0))))
name116 = "Relation.Binary.Preorder._.Eq.refl"
d116 :: T74 -> AgdaAny -> AgdaAny
d116 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d96 (coe v0))))))
name118 = "Relation.Binary.Preorder._.Eq.reflexive"
d118 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T74 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d118 v0 v1 v2 v3 = du118 v3
du118 ::
  T74 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du118 v0
  = let v1 = d96 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d36 (coe v1))) v2)
name120 = "Relation.Binary.Preorder._.Eq.sym"
d120 :: T74 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d120 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d96 (coe v0))))))
name122 = "Relation.Binary.Preorder._.Eq.trans"
d122 ::
  T74 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d122 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d96 (coe v0))))))
name128 = "Relation.Binary.Setoid"
d128 a0 a1 = ()
newtype T128 = C971 MAlonzo.Code.Relation.Binary.Core.T644
name140 = "Relation.Binary.Setoid.Carrier"
d140 :: T128 -> ()
d140 = erased
name142 = "Relation.Binary.Setoid._≈_"
d142 :: T128 -> AgdaAny -> AgdaAny -> ()
d142 = erased
name144 = "Relation.Binary.Setoid.isEquivalence"
d144 :: T128 -> MAlonzo.Code.Relation.Binary.Core.T644
d144 v0
  = case coe v0 of
      C971 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name148 = "Relation.Binary.Setoid._.refl"
d148 :: T128 -> AgdaAny -> AgdaAny
d148 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660 (coe (d144 (coe v0))))
name150 = "Relation.Binary.Setoid._.reflexive"
d150 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T128 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d150 v0 v1 v2 = du150 v2
du150 ::
  T128 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du150 v0
  = coe
      (\ v1 v2 v3 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d144 (coe v0))) v1)
name152 = "Relation.Binary.Setoid._.sym"
d152 :: T128 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d152 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662 (coe (d144 (coe v0))))
name154 = "Relation.Binary.Setoid._.trans"
d154 ::
  T128 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d154 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664 (coe (d144 (coe v0))))
name156 = "Relation.Binary.Setoid.isPreorder"
d156 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T128 -> T16
d156 v0 v1 v2 = du156 v2
du156 :: T128 -> T16
du156 v0
  = coe
      (C25
         (coe MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du68)
         (coe
            (\ v1 v2 v3 ->
               MAlonzo.Code.Relation.Binary.Core.du666 (coe (d144 (coe v0))) v1))
         (coe
            (MAlonzo.Code.Relation.Binary.Core.d664 (coe (d144 (coe v0))))))
name158 = "Relation.Binary.Setoid.preorder"
d158 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T128 -> T74
d158 v0 v1 v2 = du158 v2
du158 :: T128 -> T74
du158 v0
  = coe
      (\ v1 v2 v3 v4 -> C739 v4) erased erased erased (du156 (coe v0))
name168 = "Relation.Binary.IsDecEquivalence"
d168 a0 a1 a2 a3 = ()
data T168
  = C1173 MAlonzo.Code.Relation.Binary.Core.T644
          (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14)
name182 = "Relation.Binary.IsDecEquivalence.isEquivalence"
d182 :: T168 -> MAlonzo.Code.Relation.Binary.Core.T644
d182 v0
  = case coe v0 of
      C1173 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name184 = "Relation.Binary.IsDecEquivalence._≟_"
d184 ::
  T168 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d184 v0
  = case coe v0 of
      C1173 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name188 = "Relation.Binary.IsDecEquivalence._.refl"
d188 :: T168 -> AgdaAny -> AgdaAny
d188 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660 (coe (d182 (coe v0))))
name190 = "Relation.Binary.IsDecEquivalence._.reflexive"
d190 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T168 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d190 v0 v1 v2 v3 v4 = du190 v4
du190 ::
  T168 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du190 v0
  = coe
      (\ v1 v2 v3 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v0))) v1)
name192 = "Relation.Binary.IsDecEquivalence._.sym"
d192 :: T168 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d192 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662 (coe (d182 (coe v0))))
name194 = "Relation.Binary.IsDecEquivalence._.trans"
d194 ::
  T168 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d194 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664 (coe (d182 (coe v0))))
name200 = "Relation.Binary.DecSetoid"
d200 a0 a1 = ()
newtype T200 = C1311 T168
name212 = "Relation.Binary.DecSetoid.Carrier"
d212 :: T200 -> ()
d212 = erased
name214 = "Relation.Binary.DecSetoid._≈_"
d214 :: T200 -> AgdaAny -> AgdaAny -> ()
d214 = erased
name216 = "Relation.Binary.DecSetoid.isDecEquivalence"
d216 :: T200 -> T168
d216 v0
  = case coe v0 of
      C1311 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name220 = "Relation.Binary.DecSetoid._._≟_"
d220 ::
  T200 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d220 v0 = coe (d184 (coe (d216 (coe v0))))
name222 = "Relation.Binary.DecSetoid._.isEquivalence"
d222 :: T200 -> MAlonzo.Code.Relation.Binary.Core.T644
d222 v0 = coe (d182 (coe (d216 (coe v0))))
name224 = "Relation.Binary.DecSetoid._.refl"
d224 :: T200 -> AgdaAny -> AgdaAny
d224 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d182 (coe (d216 (coe v0))))))
name226 = "Relation.Binary.DecSetoid._.reflexive"
d226 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T200 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d226 v0 v1 v2 = du226 v2
du226 ::
  T200 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du226 v0
  = let v1 = d216 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v1))) v2)
name228 = "Relation.Binary.DecSetoid._.sym"
d228 :: T200 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d228 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d182 (coe (d216 (coe v0))))))
name230 = "Relation.Binary.DecSetoid._.trans"
d230 ::
  T200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d230 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d182 (coe (d216 (coe v0))))))
name232 = "Relation.Binary.DecSetoid.setoid"
d232 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T200 -> T128
d232 v0 v1 v2 = du232 v2
du232 :: T200 -> T128
du232 v0
  = coe
      (\ v1 v2 v3 -> C971 v3) erased erased (d182 (coe (d216 (coe v0))))
name236 = "Relation.Binary.DecSetoid._.preorder"
d236 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T200 -> T74
d236 v0 v1 v2 = du236 v2
du236 :: T200 -> T74
du236 v0 = coe (du158 (coe (du232 (coe v0))))
name250 = "Relation.Binary.IsPartialOrder"
d250 a0 a1 a2 a3 a4 a5 = ()
data T250
  = C1491 T16 (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
name268 = "Relation.Binary.IsPartialOrder.isPreorder"
d268 :: T250 -> T16
d268 v0
  = case coe v0 of
      C1491 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name270 = "Relation.Binary.IsPartialOrder.antisym"
d270 :: T250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d270 v0
  = case coe v0 of
      C1491 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name274 = "Relation.Binary.IsPartialOrder._.isEquivalence"
d274 :: T250 -> MAlonzo.Code.Relation.Binary.Core.T644
d274 v0 = coe (d36 (coe (d268 (coe v0))))
name276 = "Relation.Binary.IsPartialOrder._.refl"
d276 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T250 -> AgdaAny -> AgdaAny
d276 v0 v1 v2 v3 v4 v5 v6 = du276 v6
du276 :: T250 -> AgdaAny -> AgdaAny
du276 v0 = coe (du52 (coe (d268 (coe v0))))
name278 = "Relation.Binary.IsPartialOrder._.reflexive"
d278 :: T250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d278 v0 = coe (d38 (coe (d268 (coe v0))))
name280 = "Relation.Binary.IsPartialOrder._.trans"
d280 ::
  T250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d280 v0 = coe (d40 (coe (d268 (coe v0))))
name282 = "Relation.Binary.IsPartialOrder._.∼-resp-≈"
d282 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T250 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d282 v0 v1 v2 v3 v4 v5 v6 = du282 v6
du282 :: T250 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du282 v0 = coe (du66 (coe (d268 (coe v0))))
name284 = "Relation.Binary.IsPartialOrder._.∼-respʳ-≈"
d284 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d284 v0 v1 v2 v3 v4 v5 v6 = du284 v6
du284 ::
  T250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du284 v0 = coe (du60 (coe (d268 (coe v0))))
name286 = "Relation.Binary.IsPartialOrder._.∼-respˡ-≈"
d286 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d286 v0 v1 v2 v3 v4 v5 v6 = du286 v6
du286 ::
  T250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du286 v0 = coe (du54 (coe (d268 (coe v0))))
name290 = "Relation.Binary.IsPartialOrder._.Eq.refl"
d290 :: T250 -> AgdaAny -> AgdaAny
d290 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe v0))))))
name292 = "Relation.Binary.IsPartialOrder._.Eq.reflexive"
d292 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T250 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d292 v0 v1 v2 v3 v4 v5 v6 = du292 v6
du292 ::
  T250 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du292 v0
  = let v1 = d268 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d36 (coe v1))) v2)
name294 = "Relation.Binary.IsPartialOrder._.Eq.sym"
d294 :: T250 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d294 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe v0))))))
name296 = "Relation.Binary.IsPartialOrder._.Eq.trans"
d296 ::
  T250 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d296 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe v0))))))
name304 = "Relation.Binary.Poset"
d304 a0 a1 a2 = ()
newtype T304 = C1825 T250
name320 = "Relation.Binary.Poset.Carrier"
d320 :: T304 -> ()
d320 = erased
name322 = "Relation.Binary.Poset._≈_"
d322 :: T304 -> AgdaAny -> AgdaAny -> ()
d322 = erased
name324 = "Relation.Binary.Poset._≤_"
d324 :: T304 -> AgdaAny -> AgdaAny -> ()
d324 = erased
name326 = "Relation.Binary.Poset.isPartialOrder"
d326 :: T304 -> T250
d326 v0
  = case coe v0 of
      C1825 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name330 = "Relation.Binary.Poset._.antisym"
d330 :: T304 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d330 v0 = coe (d270 (coe (d326 (coe v0))))
name332 = "Relation.Binary.Poset._.isEquivalence"
d332 :: T304 -> MAlonzo.Code.Relation.Binary.Core.T644
d332 v0 = coe (d36 (coe (d268 (coe (d326 (coe v0))))))
name334 = "Relation.Binary.Poset._.isPreorder"
d334 :: T304 -> T16
d334 v0 = coe (d268 (coe (d326 (coe v0))))
name336 = "Relation.Binary.Poset._.refl"
d336 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T304 -> AgdaAny -> AgdaAny
d336 v0 v1 v2 v3 = du336 v3
du336 :: T304 -> AgdaAny -> AgdaAny
du336 v0
  = let v1 = d326 (coe v0) in coe (du52 (coe (d268 (coe v1))))
name338 = "Relation.Binary.Poset._.reflexive"
d338 :: T304 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d338 v0 = coe (d38 (coe (d268 (coe (d326 (coe v0))))))
name340 = "Relation.Binary.Poset._.trans"
d340 ::
  T304 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d340 v0 = coe (d40 (coe (d268 (coe (d326 (coe v0))))))
name342 = "Relation.Binary.Poset._.∼-resp-≈"
d342 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T304 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d342 v0 v1 v2 v3 = du342 v3
du342 :: T304 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du342 v0
  = let v1 = d326 (coe v0) in coe (du66 (coe (d268 (coe v1))))
name344 = "Relation.Binary.Poset._.∼-respʳ-≈"
d344 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T304 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d344 v0 v1 v2 v3 = du344 v3
du344 ::
  T304 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du344 v0
  = let v1 = d326 (coe v0) in coe (du60 (coe (d268 (coe v1))))
name346 = "Relation.Binary.Poset._.∼-respˡ-≈"
d346 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T304 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d346 v0 v1 v2 v3 = du346 v3
du346 ::
  T304 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du346 v0
  = let v1 = d326 (coe v0) in coe (du54 (coe (d268 (coe v1))))
name350 = "Relation.Binary.Poset._.Eq.refl"
d350 :: T304 -> AgdaAny -> AgdaAny
d350 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe (d326 (coe v0))))))))
name352 = "Relation.Binary.Poset._.Eq.reflexive"
d352 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T304 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d352 v0 v1 v2 v3 = du352 v3
du352 ::
  T304 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du352 v0
  = let v1 = d326 (coe v0) in
    let v2 = d268 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d36 (coe v2))) v3)
name354 = "Relation.Binary.Poset._.Eq.sym"
d354 :: T304 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d354 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe (d326 (coe v0))))))))
name356 = "Relation.Binary.Poset._.Eq.trans"
d356 ::
  T304 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d356 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe (d326 (coe v0))))))))
name358 = "Relation.Binary.Poset.preorder"
d358 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T304 -> T74
d358 v0 v1 v2 v3 = du358 v3
du358 :: T304 -> T74
du358 v0
  = coe
      (\ v1 v2 v3 v4 -> C739 v4) erased erased erased
      (d268 (coe (d326 (coe v0))))
name372 = "Relation.Binary.IsDecPartialOrder"
d372 a0 a1 a2 a3 a4 a5 = ()
data T372
  = C2143 T250
          (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14)
          (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14)
name392 = "Relation.Binary.IsDecPartialOrder.isPartialOrder"
d392 :: T372 -> T250
d392 v0
  = case coe v0 of
      C2143 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name394 = "Relation.Binary.IsDecPartialOrder._≟_"
d394 ::
  T372 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d394 v0
  = case coe v0 of
      C2143 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name396 = "Relation.Binary.IsDecPartialOrder._≤?_"
d396 ::
  T372 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d396 v0
  = case coe v0 of
      C2143 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name400 = "Relation.Binary.IsDecPartialOrder.PO.antisym"
d400 :: T372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d400 v0 = coe (d270 (coe (d392 (coe v0))))
name402 = "Relation.Binary.IsDecPartialOrder.PO.isEquivalence"
d402 :: T372 -> MAlonzo.Code.Relation.Binary.Core.T644
d402 v0 = coe (d36 (coe (d268 (coe (d392 (coe v0))))))
name404 = "Relation.Binary.IsDecPartialOrder.PO.isPreorder"
d404 :: T372 -> T16
d404 v0 = coe (d268 (coe (d392 (coe v0))))
name406 = "Relation.Binary.IsDecPartialOrder.PO.refl"
d406 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T372 -> AgdaAny -> AgdaAny
d406 v0 v1 v2 v3 v4 v5 v6 = du406 v6
du406 :: T372 -> AgdaAny -> AgdaAny
du406 v0
  = let v1 = d392 (coe v0) in coe (du52 (coe (d268 (coe v1))))
name408 = "Relation.Binary.IsDecPartialOrder.PO.reflexive"
d408 :: T372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d408 v0 = coe (d38 (coe (d268 (coe (d392 (coe v0))))))
name410 = "Relation.Binary.IsDecPartialOrder.PO.trans"
d410 ::
  T372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d410 v0 = coe (d40 (coe (d268 (coe (d392 (coe v0))))))
name412 = "Relation.Binary.IsDecPartialOrder.PO.∼-resp-≈"
d412 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T372 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d412 v0 v1 v2 v3 v4 v5 v6 = du412 v6
du412 :: T372 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du412 v0
  = let v1 = d392 (coe v0) in coe (du66 (coe (d268 (coe v1))))
name414 = "Relation.Binary.IsDecPartialOrder.PO.∼-respʳ-≈"
d414 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d414 v0 v1 v2 v3 v4 v5 v6 = du414 v6
du414 ::
  T372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du414 v0
  = let v1 = d392 (coe v0) in coe (du60 (coe (d268 (coe v1))))
name416 = "Relation.Binary.IsDecPartialOrder.PO.∼-respˡ-≈"
d416 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d416 v0 v1 v2 v3 v4 v5 v6 = du416 v6
du416 ::
  T372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du416 v0
  = let v1 = d392 (coe v0) in coe (du54 (coe (d268 (coe v1))))
name420 = "Relation.Binary.IsDecPartialOrder.PO.Eq.refl"
d420 :: T372 -> AgdaAny -> AgdaAny
d420 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe (d392 (coe v0))))))))
name422 = "Relation.Binary.IsDecPartialOrder.PO.Eq.reflexive"
d422 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T372 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d422 v0 v1 v2 v3 v4 v5 v6 = du422 v6
du422 ::
  T372 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du422 v0
  = let v1 = d392 (coe v0) in
    let v2 = d268 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d36 (coe v2))) v3)
name424 = "Relation.Binary.IsDecPartialOrder.PO.Eq.sym"
d424 :: T372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d424 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe (d392 (coe v0))))))))
name426 = "Relation.Binary.IsDecPartialOrder.PO.Eq.trans"
d426 ::
  T372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d426 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe (d392 (coe v0))))))))
name430 = "Relation.Binary.IsDecPartialOrder.Eq.isDecEquivalence"
d430 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T372 -> T168
d430 v0 v1 v2 v3 v4 v5 v6 = du430 v6
du430 :: T372 -> T168
du430 v0
  = coe
      (C1173
         (coe (d36 (coe (d268 (coe (d392 (coe v0)))))))
         (coe (d394 (coe v0))))
name434 = "Relation.Binary.IsDecPartialOrder.Eq._._≟_"
d434 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T372 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d434 v0 v1 v2 v3 v4 v5 v6 = du434 v6
du434 ::
  T372 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du434 v0 = coe (d394 (coe v0))
name436 = "Relation.Binary.IsDecPartialOrder.Eq._.isEquivalence"
d436 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T372 -> MAlonzo.Code.Relation.Binary.Core.T644
d436 v0 v1 v2 v3 v4 v5 v6 = du436 v6
du436 :: T372 -> MAlonzo.Code.Relation.Binary.Core.T644
du436 v0 = coe (d36 (coe (d268 (coe (d392 (coe v0))))))
name438 = "Relation.Binary.IsDecPartialOrder.Eq._.refl"
d438 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T372 -> AgdaAny -> AgdaAny
d438 v0 v1 v2 v3 v4 v5 v6 = du438 v6
du438 :: T372 -> AgdaAny -> AgdaAny
du438 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe (d392 (coe v0))))))))
name440 = "Relation.Binary.IsDecPartialOrder.Eq._.reflexive"
d440 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T372 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d440 v0 v1 v2 v3 v4 v5 v6 = du440 v6
du440 ::
  T372 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du440 v0
  = let v1 = du430 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v1))) v2)
name442 = "Relation.Binary.IsDecPartialOrder.Eq._.sym"
d442 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d442 v0 v1 v2 v3 v4 v5 v6 = du442 v6
du442 :: T372 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du442 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe (d392 (coe v0))))))))
name444 = "Relation.Binary.IsDecPartialOrder.Eq._.trans"
d444 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d444 v0 v1 v2 v3 v4 v5 v6 = du444 v6
du444 ::
  T372 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du444 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe (d392 (coe v0))))))))
name452 = "Relation.Binary.DecPoset"
d452 a0 a1 a2 = ()
newtype T452 = C2729 T372
name468 = "Relation.Binary.DecPoset.Carrier"
d468 :: T452 -> ()
d468 = erased
name470 = "Relation.Binary.DecPoset._≈_"
d470 :: T452 -> AgdaAny -> AgdaAny -> ()
d470 = erased
name472 = "Relation.Binary.DecPoset._≤_"
d472 :: T452 -> AgdaAny -> AgdaAny -> ()
d472 = erased
name474 = "Relation.Binary.DecPoset.isDecPartialOrder"
d474 :: T452 -> T372
d474 v0
  = case coe v0 of
      C2729 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name478 = "Relation.Binary.DecPoset.DPO._≟_"
d478 ::
  T452 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d478 v0 = coe (d394 (coe (d474 (coe v0))))
name480 = "Relation.Binary.DecPoset.DPO._≤?_"
d480 ::
  T452 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d480 v0 = coe (d396 (coe (d474 (coe v0))))
name482 = "Relation.Binary.DecPoset.DPO.antisym"
d482 :: T452 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d482 v0 = coe (d270 (coe (d392 (coe (d474 (coe v0))))))
name484 = "Relation.Binary.DecPoset.DPO.isEquivalence"
d484 :: T452 -> MAlonzo.Code.Relation.Binary.Core.T644
d484 v0 = coe (d36 (coe (d268 (coe (d392 (coe (d474 (coe v0))))))))
name486 = "Relation.Binary.DecPoset.DPO.isPartialOrder"
d486 :: T452 -> T250
d486 v0 = coe (d392 (coe (d474 (coe v0))))
name488 = "Relation.Binary.DecPoset.DPO.isPreorder"
d488 :: T452 -> T16
d488 v0 = coe (d268 (coe (d392 (coe (d474 (coe v0))))))
name490 = "Relation.Binary.DecPoset.DPO.refl"
d490 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> AgdaAny -> AgdaAny
d490 v0 v1 v2 v3 = du490 v3
du490 :: T452 -> AgdaAny -> AgdaAny
du490 v0
  = let v1 = d474 (coe v0) in
    let v2 = d392 (coe v1) in coe (du52 (coe (d268 (coe v2))))
name492 = "Relation.Binary.DecPoset.DPO.reflexive"
d492 :: T452 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d492 v0 = coe (d38 (coe (d268 (coe (d392 (coe (d474 (coe v0))))))))
name494 = "Relation.Binary.DecPoset.DPO.trans"
d494 ::
  T452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d494 v0 = coe (d40 (coe (d268 (coe (d392 (coe (d474 (coe v0))))))))
name496 = "Relation.Binary.DecPoset.DPO.∼-resp-≈"
d496 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d496 v0 v1 v2 v3 = du496 v3
du496 :: T452 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du496 v0
  = let v1 = d474 (coe v0) in
    let v2 = d392 (coe v1) in coe (du66 (coe (d268 (coe v2))))
name498 = "Relation.Binary.DecPoset.DPO.∼-respʳ-≈"
d498 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d498 v0 v1 v2 v3 = du498 v3
du498 ::
  T452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du498 v0
  = let v1 = d474 (coe v0) in
    let v2 = d392 (coe v1) in coe (du60 (coe (d268 (coe v2))))
name500 = "Relation.Binary.DecPoset.DPO.∼-respˡ-≈"
d500 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d500 v0 v1 v2 v3 = du500 v3
du500 ::
  T452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du500 v0
  = let v1 = d474 (coe v0) in
    let v2 = d392 (coe v1) in coe (du54 (coe (d268 (coe v2))))
name504 = "Relation.Binary.DecPoset.DPO.Eq._≟_"
d504 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d504 v0 v1 v2 v3 = du504 v3
du504 ::
  T452 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du504 v0 = let v1 = d474 (coe v0) in coe (d394 (coe v1))
name506 = "Relation.Binary.DecPoset.DPO.Eq.isDecEquivalence"
d506 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> T168
d506 v0 v1 v2 v3 = du506 v3
du506 :: T452 -> T168
du506 v0 = coe (du430 (coe (d474 (coe v0))))
name508 = "Relation.Binary.DecPoset.DPO.Eq.isEquivalence"
d508 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 -> MAlonzo.Code.Relation.Binary.Core.T644
d508 v0 v1 v2 v3 = du508 v3
du508 :: T452 -> MAlonzo.Code.Relation.Binary.Core.T644
du508 v0
  = let v1 = d474 (coe v0) in
    coe (d36 (coe (d268 (coe (d392 (coe v1))))))
name510 = "Relation.Binary.DecPoset.DPO.Eq.refl"
d510 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> AgdaAny -> AgdaAny
d510 v0 v1 v2 v3 = du510 v3
du510 :: T452 -> AgdaAny -> AgdaAny
du510 v0
  = let v1 = d474 (coe v0) in
    coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe (d392 (coe v1))))))))
name512 = "Relation.Binary.DecPoset.DPO.Eq.reflexive"
d512 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d512 v0 v1 v2 v3 = du512 v3
du512 ::
  T452 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du512 v0
  = let v1 = d474 (coe v0) in
    let v2 = du430 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v2))) v3)
name514 = "Relation.Binary.DecPoset.DPO.Eq.sym"
d514 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d514 v0 v1 v2 v3 = du514 v3
du514 :: T452 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du514 v0
  = let v1 = d474 (coe v0) in
    coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe (d392 (coe v1))))))))
name516 = "Relation.Binary.DecPoset.DPO.Eq.trans"
d516 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d516 v0 v1 v2 v3 = du516 v3
du516 ::
  T452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du516 v0
  = let v1 = d474 (coe v0) in
    coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe (d392 (coe v1))))))))
name518 = "Relation.Binary.DecPoset.poset"
d518 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> T304
d518 v0 v1 v2 v3 = du518 v3
du518 :: T452 -> T304
du518 v0
  = coe
      (\ v1 v2 v3 v4 -> C1825 v4) erased erased erased
      (d392 (coe (d474 (coe v0))))
name522 = "Relation.Binary.DecPoset._.preorder"
d522 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> T74
d522 v0 v1 v2 v3 = du522 v3
du522 :: T452 -> T74
du522 v0 = coe (du358 (coe (du518 (coe v0))))
name526 = "Relation.Binary.DecPoset.Eq.decSetoid"
d526 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> T200
d526 v0 v1 v2 v3 = du526 v3
du526 :: T452 -> T200
du526 v0
  = coe
      (\ v1 v2 v3 -> C1311 v3) erased erased
      (du430 (coe (d474 (coe v0))))
name530 = "Relation.Binary.DecPoset.Eq._._≈_"
d530 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> AgdaAny -> AgdaAny -> ()
d530 = erased
name532 = "Relation.Binary.DecPoset.Eq._._≟_"
d532 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d532 v0 v1 v2 v3 = du532 v3
du532 ::
  T452 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du532 v0 = coe (d394 (coe (d474 (coe v0))))
name534 = "Relation.Binary.DecPoset.Eq._.Carrier"
d534 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> ()
d534 = erased
name536 = "Relation.Binary.DecPoset.Eq._.isDecEquivalence"
d536 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> T168
d536 v0 v1 v2 v3 = du536 v3
du536 :: T452 -> T168
du536 v0 = coe (du430 (coe (d474 (coe v0))))
name538 = "Relation.Binary.DecPoset.Eq._.isEquivalence"
d538 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 -> MAlonzo.Code.Relation.Binary.Core.T644
d538 v0 v1 v2 v3 = du538 v3
du538 :: T452 -> MAlonzo.Code.Relation.Binary.Core.T644
du538 v0
  = coe (d36 (coe (d268 (coe (d392 (coe (d474 (coe v0))))))))
name540 = "Relation.Binary.DecPoset.Eq._.preorder"
d540 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> T74
d540 v0 v1 v2 v3 = du540 v3
du540 :: T452 -> T74
du540 v0
  = let v1 = du526 (coe v0) in coe (du158 (coe (du232 (coe v1))))
name542 = "Relation.Binary.DecPoset.Eq._.refl"
d542 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> AgdaAny -> AgdaAny
d542 v0 v1 v2 v3 = du542 v3
du542 :: T452 -> AgdaAny -> AgdaAny
du542 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe (d392 (coe (d474 (coe v0))))))))))
name544 = "Relation.Binary.DecPoset.Eq._.reflexive"
d544 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d544 v0 v1 v2 v3 = du544 v3
du544 ::
  T452 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du544 v0
  = let v1 = du526 (coe v0) in
    let v2 = d216 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v2))) v3)
name546 = "Relation.Binary.DecPoset.Eq._.setoid"
d546 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T452 -> T128
d546 v0 v1 v2 v3 = du546 v3
du546 :: T452 -> T128
du546 v0 = coe (du232 (coe (du526 (coe v0))))
name548 = "Relation.Binary.DecPoset.Eq._.sym"
d548 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d548 v0 v1 v2 v3 = du548 v3
du548 :: T452 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du548 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe (d392 (coe (d474 (coe v0))))))))))
name550 = "Relation.Binary.DecPoset.Eq._.trans"
d550 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d550 v0 v1 v2 v3 = du550 v3
du550 ::
  T452 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du550 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe (d392 (coe (d474 (coe v0))))))))))
name564 = "Relation.Binary.IsStrictPartialOrder"
d564 a0 a1 a2 a3 a4 a5 = ()
data T564
  = C3247 MAlonzo.Code.Relation.Binary.Core.T644
          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
          MAlonzo.Code.Agda.Builtin.Sigma.T14
name586 = "Relation.Binary.IsStrictPartialOrder.isEquivalence"
d586 :: T564 -> MAlonzo.Code.Relation.Binary.Core.T644
d586 v0
  = case coe v0 of
      C3247 v1 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name588 = "Relation.Binary.IsStrictPartialOrder.irrefl"
d588 ::
  T564 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d588 = erased
name590 = "Relation.Binary.IsStrictPartialOrder.trans"
d590 ::
  T564 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d590 v0
  = case coe v0 of
      C3247 v1 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name592 = "Relation.Binary.IsStrictPartialOrder.<-resp-≈"
d592 :: T564 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d592 v0
  = case coe v0 of
      C3247 v1 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name596 = "Relation.Binary.IsStrictPartialOrder.Eq.refl"
d596 :: T564 -> AgdaAny -> AgdaAny
d596 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660 (coe (d586 (coe v0))))
name598 = "Relation.Binary.IsStrictPartialOrder.Eq.reflexive"
d598 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T564 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d598 v0 v1 v2 v3 v4 v5 v6 = du598 v6
du598 ::
  T564 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du598 v0
  = coe
      (\ v1 v2 v3 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d586 (coe v0))) v1)
name600 = "Relation.Binary.IsStrictPartialOrder.Eq.sym"
d600 :: T564 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d600 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662 (coe (d586 (coe v0))))
name602 = "Relation.Binary.IsStrictPartialOrder.Eq.trans"
d602 ::
  T564 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d602 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664 (coe (d586 (coe v0))))
name604 = "Relation.Binary.IsStrictPartialOrder.asym"
d604 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T564 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d604 = erased
name610 = "Relation.Binary.IsStrictPartialOrder.<-respʳ-≈"
d610 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T564 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d610 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du610 v6 v7 v8 v9
du610 ::
  T564 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du610 v0 v1 v2 v3
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d28 (d592 (coe v0)) v1 v2 v3
name612 = "Relation.Binary.IsStrictPartialOrder.<-respˡ-≈"
d612 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T564 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d612 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du612 v6 v7 v8 v9
du612 ::
  T564 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du612 v0 v1 v2 v3
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d30 (d592 (coe v0)) v1 v2 v3
name614 = "Relation.Binary.IsStrictPartialOrder.asymmetric"
d614 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T564 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d614 = erased
name622 = "Relation.Binary.StrictPartialOrder"
d622 a0 a1 a2 = ()
newtype T622 = C3899 T564
name638 = "Relation.Binary.StrictPartialOrder.Carrier"
d638 :: T622 -> ()
d638 = erased
name640 = "Relation.Binary.StrictPartialOrder._≈_"
d640 :: T622 -> AgdaAny -> AgdaAny -> ()
d640 = erased
name642 = "Relation.Binary.StrictPartialOrder._<_"
d642 :: T622 -> AgdaAny -> AgdaAny -> ()
d642 = erased
name644 = "Relation.Binary.StrictPartialOrder.isStrictPartialOrder"
d644 :: T622 -> T564
d644 v0
  = case coe v0 of
      C3899 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name648 = "Relation.Binary.StrictPartialOrder._.<-resp-≈"
d648 :: T622 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d648 v0 = coe (d592 (coe (d644 (coe v0))))
name650 = "Relation.Binary.StrictPartialOrder._.<-respʳ-≈"
d650 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T622 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d650 v0 v1 v2 v3 = du650 v3
du650 ::
  T622 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du650 v0
  = let v1 = d644 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe MAlonzo.Code.Agda.Builtin.Sigma.d28 (d592 (coe v1)) v2 v3 v4)
name652 = "Relation.Binary.StrictPartialOrder._.<-respˡ-≈"
d652 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T622 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d652 v0 v1 v2 v3 = du652 v3
du652 ::
  T622 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du652 v0
  = let v1 = d644 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe MAlonzo.Code.Agda.Builtin.Sigma.d30 (d592 (coe v1)) v2 v3 v4)
name654 = "Relation.Binary.StrictPartialOrder._.asym"
d654 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T622 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d654 = erased
name656 = "Relation.Binary.StrictPartialOrder._.asymmetric"
d656 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T622 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d656 = erased
name658 = "Relation.Binary.StrictPartialOrder._.irrefl"
d658 ::
  T622 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d658 = erased
name660 = "Relation.Binary.StrictPartialOrder._.isEquivalence"
d660 :: T622 -> MAlonzo.Code.Relation.Binary.Core.T644
d660 v0 = coe (d586 (coe (d644 (coe v0))))
name662 = "Relation.Binary.StrictPartialOrder._.trans"
d662 ::
  T622 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d662 v0 = coe (d590 (coe (d644 (coe v0))))
name666 = "Relation.Binary.StrictPartialOrder._.Eq.refl"
d666 :: T622 -> AgdaAny -> AgdaAny
d666 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d586 (coe (d644 (coe v0))))))
name668 = "Relation.Binary.StrictPartialOrder._.Eq.reflexive"
d668 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T622 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d668 v0 v1 v2 v3 = du668 v3
du668 ::
  T622 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du668 v0
  = let v1 = d644 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d586 (coe v1))) v2)
name670 = "Relation.Binary.StrictPartialOrder._.Eq.sym"
d670 :: T622 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d670 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d586 (coe (d644 (coe v0))))))
name672 = "Relation.Binary.StrictPartialOrder._.Eq.trans"
d672 ::
  T622 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d672 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d586 (coe (d644 (coe v0))))))
name686 = "Relation.Binary.IsDecStrictPartialOrder"
d686 a0 a1 a2 a3 a4 a5 = ()
data T686
  = C4155 T564
          (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14)
          (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14)
name706
  = "Relation.Binary.IsDecStrictPartialOrder.isStrictPartialOrder"
d706 :: T686 -> T564
d706 v0
  = case coe v0 of
      C4155 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name708 = "Relation.Binary.IsDecStrictPartialOrder._≟_"
d708 ::
  T686 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d708 v0
  = case coe v0 of
      C4155 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name710 = "Relation.Binary.IsDecStrictPartialOrder._<?_"
d710 ::
  T686 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d710 v0
  = case coe v0 of
      C4155 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name714 = "Relation.Binary.IsDecStrictPartialOrder.SPO.<-resp-≈"
d714 :: T686 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d714 v0 = coe (d592 (coe (d706 (coe v0))))
name716 = "Relation.Binary.IsDecStrictPartialOrder.SPO.<-respʳ-≈"
d716 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d716 v0 v1 v2 v3 v4 v5 v6 = du716 v6
du716 ::
  T686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du716 v0
  = let v1 = d706 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe MAlonzo.Code.Agda.Builtin.Sigma.d28 (d592 (coe v1)) v2 v3 v4)
name718 = "Relation.Binary.IsDecStrictPartialOrder.SPO.<-respˡ-≈"
d718 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d718 v0 v1 v2 v3 v4 v5 v6 = du718 v6
du718 ::
  T686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du718 v0
  = let v1 = d706 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe MAlonzo.Code.Agda.Builtin.Sigma.d30 (d592 (coe v1)) v2 v3 v4)
name720 = "Relation.Binary.IsDecStrictPartialOrder.SPO.asym"
d720 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d720 = erased
name722 = "Relation.Binary.IsDecStrictPartialOrder.SPO.asymmetric"
d722 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d722 = erased
name724 = "Relation.Binary.IsDecStrictPartialOrder.SPO.irrefl"
d724 ::
  T686 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d724 = erased
name726
  = "Relation.Binary.IsDecStrictPartialOrder.SPO.isEquivalence"
d726 :: T686 -> MAlonzo.Code.Relation.Binary.Core.T644
d726 v0 = coe (d586 (coe (d706 (coe v0))))
name728 = "Relation.Binary.IsDecStrictPartialOrder.SPO.trans"
d728 ::
  T686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d728 v0 = coe (d590 (coe (d706 (coe v0))))
name732 = "Relation.Binary.IsDecStrictPartialOrder.SPO.Eq.refl"
d732 :: T686 -> AgdaAny -> AgdaAny
d732 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d586 (coe (d706 (coe v0))))))
name734
  = "Relation.Binary.IsDecStrictPartialOrder.SPO.Eq.reflexive"
d734 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d734 v0 v1 v2 v3 v4 v5 v6 = du734 v6
du734 ::
  T686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du734 v0
  = let v1 = d706 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d586 (coe v1))) v2)
name736 = "Relation.Binary.IsDecStrictPartialOrder.SPO.Eq.sym"
d736 :: T686 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d736 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d586 (coe (d706 (coe v0))))))
name738 = "Relation.Binary.IsDecStrictPartialOrder.SPO.Eq.trans"
d738 ::
  T686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d738 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d586 (coe (d706 (coe v0))))))
name742
  = "Relation.Binary.IsDecStrictPartialOrder.Eq.isDecEquivalence"
d742 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T686 -> T168
d742 v0 v1 v2 v3 v4 v5 v6 = du742 v6
du742 :: T686 -> T168
du742 v0
  = coe
      (C1173 (coe (d586 (coe (d706 (coe v0))))) (coe (d708 (coe v0))))
name746 = "Relation.Binary.IsDecStrictPartialOrder.Eq._._≟_"
d746 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d746 v0 v1 v2 v3 v4 v5 v6 = du746 v6
du746 ::
  T686 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du746 v0 = coe (d708 (coe v0))
name748
  = "Relation.Binary.IsDecStrictPartialOrder.Eq._.isEquivalence"
d748 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 -> MAlonzo.Code.Relation.Binary.Core.T644
d748 v0 v1 v2 v3 v4 v5 v6 = du748 v6
du748 :: T686 -> MAlonzo.Code.Relation.Binary.Core.T644
du748 v0 = coe (d586 (coe (d706 (coe v0))))
name750 = "Relation.Binary.IsDecStrictPartialOrder.Eq._.refl"
d750 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T686 -> AgdaAny -> AgdaAny
d750 v0 v1 v2 v3 v4 v5 v6 = du750 v6
du750 :: T686 -> AgdaAny -> AgdaAny
du750 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d586 (coe (d706 (coe v0))))))
name752 = "Relation.Binary.IsDecStrictPartialOrder.Eq._.reflexive"
d752 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d752 v0 v1 v2 v3 v4 v5 v6 = du752 v6
du752 ::
  T686 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du752 v0
  = let v1 = du742 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v1))) v2)
name754 = "Relation.Binary.IsDecStrictPartialOrder.Eq._.sym"
d754 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d754 v0 v1 v2 v3 v4 v5 v6 = du754 v6
du754 :: T686 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du754 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d586 (coe (d706 (coe v0))))))
name756 = "Relation.Binary.IsDecStrictPartialOrder.Eq._.trans"
d756 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d756 v0 v1 v2 v3 v4 v5 v6 = du756 v6
du756 ::
  T686 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du756 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d586 (coe (d706 (coe v0))))))
name764 = "Relation.Binary.DecStrictPartialOrder"
d764 a0 a1 a2 = ()
newtype T764 = C4715 T686
name780 = "Relation.Binary.DecStrictPartialOrder.Carrier"
d780 :: T764 -> ()
d780 = erased
name782 = "Relation.Binary.DecStrictPartialOrder._≈_"
d782 :: T764 -> AgdaAny -> AgdaAny -> ()
d782 = erased
name784 = "Relation.Binary.DecStrictPartialOrder._<_"
d784 :: T764 -> AgdaAny -> AgdaAny -> ()
d784 = erased
name786
  = "Relation.Binary.DecStrictPartialOrder.isDecStrictPartialOrder"
d786 :: T764 -> T686
d786 v0
  = case coe v0 of
      C4715 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name790 = "Relation.Binary.DecStrictPartialOrder.DSPO._<?_"
d790 ::
  T764 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d790 v0 = coe (d710 (coe (d786 (coe v0))))
name792 = "Relation.Binary.DecStrictPartialOrder.DSPO._≟_"
d792 ::
  T764 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d792 v0 = coe (d708 (coe (d786 (coe v0))))
name794 = "Relation.Binary.DecStrictPartialOrder.DSPO.<-resp-≈"
d794 :: T764 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d794 v0 = coe (d592 (coe (d706 (coe (d786 (coe v0))))))
name796 = "Relation.Binary.DecStrictPartialOrder.DSPO.<-respʳ-≈"
d796 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d796 v0 v1 v2 v3 = du796 v3
du796 ::
  T764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du796 v0
  = let v1 = d786 (coe v0) in
    let v2 = d706 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         coe MAlonzo.Code.Agda.Builtin.Sigma.d28 (d592 (coe v2)) v3 v4 v5)
name798 = "Relation.Binary.DecStrictPartialOrder.DSPO.<-respˡ-≈"
d798 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d798 v0 v1 v2 v3 = du798 v3
du798 ::
  T764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du798 v0
  = let v1 = d786 (coe v0) in
    let v2 = d706 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         coe MAlonzo.Code.Agda.Builtin.Sigma.d30 (d592 (coe v2)) v3 v4 v5)
name800 = "Relation.Binary.DecStrictPartialOrder.DSPO.asym"
d800 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d800 = erased
name802 = "Relation.Binary.DecStrictPartialOrder.DSPO.asymmetric"
d802 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d802 = erased
name804 = "Relation.Binary.DecStrictPartialOrder.DSPO.irrefl"
d804 ::
  T764 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d804 = erased
name806
  = "Relation.Binary.DecStrictPartialOrder.DSPO.isEquivalence"
d806 :: T764 -> MAlonzo.Code.Relation.Binary.Core.T644
d806 v0 = coe (d586 (coe (d706 (coe (d786 (coe v0))))))
name808
  = "Relation.Binary.DecStrictPartialOrder.DSPO.isStrictPartialOrder"
d808 :: T764 -> T564
d808 v0 = coe (d706 (coe (d786 (coe v0))))
name810 = "Relation.Binary.DecStrictPartialOrder.DSPO.trans"
d810 ::
  T764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d810 v0 = coe (d590 (coe (d706 (coe (d786 (coe v0))))))
name814 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq._≟_"
d814 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d814 v0 v1 v2 v3 = du814 v3
du814 ::
  T764 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du814 v0 = let v1 = d786 (coe v0) in coe (d708 (coe v1))
name816
  = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.isDecEquivalence"
d816 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> T168
d816 v0 v1 v2 v3 = du816 v3
du816 :: T764 -> T168
du816 v0 = coe (du742 (coe (d786 (coe v0))))
name818
  = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.isEquivalence"
d818 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 -> MAlonzo.Code.Relation.Binary.Core.T644
d818 v0 v1 v2 v3 = du818 v3
du818 :: T764 -> MAlonzo.Code.Relation.Binary.Core.T644
du818 v0
  = let v1 = d786 (coe v0) in coe (d586 (coe (d706 (coe v1))))
name820 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.refl"
d820 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> AgdaAny -> AgdaAny
d820 v0 v1 v2 v3 = du820 v3
du820 :: T764 -> AgdaAny -> AgdaAny
du820 v0
  = let v1 = d786 (coe v0) in
    coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d586 (coe (d706 (coe v1))))))
name822 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.reflexive"
d822 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d822 v0 v1 v2 v3 = du822 v3
du822 ::
  T764 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du822 v0
  = let v1 = d786 (coe v0) in
    let v2 = du742 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v2))) v3)
name824 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.sym"
d824 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d824 v0 v1 v2 v3 = du824 v3
du824 :: T764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du824 v0
  = let v1 = d786 (coe v0) in
    coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d586 (coe (d706 (coe v1))))))
name826 = "Relation.Binary.DecStrictPartialOrder.DSPO.Eq.trans"
d826 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d826 v0 v1 v2 v3 = du826 v3
du826 ::
  T764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du826 v0
  = let v1 = d786 (coe v0) in
    coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d586 (coe (d706 (coe v1))))))
name828
  = "Relation.Binary.DecStrictPartialOrder.strictPartialOrder"
d828 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> T622
d828 v0 v1 v2 v3 = du828 v3
du828 :: T764 -> T622
du828 v0
  = coe
      (\ v1 v2 v3 v4 -> C3899 v4) erased erased erased
      (d706 (coe (d786 (coe v0))))
name832 = "Relation.Binary.DecStrictPartialOrder.Eq.decSetoid"
d832 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> T200
d832 v0 v1 v2 v3 = du832 v3
du832 :: T764 -> T200
du832 v0
  = coe
      (\ v1 v2 v3 -> C1311 v3) erased erased
      (du742 (coe (d786 (coe v0))))
name836 = "Relation.Binary.DecStrictPartialOrder.Eq._._≈_"
d836 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> AgdaAny -> AgdaAny -> ()
d836 = erased
name838 = "Relation.Binary.DecStrictPartialOrder.Eq._._≟_"
d838 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d838 v0 v1 v2 v3 = du838 v3
du838 ::
  T764 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du838 v0 = coe (d708 (coe (d786 (coe v0))))
name840 = "Relation.Binary.DecStrictPartialOrder.Eq._.Carrier"
d840 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> ()
d840 = erased
name842
  = "Relation.Binary.DecStrictPartialOrder.Eq._.isDecEquivalence"
d842 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> T168
d842 v0 v1 v2 v3 = du842 v3
du842 :: T764 -> T168
du842 v0 = coe (du742 (coe (d786 (coe v0))))
name844
  = "Relation.Binary.DecStrictPartialOrder.Eq._.isEquivalence"
d844 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 -> MAlonzo.Code.Relation.Binary.Core.T644
d844 v0 v1 v2 v3 = du844 v3
du844 :: T764 -> MAlonzo.Code.Relation.Binary.Core.T644
du844 v0 = coe (d586 (coe (d706 (coe (d786 (coe v0))))))
name846 = "Relation.Binary.DecStrictPartialOrder.Eq._.preorder"
d846 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> T74
d846 v0 v1 v2 v3 = du846 v3
du846 :: T764 -> T74
du846 v0
  = let v1 = du832 (coe v0) in coe (du158 (coe (du232 (coe v1))))
name848 = "Relation.Binary.DecStrictPartialOrder.Eq._.refl"
d848 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> AgdaAny -> AgdaAny
d848 v0 v1 v2 v3 = du848 v3
du848 :: T764 -> AgdaAny -> AgdaAny
du848 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d586 (coe (d706 (coe (d786 (coe v0))))))))
name850 = "Relation.Binary.DecStrictPartialOrder.Eq._.reflexive"
d850 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d850 v0 v1 v2 v3 = du850 v3
du850 ::
  T764 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du850 v0
  = let v1 = du832 (coe v0) in
    let v2 = d216 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v2))) v3)
name852 = "Relation.Binary.DecStrictPartialOrder.Eq._.setoid"
d852 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T764 -> T128
d852 v0 v1 v2 v3 = du852 v3
du852 :: T764 -> T128
du852 v0 = coe (du232 (coe (du832 (coe v0))))
name854 = "Relation.Binary.DecStrictPartialOrder.Eq._.sym"
d854 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d854 v0 v1 v2 v3 = du854 v3
du854 :: T764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du854 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d586 (coe (d706 (coe (d786 (coe v0))))))))
name856 = "Relation.Binary.DecStrictPartialOrder.Eq._.trans"
d856 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d856 v0 v1 v2 v3 = du856 v3
du856 ::
  T764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du856 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d586 (coe (d706 (coe (d786 (coe v0))))))))
name870 = "Relation.Binary.IsTotalOrder"
d870 a0 a1 a2 a3 a4 a5 = ()
data T870
  = C5199 T250
          (AgdaAny ->
           AgdaAny ->
           MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny)
name888 = "Relation.Binary.IsTotalOrder.isPartialOrder"
d888 :: T870 -> T250
d888 v0
  = case coe v0 of
      C5199 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name890 = "Relation.Binary.IsTotalOrder.total"
d890 ::
  T870 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny
d890 v0
  = case coe v0 of
      C5199 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name894 = "Relation.Binary.IsTotalOrder._.antisym"
d894 :: T870 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d894 v0 = coe (d270 (coe (d888 (coe v0))))
name896 = "Relation.Binary.IsTotalOrder._.isEquivalence"
d896 :: T870 -> MAlonzo.Code.Relation.Binary.Core.T644
d896 v0 = coe (d36 (coe (d268 (coe (d888 (coe v0))))))
name898 = "Relation.Binary.IsTotalOrder._.isPreorder"
d898 :: T870 -> T16
d898 v0 = coe (d268 (coe (d888 (coe v0))))
name900 = "Relation.Binary.IsTotalOrder._.refl"
d900 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T870 -> AgdaAny -> AgdaAny
d900 v0 v1 v2 v3 v4 v5 v6 = du900 v6
du900 :: T870 -> AgdaAny -> AgdaAny
du900 v0
  = let v1 = d888 (coe v0) in coe (du52 (coe (d268 (coe v1))))
name902 = "Relation.Binary.IsTotalOrder._.reflexive"
d902 :: T870 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d902 v0 = coe (d38 (coe (d268 (coe (d888 (coe v0))))))
name904 = "Relation.Binary.IsTotalOrder._.trans"
d904 ::
  T870 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d904 v0 = coe (d40 (coe (d268 (coe (d888 (coe v0))))))
name906 = "Relation.Binary.IsTotalOrder._.∼-resp-≈"
d906 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T870 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d906 v0 v1 v2 v3 v4 v5 v6 = du906 v6
du906 :: T870 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du906 v0
  = let v1 = d888 (coe v0) in coe (du66 (coe (d268 (coe v1))))
name908 = "Relation.Binary.IsTotalOrder._.∼-respʳ-≈"
d908 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T870 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d908 v0 v1 v2 v3 v4 v5 v6 = du908 v6
du908 ::
  T870 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du908 v0
  = let v1 = d888 (coe v0) in coe (du60 (coe (d268 (coe v1))))
name910 = "Relation.Binary.IsTotalOrder._.∼-respˡ-≈"
d910 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T870 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d910 v0 v1 v2 v3 v4 v5 v6 = du910 v6
du910 ::
  T870 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du910 v0
  = let v1 = d888 (coe v0) in coe (du54 (coe (d268 (coe v1))))
name914 = "Relation.Binary.IsTotalOrder._.Eq.refl"
d914 :: T870 -> AgdaAny -> AgdaAny
d914 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe (d888 (coe v0))))))))
name916 = "Relation.Binary.IsTotalOrder._.Eq.reflexive"
d916 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T870 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d916 v0 v1 v2 v3 v4 v5 v6 = du916 v6
du916 ::
  T870 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du916 v0
  = let v1 = d888 (coe v0) in
    let v2 = d268 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d36 (coe v2))) v3)
name918 = "Relation.Binary.IsTotalOrder._.Eq.sym"
d918 :: T870 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d918 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe (d888 (coe v0))))))))
name920 = "Relation.Binary.IsTotalOrder._.Eq.trans"
d920 ::
  T870 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d920 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe (d888 (coe v0))))))))
name928 = "Relation.Binary.TotalOrder"
d928 a0 a1 a2 = ()
newtype T928 = C5585 T870
name944 = "Relation.Binary.TotalOrder.Carrier"
d944 :: T928 -> ()
d944 = erased
name946 = "Relation.Binary.TotalOrder._≈_"
d946 :: T928 -> AgdaAny -> AgdaAny -> ()
d946 = erased
name948 = "Relation.Binary.TotalOrder._≤_"
d948 :: T928 -> AgdaAny -> AgdaAny -> ()
d948 = erased
name950 = "Relation.Binary.TotalOrder.isTotalOrder"
d950 :: T928 -> T870
d950 v0
  = case coe v0 of
      C5585 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name954 = "Relation.Binary.TotalOrder._.antisym"
d954 :: T928 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d954 v0 = coe (d270 (coe (d888 (coe (d950 (coe v0))))))
name956 = "Relation.Binary.TotalOrder._.isEquivalence"
d956 :: T928 -> MAlonzo.Code.Relation.Binary.Core.T644
d956 v0 = coe (d36 (coe (d268 (coe (d888 (coe (d950 (coe v0))))))))
name958 = "Relation.Binary.TotalOrder._.isPartialOrder"
d958 :: T928 -> T250
d958 v0 = coe (d888 (coe (d950 (coe v0))))
name960 = "Relation.Binary.TotalOrder._.isPreorder"
d960 :: T928 -> T16
d960 v0 = coe (d268 (coe (d888 (coe (d950 (coe v0))))))
name962 = "Relation.Binary.TotalOrder._.refl"
d962 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T928 -> AgdaAny -> AgdaAny
d962 v0 v1 v2 v3 = du962 v3
du962 :: T928 -> AgdaAny -> AgdaAny
du962 v0
  = let v1 = d950 (coe v0) in
    let v2 = d888 (coe v1) in coe (du52 (coe (d268 (coe v2))))
name964 = "Relation.Binary.TotalOrder._.reflexive"
d964 :: T928 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d964 v0 = coe (d38 (coe (d268 (coe (d888 (coe (d950 (coe v0))))))))
name966 = "Relation.Binary.TotalOrder._.total"
d966 ::
  T928 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny
d966 v0 = coe (d890 (coe (d950 (coe v0))))
name968 = "Relation.Binary.TotalOrder._.trans"
d968 ::
  T928 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d968 v0 = coe (d40 (coe (d268 (coe (d888 (coe (d950 (coe v0))))))))
name970 = "Relation.Binary.TotalOrder._.∼-resp-≈"
d970 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T928 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d970 v0 v1 v2 v3 = du970 v3
du970 :: T928 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du970 v0
  = let v1 = d950 (coe v0) in
    let v2 = d888 (coe v1) in coe (du66 (coe (d268 (coe v2))))
name972 = "Relation.Binary.TotalOrder._.∼-respʳ-≈"
d972 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T928 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d972 v0 v1 v2 v3 = du972 v3
du972 ::
  T928 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du972 v0
  = let v1 = d950 (coe v0) in
    let v2 = d888 (coe v1) in coe (du60 (coe (d268 (coe v2))))
name974 = "Relation.Binary.TotalOrder._.∼-respˡ-≈"
d974 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T928 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d974 v0 v1 v2 v3 = du974 v3
du974 ::
  T928 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du974 v0
  = let v1 = d950 (coe v0) in
    let v2 = d888 (coe v1) in coe (du54 (coe (d268 (coe v2))))
name978 = "Relation.Binary.TotalOrder._.Eq.refl"
d978 :: T928 -> AgdaAny -> AgdaAny
d978 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe (d888 (coe (d950 (coe v0))))))))))
name980 = "Relation.Binary.TotalOrder._.Eq.reflexive"
d980 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T928 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d980 v0 v1 v2 v3 = du980 v3
du980 ::
  T928 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du980 v0
  = let v1 = d950 (coe v0) in
    let v2 = d888 (coe v1) in
    let v3 = d268 (coe v2) in
    coe
      (\ v4 v5 v6 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d36 (coe v3))) v4)
name982 = "Relation.Binary.TotalOrder._.Eq.sym"
d982 :: T928 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d982 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe (d888 (coe (d950 (coe v0))))))))))
name984 = "Relation.Binary.TotalOrder._.Eq.trans"
d984 ::
  T928 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d984 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe (d888 (coe (d950 (coe v0))))))))))
name986 = "Relation.Binary.TotalOrder.poset"
d986 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T928 -> T304
d986 v0 v1 v2 v3 = du986 v3
du986 :: T928 -> T304
du986 v0
  = coe
      (\ v1 v2 v3 v4 -> C1825 v4) erased erased erased
      (d888 (coe (d950 (coe v0))))
name990 = "Relation.Binary.TotalOrder._.preorder"
d990 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T928 -> T74
d990 v0 v1 v2 v3 = du990 v3
du990 :: T928 -> T74
du990 v0 = coe (du358 (coe (du986 (coe v0))))
name1004 = "Relation.Binary.IsDecTotalOrder"
d1004 a0 a1 a2 a3 a4 a5 = ()
data T1004
  = C5939 T870
          (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14)
          (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14)
name1024 = "Relation.Binary.IsDecTotalOrder.isTotalOrder"
d1024 :: T1004 -> T870
d1024 v0
  = case coe v0 of
      C5939 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name1026 = "Relation.Binary.IsDecTotalOrder._≟_"
d1026 ::
  T1004 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1026 v0
  = case coe v0 of
      C5939 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name1028 = "Relation.Binary.IsDecTotalOrder._≤?_"
d1028 ::
  T1004 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1028 v0
  = case coe v0 of
      C5939 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name1032 = "Relation.Binary.IsDecTotalOrder._.antisym"
d1032 ::
  T1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1032 v0 = coe (d270 (coe (d888 (coe (d1024 (coe v0))))))
name1034 = "Relation.Binary.IsDecTotalOrder._.isEquivalence"
d1034 :: T1004 -> MAlonzo.Code.Relation.Binary.Core.T644
d1034 v0
  = coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v0))))))))
name1036 = "Relation.Binary.IsDecTotalOrder._.isPartialOrder"
d1036 :: T1004 -> T250
d1036 v0 = coe (d888 (coe (d1024 (coe v0))))
name1038 = "Relation.Binary.IsDecTotalOrder._.isPreorder"
d1038 :: T1004 -> T16
d1038 v0 = coe (d268 (coe (d888 (coe (d1024 (coe v0))))))
name1040 = "Relation.Binary.IsDecTotalOrder._.refl"
d1040 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T1004 -> AgdaAny -> AgdaAny
d1040 v0 v1 v2 v3 v4 v5 v6 = du1040 v6
du1040 :: T1004 -> AgdaAny -> AgdaAny
du1040 v0
  = let v1 = d1024 (coe v0) in
    let v2 = d888 (coe v1) in coe (du52 (coe (d268 (coe v2))))
name1042 = "Relation.Binary.IsDecTotalOrder._.reflexive"
d1042 :: T1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1042 v0
  = coe (d38 (coe (d268 (coe (d888 (coe (d1024 (coe v0))))))))
name1044 = "Relation.Binary.IsDecTotalOrder._.total"
d1044 ::
  T1004 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny
d1044 v0 = coe (d890 (coe (d1024 (coe v0))))
name1046 = "Relation.Binary.IsDecTotalOrder._.trans"
d1046 ::
  T1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1046 v0
  = coe (d40 (coe (d268 (coe (d888 (coe (d1024 (coe v0))))))))
name1048 = "Relation.Binary.IsDecTotalOrder._.∼-resp-≈"
d1048 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1004 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d1048 v0 v1 v2 v3 v4 v5 v6 = du1048 v6
du1048 :: T1004 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du1048 v0
  = let v1 = d1024 (coe v0) in
    let v2 = d888 (coe v1) in coe (du66 (coe (d268 (coe v2))))
name1050 = "Relation.Binary.IsDecTotalOrder._.∼-respʳ-≈"
d1050 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1050 v0 v1 v2 v3 v4 v5 v6 = du1050 v6
du1050 ::
  T1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1050 v0
  = let v1 = d1024 (coe v0) in
    let v2 = d888 (coe v1) in coe (du60 (coe (d268 (coe v2))))
name1052 = "Relation.Binary.IsDecTotalOrder._.∼-respˡ-≈"
d1052 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1052 v0 v1 v2 v3 v4 v5 v6 = du1052 v6
du1052 ::
  T1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1052 v0
  = let v1 = d1024 (coe v0) in
    let v2 = d888 (coe v1) in coe (du54 (coe (d268 (coe v2))))
name1056 = "Relation.Binary.IsDecTotalOrder.Eq.isDecEquivalence"
d1056 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T1004 -> T168
d1056 v0 v1 v2 v3 v4 v5 v6 = du1056 v6
du1056 :: T1004 -> T168
du1056 v0
  = coe
      (C1173
         (coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v0)))))))))
         (coe (d1026 (coe v0))))
name1060 = "Relation.Binary.IsDecTotalOrder.Eq._._≟_"
d1060 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1004 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1060 v0 v1 v2 v3 v4 v5 v6 = du1060 v6
du1060 ::
  T1004 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du1060 v0 = coe (d1026 (coe v0))
name1062 = "Relation.Binary.IsDecTotalOrder.Eq._.isEquivalence"
d1062 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1004 -> MAlonzo.Code.Relation.Binary.Core.T644
d1062 v0 v1 v2 v3 v4 v5 v6 = du1062 v6
du1062 :: T1004 -> MAlonzo.Code.Relation.Binary.Core.T644
du1062 v0
  = coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v0))))))))
name1064 = "Relation.Binary.IsDecTotalOrder.Eq._.refl"
d1064 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T1004 -> AgdaAny -> AgdaAny
d1064 v0 v1 v2 v3 v4 v5 v6 = du1064 v6
du1064 :: T1004 -> AgdaAny -> AgdaAny
du1064 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v0))))))))))
name1066 = "Relation.Binary.IsDecTotalOrder.Eq._.reflexive"
d1066 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1004 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d1066 v0 v1 v2 v3 v4 v5 v6 = du1066 v6
du1066 ::
  T1004 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du1066 v0
  = let v1 = du1056 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v1))) v2)
name1068 = "Relation.Binary.IsDecTotalOrder.Eq._.sym"
d1068 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1068 v0 v1 v2 v3 v4 v5 v6 = du1068 v6
du1068 :: T1004 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1068 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v0))))))))))
name1070 = "Relation.Binary.IsDecTotalOrder.Eq._.trans"
d1070 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1070 v0 v1 v2 v3 v4 v5 v6 = du1070 v6
du1070 ::
  T1004 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1070 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v0))))))))))
name1078 = "Relation.Binary.DecTotalOrder"
d1078 a0 a1 a2 = ()
newtype T1078 = C6485 T1004
name1094 = "Relation.Binary.DecTotalOrder.Carrier"
d1094 :: T1078 -> ()
d1094 = erased
name1096 = "Relation.Binary.DecTotalOrder._≈_"
d1096 :: T1078 -> AgdaAny -> AgdaAny -> ()
d1096 = erased
name1098 = "Relation.Binary.DecTotalOrder._≤_"
d1098 :: T1078 -> AgdaAny -> AgdaAny -> ()
d1098 = erased
name1100 = "Relation.Binary.DecTotalOrder.isDecTotalOrder"
d1100 :: T1078 -> T1004
d1100 v0
  = case coe v0 of
      C6485 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name1104 = "Relation.Binary.DecTotalOrder.DTO._≟_"
d1104 ::
  T1078 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1104 v0 = coe (d1026 (coe (d1100 (coe v0))))
name1106 = "Relation.Binary.DecTotalOrder.DTO._≤?_"
d1106 ::
  T1078 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1106 v0 = coe (d1028 (coe (d1100 (coe v0))))
name1108 = "Relation.Binary.DecTotalOrder.DTO.antisym"
d1108 ::
  T1078 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1108 v0
  = coe (d270 (coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))))
name1110 = "Relation.Binary.DecTotalOrder.DTO.isEquivalence"
d1110 :: T1078 -> MAlonzo.Code.Relation.Binary.Core.T644
d1110 v0
  = coe
      (d36
         (coe (d268 (coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))))))
name1112 = "Relation.Binary.DecTotalOrder.DTO.isPartialOrder"
d1112 :: T1078 -> T250
d1112 v0 = coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))
name1114 = "Relation.Binary.DecTotalOrder.DTO.isPreorder"
d1114 :: T1078 -> T16
d1114 v0
  = coe (d268 (coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))))
name1116 = "Relation.Binary.DecTotalOrder.DTO.isTotalOrder"
d1116 :: T1078 -> T870
d1116 v0 = coe (d1024 (coe (d1100 (coe v0))))
name1118 = "Relation.Binary.DecTotalOrder.DTO.refl"
d1118 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> AgdaAny -> AgdaAny
d1118 v0 v1 v2 v3 = du1118 v3
du1118 :: T1078 -> AgdaAny -> AgdaAny
du1118 v0
  = let v1 = d1100 (coe v0) in
    let v2 = d1024 (coe v1) in
    let v3 = d888 (coe v2) in coe (du52 (coe (d268 (coe v3))))
name1120 = "Relation.Binary.DecTotalOrder.DTO.reflexive"
d1120 :: T1078 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1120 v0
  = coe
      (d38
         (coe (d268 (coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))))))
name1122 = "Relation.Binary.DecTotalOrder.DTO.total"
d1122 ::
  T1078 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T14 AgdaAny AgdaAny AgdaAny AgdaAny
d1122 v0 = coe (d890 (coe (d1024 (coe (d1100 (coe v0))))))
name1124 = "Relation.Binary.DecTotalOrder.DTO.trans"
d1124 ::
  T1078 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1124 v0
  = coe
      (d40
         (coe (d268 (coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))))))
name1126 = "Relation.Binary.DecTotalOrder.DTO.∼-resp-≈"
d1126 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d1126 v0 v1 v2 v3 = du1126 v3
du1126 :: T1078 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du1126 v0
  = let v1 = d1100 (coe v0) in
    let v2 = d1024 (coe v1) in
    let v3 = d888 (coe v2) in coe (du66 (coe (d268 (coe v3))))
name1128 = "Relation.Binary.DecTotalOrder.DTO.∼-respʳ-≈"
d1128 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1128 v0 v1 v2 v3 = du1128 v3
du1128 ::
  T1078 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1128 v0
  = let v1 = d1100 (coe v0) in
    let v2 = d1024 (coe v1) in
    let v3 = d888 (coe v2) in coe (du60 (coe (d268 (coe v3))))
name1130 = "Relation.Binary.DecTotalOrder.DTO.∼-respˡ-≈"
d1130 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1130 v0 v1 v2 v3 = du1130 v3
du1130 ::
  T1078 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1130 v0
  = let v1 = d1100 (coe v0) in
    let v2 = d1024 (coe v1) in
    let v3 = d888 (coe v2) in coe (du54 (coe (d268 (coe v3))))
name1134 = "Relation.Binary.DecTotalOrder.DTO.Eq._≟_"
d1134 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1134 v0 v1 v2 v3 = du1134 v3
du1134 ::
  T1078 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du1134 v0 = let v1 = d1100 (coe v0) in coe (d1026 (coe v1))
name1136 = "Relation.Binary.DecTotalOrder.DTO.Eq.isDecEquivalence"
d1136 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> T168
d1136 v0 v1 v2 v3 = du1136 v3
du1136 :: T1078 -> T168
du1136 v0 = coe (du1056 (coe (d1100 (coe v0))))
name1138 = "Relation.Binary.DecTotalOrder.DTO.Eq.isEquivalence"
d1138 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 -> MAlonzo.Code.Relation.Binary.Core.T644
d1138 v0 v1 v2 v3 = du1138 v3
du1138 :: T1078 -> MAlonzo.Code.Relation.Binary.Core.T644
du1138 v0
  = let v1 = d1100 (coe v0) in
    coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v1))))))))
name1140 = "Relation.Binary.DecTotalOrder.DTO.Eq.refl"
d1140 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> AgdaAny -> AgdaAny
d1140 v0 v1 v2 v3 = du1140 v3
du1140 :: T1078 -> AgdaAny -> AgdaAny
du1140 v0
  = let v1 = d1100 (coe v0) in
    coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v1))))))))))
name1142 = "Relation.Binary.DecTotalOrder.DTO.Eq.reflexive"
d1142 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d1142 v0 v1 v2 v3 = du1142 v3
du1142 ::
  T1078 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du1142 v0
  = let v1 = d1100 (coe v0) in
    let v2 = du1056 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v2))) v3)
name1144 = "Relation.Binary.DecTotalOrder.DTO.Eq.sym"
d1144 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1144 v0 v1 v2 v3 = du1144 v3
du1144 :: T1078 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1144 v0
  = let v1 = d1100 (coe v0) in
    coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v1))))))))))
name1146 = "Relation.Binary.DecTotalOrder.DTO.Eq.trans"
d1146 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1146 v0 v1 v2 v3 = du1146 v3
du1146 ::
  T1078 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1146 v0
  = let v1 = d1100 (coe v0) in
    coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d36 (coe (d268 (coe (d888 (coe (d1024 (coe v1))))))))))
name1148 = "Relation.Binary.DecTotalOrder.totalOrder"
d1148 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> T928
d1148 v0 v1 v2 v3 = du1148 v3
du1148 :: T1078 -> T928
du1148 v0
  = coe
      (\ v1 v2 v3 v4 -> C5585 v4) erased erased erased
      (d1024 (coe (d1100 (coe v0))))
name1152 = "Relation.Binary.DecTotalOrder._.poset"
d1152 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> T304
d1152 v0 v1 v2 v3 = du1152 v3
du1152 :: T1078 -> T304
du1152 v0 = coe (du986 (coe (du1148 (coe v0))))
name1154 = "Relation.Binary.DecTotalOrder._.preorder"
d1154 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> T74
d1154 v0 v1 v2 v3 = du1154 v3
du1154 :: T1078 -> T74
du1154 v0
  = let v1 = du1148 (coe v0) in coe (du358 (coe (du986 (coe v1))))
name1158 = "Relation.Binary.DecTotalOrder.Eq.decSetoid"
d1158 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> T200
d1158 v0 v1 v2 v3 = du1158 v3
du1158 :: T1078 -> T200
du1158 v0
  = coe
      (\ v1 v2 v3 -> C1311 v3) erased erased
      (du1056 (coe (d1100 (coe v0))))
name1162 = "Relation.Binary.DecTotalOrder.Eq._._≈_"
d1162 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> AgdaAny -> AgdaAny -> ()
d1162 = erased
name1164 = "Relation.Binary.DecTotalOrder.Eq._._≟_"
d1164 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1164 v0 v1 v2 v3 = du1164 v3
du1164 ::
  T1078 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du1164 v0 = coe (d1026 (coe (d1100 (coe v0))))
name1166 = "Relation.Binary.DecTotalOrder.Eq._.Carrier"
d1166 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> ()
d1166 = erased
name1168 = "Relation.Binary.DecTotalOrder.Eq._.isDecEquivalence"
d1168 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> T168
d1168 v0 v1 v2 v3 = du1168 v3
du1168 :: T1078 -> T168
du1168 v0 = coe (du1056 (coe (d1100 (coe v0))))
name1170 = "Relation.Binary.DecTotalOrder.Eq._.isEquivalence"
d1170 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 -> MAlonzo.Code.Relation.Binary.Core.T644
d1170 v0 v1 v2 v3 = du1170 v3
du1170 :: T1078 -> MAlonzo.Code.Relation.Binary.Core.T644
du1170 v0
  = coe
      (d36
         (coe (d268 (coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))))))
name1172 = "Relation.Binary.DecTotalOrder.Eq._.preorder"
d1172 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> T74
d1172 v0 v1 v2 v3 = du1172 v3
du1172 :: T1078 -> T74
du1172 v0
  = let v1 = du1158 (coe v0) in coe (du158 (coe (du232 (coe v1))))
name1174 = "Relation.Binary.DecTotalOrder.Eq._.refl"
d1174 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> AgdaAny -> AgdaAny
d1174 v0 v1 v2 v3 = du1174 v3
du1174 :: T1078 -> AgdaAny -> AgdaAny
du1174 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe
            (d36
               (coe (d268 (coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))))))))
name1176 = "Relation.Binary.DecTotalOrder.Eq._.reflexive"
d1176 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d1176 v0 v1 v2 v3 = du1176 v3
du1176 ::
  T1078 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du1176 v0
  = let v1 = du1158 (coe v0) in
    let v2 = d216 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v2))) v3)
name1178 = "Relation.Binary.DecTotalOrder.Eq._.setoid"
d1178 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1078 -> T128
d1178 v0 v1 v2 v3 = du1178 v3
du1178 :: T1078 -> T128
du1178 v0 = coe (du232 (coe (du1158 (coe v0))))
name1180 = "Relation.Binary.DecTotalOrder.Eq._.sym"
d1180 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1180 v0 v1 v2 v3 = du1180 v3
du1180 :: T1078 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1180 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe
            (d36
               (coe (d268 (coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))))))))
name1182 = "Relation.Binary.DecTotalOrder.Eq._.trans"
d1182 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1078 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1182 v0 v1 v2 v3 = du1182 v3
du1182 ::
  T1078 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1182 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe
            (d36
               (coe (d268 (coe (d888 (coe (d1024 (coe (d1100 (coe v0))))))))))))
name1196 = "Relation.Binary.IsStrictTotalOrder"
d1196 a0 a1 a2 a3 a4 a5 = ()
data T1196
  = C7031 MAlonzo.Code.Relation.Binary.Core.T644
          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
          (AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362)
name1216 = "Relation.Binary.IsStrictTotalOrder.isEquivalence"
d1216 :: T1196 -> MAlonzo.Code.Relation.Binary.Core.T644
d1216 v0
  = case coe v0 of
      C7031 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name1218 = "Relation.Binary.IsStrictTotalOrder.trans"
d1218 ::
  T1196 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1218 v0
  = case coe v0 of
      C7031 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name1220 = "Relation.Binary.IsStrictTotalOrder.compare"
d1220 ::
  T1196 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362
d1220 v0
  = case coe v0 of
      C7031 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name1222 = "Relation.Binary.IsStrictTotalOrder._≟_"
d1222 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1222 v0 v1 v2 v3 v4 v5 v6 = du1222 v6
du1222 ::
  T1196 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du1222 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Consequences.du402
         (coe (d1220 (coe v0))))
name1224 = "Relation.Binary.IsStrictTotalOrder._<?_"
d1224 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1224 v0 v1 v2 v3 v4 v5 v6 = du1224 v6
du1224 ::
  T1196 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du1224 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Consequences.du438
         (coe (d1220 (coe v0))))
name1226 = "Relation.Binary.IsStrictTotalOrder.isDecEquivalence"
d1226 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T1196 -> T168
d1226 v0 v1 v2 v3 v4 v5 v6 = du1226 v6
du1226 :: T1196 -> T168
du1226 v0
  = coe (C1173 (coe (d1216 (coe v0))) (coe (du1222 (coe v0))))
name1230 = "Relation.Binary.IsStrictTotalOrder.Eq._≟_"
d1230 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1230 v0 v1 v2 v3 v4 v5 v6 = du1230 v6
du1230 ::
  T1196 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du1230 v0 = coe (du1222 (coe v0))
name1232 = "Relation.Binary.IsStrictTotalOrder.Eq.isEquivalence"
d1232 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 -> MAlonzo.Code.Relation.Binary.Core.T644
d1232 v0 v1 v2 v3 v4 v5 v6 = du1232 v6
du1232 :: T1196 -> MAlonzo.Code.Relation.Binary.Core.T644
du1232 v0 = coe (d1216 (coe v0))
name1234 = "Relation.Binary.IsStrictTotalOrder.Eq.refl"
d1234 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T1196 -> AgdaAny -> AgdaAny
d1234 v0 v1 v2 v3 v4 v5 v6 = du1234 v6
du1234 :: T1196 -> AgdaAny -> AgdaAny
du1234 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660 (coe (d1216 (coe v0))))
name1236 = "Relation.Binary.IsStrictTotalOrder.Eq.reflexive"
d1236 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d1236 v0 v1 v2 v3 v4 v5 v6 = du1236 v6
du1236 ::
  T1196 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du1236 v0
  = let v1 = du1226 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v1))) v2)
name1238 = "Relation.Binary.IsStrictTotalOrder.Eq.sym"
d1238 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1238 v0 v1 v2 v3 v4 v5 v6 = du1238 v6
du1238 :: T1196 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1238 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662 (coe (d1216 (coe v0))))
name1240 = "Relation.Binary.IsStrictTotalOrder.Eq.trans"
d1240 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1240 v0 v1 v2 v3 v4 v5 v6 = du1240 v6
du1240 ::
  T1196 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1240 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664 (coe (d1216 (coe v0))))
name1242 = "Relation.Binary.IsStrictTotalOrder.<-respˡ-≈"
d1242 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1242 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du1242 v2 v6 v7 v9
du1242 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1196 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1242 v0 v1 v2 v3
  = coe
      (\ v4 v5 ->
         MAlonzo.Code.Relation.Binary.Consequences.du558
           (coe v0) (coe (d1220 (coe v1))) (coe v2) (coe v3))
name1244 = "Relation.Binary.IsStrictTotalOrder.<-respʳ-≈"
d1244 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1244 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 = du1244 v2 v6 v7 v9
du1244 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1196 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1244 v0 v1 v2 v3
  = coe
      (\ v4 v5 ->
         MAlonzo.Code.Relation.Binary.Consequences.du474
           (coe v0) (coe (d1220 (coe v1))) (coe v2) (coe v3))
name1246 = "Relation.Binary.IsStrictTotalOrder.<-resp-≈"
d1246 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d1246 v0 v1 v2 v3 v4 v5 v6 = du1246 v2 v6
du1246 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1196 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du1246 v0 v1
  = coe
      (MAlonzo.Code.Agda.Builtin.Sigma.C32
         (coe (\ v2 v3 v4 -> du1244 (coe v0) (coe v1) v2 v4))
         (coe (\ v2 v3 v4 -> du1242 (coe v0) (coe v1) v2 v4)))
name1248
  = "Relation.Binary.IsStrictTotalOrder.isStrictPartialOrder"
d1248 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> T1196 -> T564
d1248 v0 v1 v2 v3 v4 v5 v6 = du1248 v2 v6
du1248 :: MAlonzo.Code.Agda.Primitive.T4 -> T1196 -> T564
du1248 v0 v1
  = coe
      (\ v2 v3 v4 v5 -> C3247 v2 v4 v5) (d1216 (coe v1)) erased
      (d1218 (coe v1)) (du1246 (coe v0) (coe v1))
name1252 = "Relation.Binary.IsStrictTotalOrder._.asym"
d1252 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d1252 = erased
name1254 = "Relation.Binary.IsStrictTotalOrder._.irrefl"
d1254 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T1196 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d1254 = erased
name1262 = "Relation.Binary.StrictTotalOrder"
d1262 a0 a1 a2 = ()
newtype T1262 = C8081 T1196
name1278 = "Relation.Binary.StrictTotalOrder.Carrier"
d1278 :: T1262 -> ()
d1278 = erased
name1280 = "Relation.Binary.StrictTotalOrder._≈_"
d1280 :: T1262 -> AgdaAny -> AgdaAny -> ()
d1280 = erased
name1282 = "Relation.Binary.StrictTotalOrder._<_"
d1282 :: T1262 -> AgdaAny -> AgdaAny -> ()
d1282 = erased
name1284 = "Relation.Binary.StrictTotalOrder.isStrictTotalOrder"
d1284 :: T1262 -> T1196
d1284 v0
  = case coe v0 of
      C8081 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
name1288 = "Relation.Binary.StrictTotalOrder._._<?_"
d1288 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1288 v0 v1 v2 v3 = du1288 v3
du1288 ::
  T1262 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du1288 v0 = coe (du1224 (coe (d1284 (coe v0))))
name1290 = "Relation.Binary.StrictTotalOrder._._≟_"
d1290 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1290 v0 v1 v2 v3 = du1290 v3
du1290 ::
  T1262 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du1290 v0 = coe (du1222 (coe (d1284 (coe v0))))
name1292 = "Relation.Binary.StrictTotalOrder._.<-resp-≈"
d1292 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
d1292 v0 v1 v2 v3 = du1292 v2 v3
du1292 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 -> MAlonzo.Code.Agda.Builtin.Sigma.T14
du1292 v0 v1 = coe (du1246 (coe v0) (coe (d1284 (coe v1))))
name1294 = "Relation.Binary.StrictTotalOrder._.<-respʳ-≈"
d1294 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1294 v0 v1 v2 v3 = du1294 v2 v3
du1294 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1294 v0 v1
  = coe (\ v2 v3 v4 -> du1244 (coe v0) (coe (d1284 (coe v1))) v2 v4)
name1296 = "Relation.Binary.StrictTotalOrder._.<-respˡ-≈"
d1296 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1296 v0 v1 v2 v3 = du1296 v2 v3
du1296 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1296 v0 v1
  = coe (\ v2 v3 v4 -> du1242 (coe v0) (coe (d1284 (coe v1))) v2 v4)
name1298 = "Relation.Binary.StrictTotalOrder._.asym"
d1298 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d1298 = erased
name1300 = "Relation.Binary.StrictTotalOrder._.compare"
d1300 ::
  T1262 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Binary.Core.T362
d1300 v0 = coe (d1220 (coe (d1284 (coe v0))))
name1302 = "Relation.Binary.StrictTotalOrder._.irrefl"
d1302 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Empty.T4
d1302 = erased
name1304 = "Relation.Binary.StrictTotalOrder._.isDecEquivalence"
d1304 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> T168
d1304 v0 v1 v2 v3 = du1304 v3
du1304 :: T1262 -> T168
du1304 v0 = coe (du1226 (coe (d1284 (coe v0))))
name1306 = "Relation.Binary.StrictTotalOrder._.isEquivalence"
d1306 :: T1262 -> MAlonzo.Code.Relation.Binary.Core.T644
d1306 v0 = coe (d1216 (coe (d1284 (coe v0))))
name1308
  = "Relation.Binary.StrictTotalOrder._.isStrictPartialOrder"
d1308 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> T564
d1308 v0 v1 v2 v3 = du1308 v2 v3
du1308 :: MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> T564
du1308 v0 v1 = coe (du1248 (coe v0) (coe (d1284 (coe v1))))
name1310 = "Relation.Binary.StrictTotalOrder._.trans"
d1310 ::
  T1262 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1310 v0 = coe (d1218 (coe (d1284 (coe v0))))
name1312 = "Relation.Binary.StrictTotalOrder.strictPartialOrder"
d1312 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> T622
d1312 v0 v1 v2 v3 = du1312 v2 v3
du1312 :: MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> T622
du1312 v0 v1
  = coe
      (\ v2 v3 v4 v5 -> C3899 v5) erased erased erased
      (du1248 (coe v0) (coe (d1284 (coe v1))))
name1314 = "Relation.Binary.StrictTotalOrder.decSetoid"
d1314 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> T200
d1314 v0 v1 v2 v3 = du1314 v3
du1314 :: T1262 -> T200
du1314 v0
  = coe
      (\ v1 v2 v3 -> C1311 v3) erased erased
      (du1226 (coe (d1284 (coe v0))))
name1318 = "Relation.Binary.StrictTotalOrder.Eq._≈_"
d1318 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> AgdaAny -> AgdaAny -> ()
d1318 = erased
name1320 = "Relation.Binary.StrictTotalOrder.Eq._≟_"
d1320 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
d1320 v0 v1 v2 v3 = du1320 v3
du1320 ::
  T1262 -> AgdaAny -> AgdaAny -> MAlonzo.Code.Relation.Nullary.T14
du1320 v0 = coe (du1222 (coe (d1284 (coe v0))))
name1322 = "Relation.Binary.StrictTotalOrder.Eq.Carrier"
d1322 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> ()
d1322 = erased
name1324 = "Relation.Binary.StrictTotalOrder.Eq.isDecEquivalence"
d1324 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> T168
d1324 v0 v1 v2 v3 = du1324 v3
du1324 :: T1262 -> T168
du1324 v0 = coe (du1226 (coe (d1284 (coe v0))))
name1326 = "Relation.Binary.StrictTotalOrder.Eq.isEquivalence"
d1326 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 -> MAlonzo.Code.Relation.Binary.Core.T644
d1326 v0 v1 v2 v3 = du1326 v3
du1326 :: T1262 -> MAlonzo.Code.Relation.Binary.Core.T644
du1326 v0 = coe (d1216 (coe (d1284 (coe v0))))
name1328 = "Relation.Binary.StrictTotalOrder.Eq.preorder"
d1328 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> T74
d1328 v0 v1 v2 v3 = du1328 v3
du1328 :: T1262 -> T74
du1328 v0
  = let v1 = du1314 (coe v0) in coe (du158 (coe (du232 (coe v1))))
name1330 = "Relation.Binary.StrictTotalOrder.Eq.refl"
d1330 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> AgdaAny -> AgdaAny
d1330 v0 v1 v2 v3 = du1330 v3
du1330 :: T1262 -> AgdaAny -> AgdaAny
du1330 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d660
         (coe (d1216 (coe (d1284 (coe v0))))))
name1332 = "Relation.Binary.StrictTotalOrder.Eq.reflexive"
d1332 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d1332 v0 v1 v2 v3 = du1332 v3
du1332 ::
  T1262 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
du1332 v0
  = let v1 = du1314 (coe v0) in
    let v2 = d216 (coe v1) in
    coe
      (\ v3 v4 v5 ->
         MAlonzo.Code.Relation.Binary.Core.du666 (coe (d182 (coe v2))) v3)
name1334 = "Relation.Binary.StrictTotalOrder.Eq.setoid"
d1334 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 -> T1262 -> T128
d1334 v0 v1 v2 v3 = du1334 v3
du1334 :: T1262 -> T128
du1334 v0 = coe (du232 (coe (du1314 (coe v0))))
name1336 = "Relation.Binary.StrictTotalOrder.Eq.sym"
d1336 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1336 v0 v1 v2 v3 = du1336 v3
du1336 :: T1262 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1336 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d662
         (coe (d1216 (coe (d1284 (coe v0))))))
name1338 = "Relation.Binary.StrictTotalOrder.Eq.trans"
d1338 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  T1262 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d1338 v0 v1 v2 v3 = du1338 v3
du1338 ::
  T1262 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du1338 v0
  = coe
      (MAlonzo.Code.Relation.Binary.Core.d664
         (coe (d1216 (coe (d1284 (coe v0))))))
