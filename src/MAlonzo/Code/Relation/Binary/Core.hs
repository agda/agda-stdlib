{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Relation.Binary.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty

name12 = "Relation.Binary.Core.REL"
d12 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> MAlonzo.Code.Agda.Primitive.T4 -> ()
d12 = erased
name24 = "Relation.Binary.Core.Rel"
d24 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> MAlonzo.Code.Agda.Primitive.T4 -> ()
d24 = erased
name42 = "Relation.Binary.Core._⇒_"
d42 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d42 = erased
name64 = "Relation.Binary.Core._=[_]⇒_"
d64 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> ()) -> ()
d64 = erased
name84 = "Relation.Binary.Core._Preserves_⟶_"
d84 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d84 = erased
name110 = "Relation.Binary.Core._Preserves₂_⟶_⟶_"
d110 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d110 = erased
name134 = "Relation.Binary.Core.Reflexive"
d134 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> ()
d134 = erased
name152 = "Relation.Binary.Core.Irreflexive"
d152 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d152 = erased
name174 = "Relation.Binary.Core.Sym"
d174 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d174 = erased
name186 = "Relation.Binary.Core.Symmetric"
d186 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> ()
d186 = erased
name208 = "Relation.Binary.Core.Trans"
d208 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d208 = erased
name240 = "Relation.Binary.Core.TransFlip"
d240 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d240 = erased
name260 = "Relation.Binary.Core.Transitive"
d260 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> ()
d260 = erased
name278 = "Relation.Binary.Core.Antisym"
d278 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d278 = erased
name298 = "Relation.Binary.Core.Antisymmetric"
d298 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d298 = erased
name310 = "Relation.Binary.Core.Asymmetric"
d310 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> ()
d310 = erased
name330 = "Relation.Binary.Core.Conn"
d330 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d330 = erased
name346 = "Relation.Binary.Core.Total"
d346 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> ()
d346 = erased
name362 = "Relation.Binary.Core.Tri"
d362 a0 a1 a2 a3 a4 a5 = ()
data T362 = C382 AgdaAny | C390 AgdaAny | C398 AgdaAny
name408 = "Relation.Binary.Core.Trichotomous"
d408 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d408 = erased
name418 = "Relation.Binary.Core._._>_"
d418 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d418 = erased
name430 = "Relation.Binary.Core.Maximum"
d430 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> ()
d430 = erased
name444 = "Relation.Binary.Core.Minimum"
d444 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> ()
d444 = erased
name456 = "Relation.Binary.Core._Respects_"
d456 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> (AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d456 = erased
name478 = "Relation.Binary.Core._Respectsʳ_"
d478 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d478 = erased
name498 = "Relation.Binary.Core._Respectsˡ_"
d498 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d498 = erased
name514 = "Relation.Binary.Core._Respects₂_"
d514 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> ()) -> ()
d514 = erased
name528 = "Relation.Binary.Core.Substitutive"
d528 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> MAlonzo.Code.Agda.Primitive.T4 -> ()
d528 = erased
name548 = "Relation.Binary.Core.Decidable"
d548 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> ()
d548 = erased
name566 = "Relation.Binary.Core.WeaklyDecidable"
d566 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> ()
d566 = erased
name584 = "Relation.Binary.Core.Irrelevant"
d584 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> ()
d584 = erased
name608 = "Relation.Binary.Core.NonEmpty"
d608 a0 a1 a2 a3 a4 a5 = ()
data T608 = C634 AgdaAny AgdaAny AgdaAny
name628 = "Relation.Binary.Core.NonEmpty.x"
d628 :: T608 -> AgdaAny
d628 v0
  = case coe v0 of
      C634 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name630 = "Relation.Binary.Core.NonEmpty.y"
d630 :: T608 -> AgdaAny
d630 v0
  = case coe v0 of
      C634 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name632 = "Relation.Binary.Core.NonEmpty.proof"
d632 :: T608 -> AgdaAny
d632 v0
  = case coe v0 of
      C634 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name644 = "Relation.Binary.Core.IsEquivalence"
d644 a0 a1 a2 a3 = ()
data T644
  = C2867 (AgdaAny -> AgdaAny)
          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
          (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
name660 = "Relation.Binary.Core.IsEquivalence.refl"
d660 :: T644 -> AgdaAny -> AgdaAny
d660 v0
  = case coe v0 of
      C2867 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name662 = "Relation.Binary.Core.IsEquivalence.sym"
d662 :: T644 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d662 v0
  = case coe v0 of
      C2867 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
name664 = "Relation.Binary.Core.IsEquivalence.trans"
d664 ::
  T644 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d664 v0
  = case coe v0 of
      C2867 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
name666 = "Relation.Binary.Core.IsEquivalence.reflexive"
d666 ::
  MAlonzo.Code.Agda.Primitive.T4 ->
  MAlonzo.Code.Agda.Primitive.T4 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  T644 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T12 -> AgdaAny
d666 v0 v1 v2 v3 v4 v5 v6 v7 = du666 v4 v5
du666 :: T644 -> AgdaAny -> AgdaAny
du666 v0 v1 = coe d660 v0 v1
