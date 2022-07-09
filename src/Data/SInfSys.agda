------------------------------------------------------------------------
-- The Agda standard library
--
-- Library for (Generalized) Inference Systems
-- paper    : "Flexible Coinduction in Agda" @ ITP 2021
-- authors  : Luca Ciccone, Francesco Dagnino, Elena Zucca
-- doi      : https://doi.org/10.4230/LIPIcs.ITP.2021.13
-- examples : https://github.com/LcicC/inference-systems-agda
------------------------------------------------------------------------

{-# OPTIONS --sized-types --without-K #-}

-- Using Sized Types
module Data.SInfSys {𝓁} where

  open import Data.InfSys.Base {𝓁} public
  open import Data.InfSys.Induction {𝓁} public
  open import Data.InfSys.SCoinduction {𝓁} public
  open import Data.InfSys.FlexSCoinduction {𝓁} public
  open MetaRule public
  open FinMetaRule public
  open IS public
