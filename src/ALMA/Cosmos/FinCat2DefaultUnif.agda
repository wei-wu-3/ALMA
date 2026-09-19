------------------------------------------------------------------------
-- Default uniform embedding family for the FinCat 2 tower
-- FinCat 2 塔的默认一致嵌入族
--
-- Constructs default-unif from the tower's structural facts
-- (twoTower-retract and twoTower-collapsible), applies surj to obtain
-- SurjectivityForTower, and assembles the unconditional universal limit
-- and non-triviality witness
-- 从塔的结构事实（twoTower-retract 与 twoTower-collapsible）构造
-- default-unif，应用 surj 得到 SurjectivityForTower，
-- 并组装无条件的通用极限与非平凡见证
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --exact-split --guardedness --double-check #-}

module ALMA.Cosmos.FinCat2DefaultUnif where

open import Agda.Builtin.Equality using (refl)

open import ALMA.Cosmos.CumulativeHierarchy using (mkEmbeddingData)
open import ALMA.Cosmos.FinCat2TowerLemmas using (twoTower-collapsible; twoTower-retract)
open import ALMA.Cosmos.FinCat2ColimitWithDep
  using (UniformEmbeddingFamilyForTower; SurjectivityForTower; UniversalLimitDep
        ; NontrivialLimitDep; dependentUniversalLimitDep; dependentNontrivialDep)
open import ALMA.Cosmos.FinCat2Surjectivity using (surj)

-- Default uniform family: retraction from twoTower-retract, collapsibility
-- from twoTower-collapsible, next-consistent by refl
-- 默认一致族：收缩来自 twoTower-retract，可坍缩性来自
-- twoTower-collapsible，next-consistent 由 refl 得证
default-unif : UniformEmbeddingFamilyForTower
default-unif n = record
  { family = record
      { getData = mkEmbeddingData (twoTower-retract n) (twoTower-collapsible n) }
  ; next-consistent = λ _ _ → refl
  }

-- Surjectivity for the default family, from the unconditional surj
-- 默认族的满射性，由无条件的 surj 给出
surj-default : SurjectivityForTower default-unif
surj-default = surj default-unif

-- Unconditional universal limit over the default family
-- 默认族上无条件的通用极限
dependentUniversalLimit-default : UniversalLimitDep default-unif
dependentUniversalLimit-default = dependentUniversalLimitDep default-unif surj-default

-- Unconditional non-triviality witness over the default family
-- 默认族上无条件的非平凡见证
dependentNontrivial-default : NontrivialLimitDep dependentUniversalLimit-default
dependentNontrivial-default = dependentNontrivialDep default-unif surj-default
