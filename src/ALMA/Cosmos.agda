------------------------------------------------------------------------
-- Cosmos, carried M-base entry point
--
-- This module is a thin re-export surface: a single `import
-- ALMA.Cosmos` brings the container primitives, the M-Cosmos object /
-- category / terminal layers, and the carried colimit machinery. The
-- further M witness modules are brought into the entry's closure so
-- the whole world is type-checked together; refer to them by their
-- qualified module names.
--
-- Cosmos，携带式 M 底座入口
--
-- 本模块是薄 re-export 面：单个 `import ALMA.Cosmos` 即带出容器基件、
-- M-Cosmos 对象/范畴/终性层与携带式余极限机器。其余 M 见证模块以
-- import 纳入入口闭包，使整个世界一并受类型检查；请以限定模块名引用
-- 它们。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos where

------------------------------------------------------------------------
-- Container base
--
-- The four modules the M kernel is built on.
--
-- 容器基件
--
-- M 内核所依赖的四个模块。

open import ALMA.Cosmos.ContCategory public
open import ALMA.Cosmos.ContCategoryLemmas public
open import ALMA.Cosmos.ContCatEquiv public
open import ALMA.Cosmos.ContFunctor public

------------------------------------------------------------------------
-- M-Cosmos object layer, category and terminality
--
-- The container cosmos as the constant-index (I = ⊤) special case.
--
-- M-Cosmos 对象层、范畴与终性
--
-- 容器宇宙作为常数索引（I = ⊤）特例。

open import ALMA.Cosmos.M.Object public
open import ALMA.Cosmos.M.Terminal public
open import ALMA.Cosmos.M.CoalgCat public
open import ALMA.Cosmos.M.CosmosCategory public

import ALMA.Cosmos.M.ContainerInstance
import ALMA.Cosmos.M.Lambek

------------------------------------------------------------------------
-- Deterministic / label-changing congruence engines and witnesses
--
-- 确定性/改标签同余引擎与见证

import ALMA.Cosmos.M.DetCongruence
import ALMA.Cosmos.M.GenCongruence
import ALMA.Cosmos.M.ListCosmos
import ALMA.Cosmos.M.ListSwap
import ALMA.Cosmos.M.ListSwapDef
import ALMA.Cosmos.M.MorphismCorrespondence
import ALMA.Cosmos.M.ContainerAutomorphism

------------------------------------------------------------------------
-- Constructive separation / obstruction / limit slices
--
-- 构造性分离/障碍/极限切片

import ALMA.Cosmos.M.TowerSeparation
import ALMA.Cosmos.M.PermutationNonCommutative
import ALMA.Cosmos.M.NontrivialLimit
import ALMA.Cosmos.M.SewingObstruction
import ALMA.Cosmos.M.PermutedEmbedding

------------------------------------------------------------------------
-- Carried finite / sequential colimit universal properties and
-- boundaries
--
-- These modules re-export one another (e.g. FinColimit opens
-- SeqColimit), so they are brought into the entry's closure with
-- qualified `import` rather than public re-export, to avoid name
-- clashes; use them by their qualified module names.
--
-- 携带式有限/序列余极限泛性质与边界
--
-- 这些模块彼此重导出（如 FinColimit open 了 SeqColimit），故以限定
-- import 纳入入口闭包而非公开重导出，以免撞名；请用限定模块名。

import ALMA.Cosmos.Carried.SeqColimit
import ALMA.Cosmos.Carried.FinColimit
import ALMA.Cosmos.Carried.FinTower
import ALMA.Cosmos.Carried.LimitSystem
import ALMA.Cosmos.Carried.DetColimit
import ALMA.Cosmos.Carried.DetSys
import ALMA.Cosmos.Carried.TrivProj
import ALMA.Cosmos.Carried.FinNatUIP
import ALMA.Cosmos.Carried.FinProj
import ALMA.Cosmos.Carried.Boundaries
import ALMA.Cosmos.Carried.FinEmbed

------------------------------------------------------------------------
-- Setoid-carried sequential colimit and same-index wide subcategory
--
-- The setoid (ˢ) variants of the colimit stack: MCorrSetoid-based
-- sequential colimits, the same-index wide subcategory, the Fin push
-- tower and its colimit, and the polarity / pull-tower boundaries.
-- Brought in with qualified `import` for the same reason as the
-- propositional stack above.
--
-- setoid 携带式序列余极限与同索引宽子范畴
--
-- 余极限栈的 setoid（ˢ）变体：基于 MCorrSetoid 的序列余极限、同索引
-- 宽子范畴、Fin push 塔及其余极限、以及极性与 pull 塔边界。与上面的
-- 命题栈同样以限定 import 纳入。

import ALMA.Cosmos.Carried.SeqColimitS
import ALMA.Cosmos.Carried.SeqColimitCat
import ALMA.Cosmos.Carried.LimitSystemS
import ALMA.Cosmos.Carried.SameIndexCatS
import ALMA.Cosmos.Carried.SameIndexColimitS
import ALMA.Cosmos.Carried.FinPushColimitS
import ALMA.Cosmos.Carried.FinPushMediateS
import ALMA.Cosmos.Carried.FinPushColimitCat
import ALMA.Cosmos.Carried.ColimitPolarity
import ALMA.Cosmos.Carried.NontrivialPullTowerS
import ALMA.Cosmos.Carried.NontrivialPushTowerS
