------------------------------------------------------------------------
-- ALMA — Cosmos, carried M-base entry point.
--
-- This module USED TO define the container terminal coalgebra directly
-- (record Cosmos over Unfolding, its homomorphisms, UnitCosmos).  That
-- construction carried the position/subst machinery and the strict
-- cumulative hierarchy that the carried M base eliminates:
--
--   * the indexed coinductive type Mᵢ (Base.IndexedMType) carries no
--     equality, so comparing morphisms no longer introduces subst —
--     relocation is a carried fibre adjunction FiberAdjˢ (function),
--     not a transport;
--   * iterating the container ShapeCat is iterating the M index
--     MO.I = Σ (Obj C) (ShapeOf FC), so the strict level tower is
--     absorbed inductively; CosmosM is universe-polymorphic in one
--     level with no per-step lifting.
--
-- The container cosmos is now a SPECIAL CASE (constant index I = ⊤) of
-- the indexed M-Cosmos, exported from Cosmos.M.ContainerInstance, and
-- every result of the old Unfolding / strict-hierarchy machine is
-- re-established under Cosmos.M and Cosmos.Carried (see
-- Cosmos.M.HierarchyAbsorption for the coverage manifest).
--
-- This file is therefore a thin re-export surface: a single
-- `import ALMA.Cosmos` brings the container primitives, the M-Cosmos
-- object/category/terminal layers and the carried colimit machinery.
-- The further M witness modules (Lambek, congruence engines, list/swap,
-- automorphisms, obstruction slices) are imported into the entry's
-- closure so the whole world is type-checked together; refer to them by
-- their qualified module names.
--
-- ALMA —— Cosmos，携带式 M 底座入口。
--
-- 本模块曾直接定义容器终余代数（基于 Unfolding 的 record Cosmos、其态
-- 射、UnitCosmos）。该构造携带位置/subst 机器与严格累积层级，而携带式
-- M 底座将其消除：
--
--   * 索引余归纳类型 Mᵢ（Base.IndexedMType）不携带等式，故比较态射不再
--     引入 subst——重定位是携带式纤维伴随 FiberAdjˢ（函数），不是传输；
--   * 迭代容器 ShapeCat 就是迭代 M 索引
--     MO.I = Σ (Obj C) (ShapeOf FC)，严格层塔被归纳吸收；CosmosM 在单一
--     层次 universe 多态，无需逐层抬级。
--
-- 容器宇宙现在是索引 M-Cosmos 的特例（常数索引 I = ⊤），由
-- Cosmos.M.ContainerInstance 导出；旧 Unfolding/严格层级机器的每个结果
-- 都在 Cosmos.M 与 Cosmos.Carried 下重建（覆盖清单见
-- Cosmos.M.HierarchyAbsorption）。
--
-- 故本文件是薄 re-export 面：单个 `import ALMA.Cosmos` 即带出容器基件、
-- M-Cosmos 对象/范畴/终性层与携带式余极限机器。其余 M 见证模块
-- （Lambek、同余引擎、list/swap、自同构、障碍切片）以 import 纳入入口
-- 闭包，使整个世界一并受类型检查；请以限定模块名引用它们。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos where

------------------------------------------------------------------------
-- Container base: the four modules the M kernel is built on.
-- 容器基件：M 内核所依赖的四个模块。
------------------------------------------------------------------------
open import ALMA.Cosmos.ContCategory public
open import ALMA.Cosmos.ContCategoryLemmas public
open import ALMA.Cosmos.ContCatEquiv public
open import ALMA.Cosmos.ContFunctor public

------------------------------------------------------------------------
-- M-Cosmos object layer, category and terminality.
-- M-Cosmos 对象层、范畴与终性。
------------------------------------------------------------------------
open import ALMA.Cosmos.M.Object public
open import ALMA.Cosmos.M.Terminal public
open import ALMA.Cosmos.M.CoalgCat public
open import ALMA.Cosmos.M.CosmosCategory public

-- The container cosmos as the constant-index (I = ⊤) special case.
-- 容器宇宙作为常数索引（I = ⊤）特例。
import ALMA.Cosmos.M.ContainerInstance
import ALMA.Cosmos.M.Lambek

------------------------------------------------------------------------
-- Deterministic / label-changing congruence engines and witnesses.
-- 确定性/改标签同余引擎与见证。
------------------------------------------------------------------------
import ALMA.Cosmos.M.DetCongruence
import ALMA.Cosmos.M.GenCongruence
import ALMA.Cosmos.M.ListCosmos
import ALMA.Cosmos.M.ListSwap
import ALMA.Cosmos.M.ListSwapDef
import ALMA.Cosmos.M.MorphismCorrespondence
import ALMA.Cosmos.M.ContainerAutomorphism

------------------------------------------------------------------------
-- Constructive separation / obstruction / limit slices.
-- 构造性分离/障碍/极限切片。
------------------------------------------------------------------------
import ALMA.Cosmos.M.TowerSeparation
import ALMA.Cosmos.M.PermutationNonCommutative
import ALMA.Cosmos.M.NontrivialLimit
import ALMA.Cosmos.M.SewingObstruction
import ALMA.Cosmos.M.PermutedEmbedding
import ALMA.Cosmos.M.HierarchyAbsorption

------------------------------------------------------------------------
-- Carried finite/sequential colimit universal properties and boundaries.
-- 携带式有限/序列余极限泛性质与边界。
------------------------------------------------------------------------
-- The carried colimit modules re-export one another (e.g. FinColimit
-- opens SeqColimit), so they are brought into the entry's closure with
-- qualified `import` rather than public re-export to avoid name clashes;
-- use them by their qualified module names.
--
-- 携带式余极限模块彼此重导出（如 FinColimit open 了 SeqColimit），故以
-- 限定 import 纳入入口闭包而非公开重导出，以免撞名；请用限定模块名。
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
