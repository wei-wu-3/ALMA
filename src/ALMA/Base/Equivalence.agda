------------------------------------------------------------------------
--     Core.agda                               centre of the lattice
--     SubstTransport.agda                     layer relations + bridge
--     Properties.agda                         generic laws of LayeredEqGen and specialisations
--     LayeredEqGenDepth.agda                  depth-bounded truncation
--     Map.agda                                preservation under maps
--     ScaleInvariant.agda                     LayeredEq / trivial layer
--     DiscreteEq.agda                         drop next-eq
--     GroupInvariant.agda                     ScaleInvariant / group action
--     LinearDynamics.agda                     ScaleInvariant / no branching
--     TopologicalEq.agda                      DiscreteEq / topology
--     ManifoldEq.agda                         LayeredEqGen / single-directional charts
--     Lattice.agda                            projections and joint projection
--     StrongEquiv.agda                        category-level bridge
--
--     Core.agda                               格的中央
--     SubstTransport.agda                     同层关系与桥接
--     Properties.agda                         LayeredEqGen 的通用律与特化
--     LayeredEqGenDepth.agda                  深度有界截断
--     Map.agda                                映射下的保持性
--     ScaleInvariant.agda                     LayeredEq / 平凡层
--     DiscreteEq.agda                         去掉 next-eq
--     GroupInvariant.agda                     ScaleInvariant / 群作用
--     LinearDynamics.agda                     ScaleInvariant / 无分支
--     TopologicalEq.agda                      DiscreteEq / 拓扑
--     ManifoldEq.agda                         LayeredEqGen / 单向坐标卡
--     Lattice.agda                            投影与联合投影
--     StrongEquiv.agda                        范畴层桥接
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence where

------------------------------------------------------------------------
-- Core: the centre of the degeneration lattice
--
-- 核心：退化格的中央
open import ALMA.Base.Equivalence.Core public

------------------------------------------------------------------------
-- SubstTransport: layer relations and the adjunction bridge
--
-- 传输：同层关系与伴随桥接
open import ALMA.Base.Equivalence.SubstTransport public

------------------------------------------------------------------------
-- Generic properties, LayeredEqGenDepth, and preservation of LayeredEq
--
-- LayeredEq 的通用性质、深度与保持性
open import ALMA.Base.Equivalence.Properties public
open import ALMA.Base.Equivalence.LayeredEqGenDepth public
open import ALMA.Base.Equivalence.Map public

------------------------------------------------------------------------
-- Degeneration: ScaleInvariant
--
-- 退化：ScaleInvariant
open import ALMA.Base.Equivalence.ScaleInvariant public

------------------------------------------------------------------------
-- Degeneration: DiscreteEq
--
-- 退化：DiscreteEq
open import ALMA.Base.Equivalence.DiscreteEq public

------------------------------------------------------------------------
-- Further degenerations of ScaleInvariant
--
-- ScaleInvariant 的更深退化
open import ALMA.Base.Equivalence.GroupInvariant public
open import ALMA.Base.Equivalence.LinearDynamics public

------------------------------------------------------------------------
-- Further degenerations of DiscreteEq
--
-- DiscreteEq 的更深退化
open import ALMA.Base.Equivalence.TopologicalEq public
open import ALMA.Base.Equivalence.ManifoldEq public

------------------------------------------------------------------------
-- Lattice structure: projections and the joint projection
--
-- 格结构：投影与联合投影
open import ALMA.Base.Equivalence.Lattice public

------------------------------------------------------------------------
-- Category-level bridge: StrongEquivalence
--
-- 范畴层桥接：StrongEquivalence
open import ALMA.Base.Equivalence.StrongEquiv public
