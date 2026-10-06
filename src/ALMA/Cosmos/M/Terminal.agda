------------------------------------------------------------------------
-- Terminality of the M-Cosmos (carried, zero-subst).
--
-- This is the M-base replacement for the legacy Cosmos/Terminal.agda,
-- which proved terminality of the seed-threaded record Cosmos up to the
-- subst-based _≈C_ bisimulation.  Here self-reference is native to M, so
-- the terminal coalgebra vocabulary is directly that of Cosmos/M/Object:
--
--   existence    : ana γ            the anamorphism from any one-step
--                                  state coalgebra γ, by M's guarded
--                                  corecursion (the edge (p , ≡refl) is
--                                  matched constructively, never J/subst);
--   observation  : unfold-coalgebra the canonical coalgebra on CosmosM
--                                  itself (label = head, child = step);
--   eta / terminal: ana-unfold and ana-unfold˘, showing ana of the
--                                  observation coalgebra is the identity
--                                  up to the carried bisimulation
--                                  ≈CosmosM, in both directions.
--
-- This module is the canonical namespace the M-base CoalgCat / Lambek
-- migration will import.  The general fusion / uniqueness lemma for an
-- arbitrary coalgebra homomorphism (stated with a constructive head
-- equation matched as ≡refl, so no equality is eliminated; non-
-- propositional labels additionally require the edge adjunction) is the
-- next focused lemma and is intentionally not threaded through subst.
--
-- M-Cosmos 的终性（携带式，零 subst）。
--
-- 本模块是旧 Cosmos/Terminal.agda 的 M 底座替代：旧模块在基于 subst 的
-- _≈C_ 互模拟下证明经种子绕行的 record Cosmos 的终性。此处自指为 M 内
-- 建，故终余代数词表直接就是 Cosmos/M/Object 的词表：
--
--   存在性    ：ana γ，由 M 的受保护余递归从任意一步状态余代数 γ 给出
--               anamorphism（边 (p , ≡refl) 被构造性匹配，绝不用
--               J/subst）；
--   观察余代数：unfold-coalgebra，CosmosM 自身上的典范余代数（label 取
--               头部，child 取 step）；
--   eta/终性  ：ana-unfold 与 ana-unfold˘，双向表明对观察余代数取 ana
--               在携带互模拟 ≈CosmosM 下为恒等。
--
-- 本模块是 M 底座 CoalgCat / Lambek 迁移将导入的规范命名空间。任意余
-- 代数同态的一般融合/唯一性引理（以构造性头部等式、按 ≡refl 匹配表述，
-- 不消去等式；非命题标签还需边伴随）是下一个聚焦引理，刻意不经 subst。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.Terminal where

-- Re-export the carried terminal-coalgebra vocabulary of Cosmos/M/Object
-- as the canonical M-base terminality namespace.  All names keep C FC as
-- their leading explicit parameters, e.g. ana C FC γ i x.
--
-- 将 Cosmos/M/Object 的携带式终余代数词表再导出为 M 底座终性规范命名空
-- 间；所有名字以 C FC 为首显式参，例如 ana C FC γ i x。
open import ALMA.Cosmos.M.Object as MO

open MO public
  using ( CosmosM ; Rooted ; step ; next ; nextOf
        ; Coalgebra ; ana ; unfold-coalgebra
        ; ≈CosmosM ; ≈CosmosM-refl
        ; ana-unfold ; ana-unfold˘ )
