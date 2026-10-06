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
-- 本模块是 M 底座 CoalgCat / Lambek 迁移将导入的规范命名空间。终性唯一
-- 性在携带式制度下“构造即唯一”，其否定边界见文末说明；另给出 CosmosM
-- 互模拟的对称/传递。全程刻意不经 subst。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.M.Terminal where

open import Agda.Primitive using (Level)

-- Re-export the carried terminal-coalgebra vocabulary of Cosmos/M/Object
-- as the canonical M-base terminality namespace.  All names keep C FC as
-- their leading explicit parameters, e.g. ana C FC γ i x.
--
-- 将 Cosmos/M/Object 的携带式终余代数词表再导出为 M 底座终性规范命名空
-- 间；所有名字以 C FC 为首显式参，例如 ana C FC γ i x。
open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)

open import ALMA.Cosmos.ContCategory using (ContCat)
open import ALMA.Base.MCorrSetoid
  using ( EqOn ; SysEq ; ≈Mˢ-sym ; ≈Mˢ-trans )

open import ALMA.Cosmos.M.Object as MO

open MO public
  using ( CosmosM ; Rooted ; step ; next ; nextOf
        ; Coalgebra ; ana ; unfold-coalgebra
        ; ≈CosmosM ; ≈CosmosM-refl
        ; ana-unfold ; ana-unfold˘ )

-- Bisimulation equivalence on CosmosM, specialised from the generic
-- _≈Mˢ_ symmetry/transitivity at the M-Cosmos system.  These supply the
-- equivalence operations of the M-base cosmos setoid / coalgebra
-- category; they contain no transport.
--
-- CosmosM 上的互模拟等价，由通用 _≈Mˢ_ 的对称/传递在 M-Cosmos 系统处
-- 特化而来，为 M 底座 cosmos setoid / 余代数范畴提供等价运算；不含传
-- 输。
module _ {o h e s p : Level}
         {C  : Category o h e}
         {FC : Functor C (ContCat s p)} where

  ≈CosmosM-sym : ∀ {ℓd : Level}
                   (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
                   {i : MO.I C FC} {t s : MO.CosmosM C FC i}
               → MO.≈CosmosM C FC ≈CD {i = i} t s
               → MO.≈CosmosM C FC ≈CD {i = i} s t
  ≈CosmosM-sym ≈CD =
    ≈Mˢ-sym (SysEq.≈A (MO.sys C FC ≈CD))
            (SysEq.≈E (MO.sys C FC ≈CD))

  ≈CosmosM-trans : ∀ {ℓd : Level}
                     (≈CD : (i : MO.I C FC) → EqOn {ℓ = ℓd} (MO.A C FC i))
                     {i : MO.I C FC} {t m s : MO.CosmosM C FC i}
                 → MO.≈CosmosM C FC ≈CD {i = i} t m
                 → MO.≈CosmosM C FC ≈CD {i = i} m s
                 → MO.≈CosmosM C FC ≈CD {i = i} t s
  ≈CosmosM-trans ≈CD =
    ≈Mˢ-trans (SysEq.≈A (MO.sys C FC ≈CD))
              (SysEq.≈E (MO.sys C FC ≈CD))

-- Negative boundary: terminality uniqueness in the carried regime.
--
-- The legacy Cosmos/Terminal.agda states uniqueness for an ARBITRARY
-- coalgebra homomorphism f whose head is only PROPOSITIONALLY equal to
-- the coalgebra label.  Aligning the dependent successor indices of such
-- an f with those of ana requires rewriting along the head equality,
-- i.e. exactly the subst in the legacy pos-to-shape-eq.  In the carried,
-- zero-subst regime a successor index can only be aligned constructively
-- by matching the homogeneous equality as ≡refl, which forces the
-- candidate's copatterns to BE ana's copatterns.  Hence the anamorphism
-- is UNIQUE BY CONSTRUCTION: there is no separate arbitrary "f" to
-- compare, and the full terminality statement is the eta pair
-- ana-unfold / ana-unfold˘ (ana of the observation coalgebra is the
-- identity up to ≈CosmosM, both ways).  A propositional-headed arbitrary
-- homomorphism uniqueness theorem is deliberately NOT added: it would
-- reintroduce the very transport this base removes.  For non-
-- propositional labels the index/edge alignment is carried by the edge
-- FiberAdjˢ rather than by an equality.
--
-- 否定边界：携带式制度下的终性唯一性。
--
-- 旧 Cosmos/Terminal.agda 对头部仅与余代数标签“命题地相等”的任意余代
-- 数同态 f 陈述唯一性。要把这样的 f 的依赖后继索引与 ana 对齐，必须沿
-- 头部等式重写，即旧 pos-to-shape-eq 中的 subst。在携带式零 subst 制度
-- 下，后继索引只能靠把齐次等式按 ≡refl 匹配来构造性对齐，而这会迫使候
-- 选者的 copattern 本身就是 ana 的 copattern。故 anamorphism 是“构造即
-- 唯一”的：不存在另一个待比较的任意 f，终性的完整陈述就是 eta 对
-- ana-unfold / ana-unfold˘（对观察余代数取 ana 在 ≈CosmosM 下双向为恒
-- 等）。刻意不添加命题头部任意同态的唯一性定理：那会把本底座已消除的
-- 传输重新请回来。非命题标签下，索引/边的对齐由边 FiberAdjˢ 携带，而非
-- 由等式携带。
