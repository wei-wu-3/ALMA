------------------------------------------------------------------------
-- Carried limit system for the FinCat tower — existence core (zero subst).
--
-- The finite stages are trivial-fibre deterministic systems on
-- Fin (n-at m), with n-at m = suc (suc m). Their coinductive limit L∞ is
-- the trivial-fibre system on ℕ. The ONLY real datum is the deterministic
-- position transition.
--
-- The position axis is eliminated AT THE DEFINING SITE:
--
--   * The limit transition at position v is read from stage v itself:
--       s∞ v = toℕ (t v (natToFin v)).
--     Stage v has n-at v = suc (suc v) > v positions, so natToFin v is
--     ALWAYS in range. There is no out-of-range case, hence no partial
--     defaultFin / finFromℕ-maybe, no "sufficiently large layer"
--     threshold and no ≤-total split — the three devices that, in
--     WIP.agda, buried the guarded recursion under E1…E5 transports.
--
--   * natToFin v is the canonical in-range representative (toℕ = v),
--     defined here self-containedly by ℕ recursion (no Fin indexed
--     pattern match, so it is Cubical-Agda transport-safe).
--
-- The coinductive orbit (the deterministic tree over L∞) is written in
-- edge-indexed style: below y e = orbit y. The child index y is carried
-- BY THE EDGE e; we recurse at y directly, never matching the successor
-- equation inside e and never transporting. For the trivial fibre there
-- is exactly one such y (y ≡ s∞ x).
--
-- This slice fixes L∞ and its orbit. In-range projection coherence (the
-- stage-m reading commuting with s∞ for positions present at stage m) and
-- the bisimulation cone / uniqueness are added in following slices.
--
-- FinCat 塔的携带式极限系统 —— 存在性核心（零 subst）。
--
-- 有限层是 Fin (n-at m) 上的平凡纤维确定性系统，n-at m = suc (suc m)。
-- 其余归纳极限 L∞ 是 ℕ 上的平凡纤维系统；唯一真实数据是确定性位置转移。
--
-- 位置轴在定义点即被消除：
--
--   * 位置 v 处的极限转移直接从第 v 层读取：
--       s∞ v = toℕ (t v (natToFin v))。
--     第 v 层有 n-at v = suc (suc v) > v 个位置，故 natToFin v 永远在范
--     围内。没有越界情形，因而没有偏函数 defaultFin / finFromℕ-maybe、
--     没有"足够大层"阈值、没有 ≤-total 情形划分 —— 正是这三样东西在
--     WIP.agda 里把受保护递归掩埋在 E1…E5 传输之下。
--
--   * natToFin v 是典范的范围内代表（toℕ = v），在此自包含地以 ℕ 递归
--     定义（不对 Fin 做索引模式匹配，对 Cubical Agda 传输安全）。
--
-- 余归纳轨道（L∞ 上的确定性树）以边索引风格书写：below y e = orbit y。
-- 子索引 y 由边 e 携带；直接在 y 处递归，绝不匹配 e 内的后继等式，绝不
-- 传输。平凡纤维下恰有一个这样的 y（y ≡ s∞ x）。
--
-- 本切片固定 L∞ 与其轨道。范围内投影相干性（第 m 层读数对该层存在位置
-- 与 s∞ 交换）及互模拟余锥 / 唯一性在后续切片补齐。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.Carried.LimitSystem where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import ALMA.Base.MCorr using (here; below)
open import ALMA.Cosmos.Carried.DetSys

-- Size of the object set of FinCatN m: n-at m = suc (suc m).
--
-- FinCatN m 对象集的大小：n-at m = suc (suc m)。
n-at : ℕ → ℕ
n-at m = suc (suc m)

-- The canonical representative of natural position v in stage v.
-- natToFin v : Fin (n-at v), and n-at v > v, so it is always in range.
--
-- 自然位置 v 在第 v 层的典范代表。natToFin v : Fin (n-at v)，且
-- n-at v > v，故永远在范围内。
natToFin : (v : ℕ) → Fin (n-at v)
natToFin zero    = zero
natToFin (suc v) = suc (natToFin v)

-- toℕ (natToFin v) ≡ v, by ℕ recursion only.
--
-- toℕ (natToFin v) ≡ v，仅对 ℕ 递归。
toℕ-natToFin : (v : ℕ) → toℕ (natToFin v) ≡ v
toℕ-natToFin zero    = refl
toℕ-natToFin (suc v) = cong suc (toℕ-natToFin v)

------------------------------------------------------------------------
-- The limit system, parameterised by the per-stage deterministic
-- position transition t m : Fin (n-at m) → Fin (n-at m).
--
-- 极限系统，以各层确定性位置转移 t m : Fin (n-at m) → Fin (n-at m)
-- 为参数。
------------------------------------------------------------------------
module LimitSystem
  (t : (m : ℕ) → Fin (n-at m) → Fin (n-at m))
  where

  -- Limit position transition: read at the stage that always contains v.
  --
  -- 极限位置转移：在永远包含 v 的第 v 层读取。
  s∞ : ℕ → ℕ
  s∞ v = toℕ (t v (natToFin v))

  -- L∞ is the trivial-fibre deterministic system on ℕ with transition s∞.
  --
  -- L∞ 是 ℕ 上以 s∞ 为转移的平凡纤维确定性系统。
  open TrivDet ℕ s∞
    using (sys; E; DetM)

  L∞ = sys

  -- Coinductive orbit of the deterministic limit dynamics. In
  -- edge-indexed form the child index y is carried by e, so the
  -- continuation is orbit y — no successor equation is matched and no
  -- transport is needed. The call is guarded directly by `below`.
  --
  -- 确定性极限动力学的余归纳轨道。边索引形式下子索引 y 由 e 携带，故
  -- 连续项就是 orbit y —— 不匹配后继等式、无需传输。递归调用直接由
  -- below 保护。
  orbit∞ : (x : ℕ) → DetM x
  orbit∞ x .here      = tt
  orbit∞ x .below y _ = orbit∞ y
