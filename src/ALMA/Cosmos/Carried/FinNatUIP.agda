------------------------------------------------------------------------
-- UIP for the discrete position index types ℕ and Fin n.
--
-- The carried surjective projection (SurjProj) asks for UIP on its two
-- index types, because the deterministic edge fibres are index-equality
-- propositions and the FiberAdj round-trips relate two proofs of the
-- SAME equality. ℕ and Fin n both carry decidable equality, hence UIP
-- constructively by Hedberg's theorem (dec⇒UIP) — this does NOT invoke
-- axiom K and stays --safe / --cubical-compatible.
--
-- This is the glue that instantiates SurjProj for the limit index ℕ and
-- the finite stage indices Fin (n-at m); general non-discrete fibres
-- remain out of scope.
--
-- 离散位置索引类型 ℕ 与 Fin n 的 UIP。
-- 携带式满射投影（SurjProj）要求两个索引类型具备 UIP，因为确定性边纤维
-- 是索引等式命题，FiberAdj 往返律联系同一等式的两份证明。ℕ 与 Fin n 都带
-- 可判定等式，故由 Hedberg 定理（dec⇒UIP）构造性地有 UIP —— 这不调用
-- 公理 K，仍为 --safe / --cubical-compatible。
--
-- 这是把 SurjProj 实例化到极限索引 ℕ 与有限层索引 Fin (n-at m) 的胶合
-- 模块；一般非离散纤维不在范围内。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --double-check #-}
module ALMA.Cosmos.Carried.FinNatUIP where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

import Data.Nat.Properties
import Data.Fin.Properties

open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import ALMA.Cosmos.Carried.DecUIP using (dec⇒UIP)

-- UIP for natural numbers.
--
-- 自然数的 UIP。
natUIP : UIP ℕ
natUIP = dec⇒UIP Data.Nat.Properties._≟_

-- UIP for finite sets.
--
-- 有限集的 UIP。
finUIP : ∀ {n} → UIP (Fin n)
finUIP {n} = dec⇒UIP (Data.Fin.Properties._≟_ {n = n})
