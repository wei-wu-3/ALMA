------------------------------------------------------------------------
-- FinEmbed: total, zero-subst one-step embedding of a finite endofunction
--
-- The old FinCatInfinityTowerCompat built the one-step stage embedding
-- with the partial finFromℕ-maybe (a Maybe-returning decoder) plus
-- restrictFin (which collapsed the new element to fzero), and then proved
-- ~80 lines of bookkeeping (embedF₀-on-inject₁ / on-new, restrictFin-*,
-- extendFin-embedF₀, restrictFin-defaultFin) carrying five explicit
-- subst. Here the embedding is a TOTAL function. Split the bounded
-- reading toℕ x' ≤ n-at m with the recursive sum m≤n⇒m<n∨m≡n (the same
-- Cubical-safe split used by FinColimit.at-cl; decidable equality is
-- avoided because its Bool-backed pattern triggers UnsupportedIndexedMatch
-- under --cubical-compatible):
--
--   embedF f x' with m≤n⇒m<n∨m≡n (toℕ<n x')
--     | inj₂ _   = x'                                 -- the new top, fixed
--     | inj₁ lt  = inject₁ (f (lower₁ x' (neq-< lt))) -- inherited element
--
-- On the inject₁ image the lemma embedF-inject₁ follows directly from the
-- stdlib round-trip lower₁-inject₁ (with lower₁-irrelevant aligning the
-- inequality proof): no clamp, no toℕ-size inference, no subst, and no
-- Cubical-unsupported match. The cone compatibility required by FinTower
-- lives entirely on this image (the new top is handled by FinColimit.at-cl),
-- so no predecessor / restrictFin is ever needed.
--
-- FinEmbed：有限自函数一步嵌入的全函数、零 subst 版本
--
-- 旧 FinCatInfinityTowerCompat 用偏函数 finFromℕ-maybe（返回 Maybe 的
-- 解码器）与 restrictFin（把新元素塌成 fzero）构造一步层嵌入，再证约
-- 80 行簿记（embedF₀-on-inject₁ / on-new、restrictFin-*、
-- extendFin-embedF₀、restrictFin-defaultFin），其中含五处显式 subst。
-- 这里嵌入是全函数：用递归和式 m≤n⇒m<n∨m≡n 拆分有界读数
-- toℕ x' ≤ n-at m（即 FinColimit.at-cl 所用的同一 Cubical 安全拆分；
-- 不用可判定相等，因其 Bool 支撑的模式在 --cubical-compatible 下触发
-- UnsupportedIndexedMatch）：
--
--   embedF f x' with m≤n⇒m<n∨m≡n (toℕ<n x')
--     | inj₂ _   = x'                                 -- 新末位，固定
--     | inj₁ lt  = inject₁ (f (lower₁ x' (neq-< lt))) -- 继承元素
--
-- 在 inject₁ 像上，引理 embedF-inject₁ 直接由标准库往返 lower₁-inject₁
-- （用 lower₁-irrelevant 对齐不等式证明）得到：无 clamp、无 toℕ 尺寸
-- 推断、无 subst，也无 Cubical 不支持的模式匹配。FinTower 所需的锥相
-- 容性完全位于该像上（新末位由 FinColimit.at-cl 处理），故根本不需要
-- 前驱 / restrictFin。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.Carried.FinEmbed where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties
  using (≤-pred; >⇒≢; m≤n⇒m<n∨m≡n)
open import Data.Fin.Base using (Fin; inject₁; lower₁; toℕ)
open import Data.Fin.Properties
  using (toℕ<n; toℕ-inject₁; toℕ-inject₁-≢;
         lower₁-inject₁; lower₁-irrelevant)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (cong; sym; trans; _≢_)

open import ALMA.Cosmos.Carried.LimitSystem using (n-at)

private
  -- A strict reading k < n (equivalently n > k) witnesses n ≢ k, directly
  -- by the stdlib lemma >⇒≢. No rewrite, no subst, Cubical-safe.
  --
  -- 严格读数 k < n（等价于 n > k）直接由标准库引理 >⇒≢ 给出 n ≢ k。
  -- 无 rewrite、无 subst，Cubical 安全。
  neq-< : ∀ {k n : ℕ} → k < n → n ≢ k
  neq-< lt = >⇒≢ lt

------------------------------------------------------------------------
-- Total one-step embedding of an endofunction at stage m.
--
-- 第 m 层自函数的全函数一步嵌入。
------------------------------------------------------------------------
embedF : ∀ {m}
       → (Fin (n-at m) → Fin (n-at m))
       → Fin (n-at (suc m)) → Fin (n-at (suc m))
embedF {m} f x'
  with m≤n⇒m<n∨m≡n (≤-pred (toℕ<n x'))
... | inj₂ _   = x'
... | inj₁ lt  = inject₁ (f (lower₁ {n = n-at m} x' (neq-< lt)))

private
  -- The new-top case cannot occur at inject₁ x: its natural reading is
  -- strictly below n-at m, while the branch equates it with n-at m.
  --
  -- inject₁ x 处不可能走到新末位分支：其自然读数严格小于 n-at m，而该
  -- 分支却把它等同于 n-at m。
  new-top-absurd : ∀ {m} (x : Fin (n-at m))
                 → toℕ (inject₁ x) ≡ n-at m → ⊥
  new-top-absurd {m} x eq =
    neq-< (toℕ<n x) (trans (sym eq) (toℕ-inject₁ {n = n-at m} x))

------------------------------------------------------------------------
-- On the inject₁ image, embedF acts as inject₁ after f.
--
-- 在 inject₁ 像上，embedF 等于先 f 再 inject₁。
------------------------------------------------------------------------
embedF-inject₁ : ∀ {m} (f : Fin (n-at m) → Fin (n-at m))
               (x : Fin (n-at m))
               → embedF f (inject₁ x) ≡ inject₁ (f x)
embedF-inject₁ {m} f x
  with m≤n⇒m<n∨m≡n (≤-pred (toℕ<n (inject₁ x)))
... | inj₂ eq = ⊥-elim (new-top-absurd x eq)
... | inj₁ lt =
  cong inject₁ (cong f
    (trans
      (lower₁-irrelevant {n = n-at m} (inject₁ x)
                          (neq-< lt)
                          (toℕ-inject₁-≢ {n = n-at m} x))
      (lower₁-inject₁ {n = n-at m} x)))

------------------------------------------------------------------------
-- Reading the embedded result back as a natural number on the image.
-- This is the one-step cone coherence shape used by FinTower.
--
-- 把像上的嵌入结果读回自然数。这正是 FinTower 所用的一步锥相干形状。
------------------------------------------------------------------------
toℕ-embedF-inject₁ : ∀ {m} (f : Fin (n-at m) → Fin (n-at m))
                    (x : Fin (n-at m))
                    → toℕ (embedF f (inject₁ x)) ≡ toℕ (f x)
toℕ-embedF-inject₁ {m} f x
  rewrite embedF-inject₁ f x = toℕ-inject₁ {n = n-at m} (f x)
