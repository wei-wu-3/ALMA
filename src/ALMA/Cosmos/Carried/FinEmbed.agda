------------------------------------------------------------------------
-- Total, zero-subst one-step embedding of a finite endofunction. The
-- old construction used a Maybe-returning decoder plus restrictFin and
-- carried five explicit subst across ~80 lines of bookkeeping; here the
-- embedding is total, splitting the bounded reading toℕ x' ≤ n-at m
-- with the recursive sum m≤n⇒m<n∨m≡n (the same Cubical-safe split used
-- by FinColimit.at-cl; decidable equality is avoided because its
-- Bool-backed pattern triggers UnsupportedIndexedMatch under
-- --cubical-compatible):
--
--   embedF f x' with m≤n⇒m<n∨m≡n (toℕ<n x')
--     | inj₂ _   = x'                                 -- new top, fixed
--     | inj₁ lt  = inject₁ (f (lower₁ x' (neq-< lt))) -- inherited
--
-- On the inject₁ image, embedF-inject₁ follows directly from the stdlib
-- round-trip lower₁-inject₁ with lower₁-irrelevant aligning the
-- inequality proof. No clamp, no toℕ-size inference, no subst, and no
-- Cubical-unsupported match; the new top is handled by FinColimit.at-cl,
-- so no predecessor / restrictFin is ever needed.
--
-- 有限自函数一步嵌入的全函数、零 subst 版本。旧构造用偏函数解码器
-- 加 restrictFin，并在约 80 行簿记中含五处显式 subst；这里嵌入是全
-- 函数，用递归和式 m≤n⇒m<n∨m≡n 拆分有界读数 toℕ x' ≤ n-at m（即
-- FinColimit.at-cl 所用的同一 Cubical 安全拆分；不用可判定相等，因其
-- Bool 支撑的模式在 --cubical-compatible 下触发 UnsupportedIndexedMatch）：
--
--   embedF f x' with m≤n⇒m<n∨m≡n (toℕ<n x')
--     | inj₂ _   = x'                                 -- 新末位，固定
--     | inj₁ lt  = inject₁ (f (lower₁ x' (neq-< lt))) -- 继承元素
--
-- 在 inject₁ 像上，embedF-inject₁ 直接由标准库往返 lower₁-inject₁ 用
-- lower₁-irrelevant 对齐不等式证明得到。无 clamp、无 toℕ 尺寸推断、
-- 无 subst、无 Cubical 不支持的模式匹配；新末位由 FinColimit.at-cl
-- 处理，故根本不需要前驱 / restrictFin。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.FinEmbed where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (≤-pred; >⇒≢; m≤n⇒m<n∨m≡n)
open import Data.Fin.Base using (Fin; inject₁; lower₁; toℕ)
open import Data.Fin.Properties
  using (toℕ<n; toℕ-inject₁; toℕ-inject₁-≢; lower₁-inject₁; lower₁-irrelevant)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans; _≢_)

open import ALMA.Cosmos.Carried.LimitSystem using (n-at)

-- A strict reading k < n (equivalently n > k) witnesses n ≢ k, directly
-- by the stdlib lemma >⇒≢.
-- 严格读数 k < n（等价于 n > k）直接由标准库引理 >⇒≢ 给出 n ≢ k。
private
  neq-< : ∀ {k n : ℕ} → k < n → n ≢ k
  neq-< lt = >⇒≢ lt

------------------------------------------------------------------------
-- Total one-step embedding of an endofunction at stage m
-- 第 m 层自函数的全函数一步嵌入

embedF : ∀ {m}
       → (Fin (n-at m) → Fin (n-at m))
       → Fin (n-at (suc m)) → Fin (n-at (suc m))
embedF {m} f x'
  with m≤n⇒m<n∨m≡n (≤-pred (toℕ<n x'))
... | inj₂ _   = x'
... | inj₁ lt  = inject₁ (f (lower₁ {n = n-at m} x' (neq-< lt)))

-- The new-top case cannot occur at inject₁ x: its natural reading is
-- strictly below n-at m, while the branch equates it with n-at m.
-- inject₁ x 处不可能走到新末位分支：其自然读数严格小于 n-at m，而该
-- 分支却把它等同于 n-at m。
private
  new-top-absurd : ∀ {m} (x : Fin (n-at m))
                 → toℕ (inject₁ x) ≡ n-at m → ⊥
  new-top-absurd {m} x eq =
    neq-< (toℕ<n x) (trans (sym eq) (toℕ-inject₁ {n = n-at m} x))

------------------------------------------------------------------------
-- On the inject₁ image, embedF acts as inject₁ after f
-- 在 inject₁ 像上，embedF 等于先 f 再 inject₁

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
-- Reading the embedded result back as a natural number on the image;
-- the one-step cone coherence shape used by FinTower.
-- 把像上的嵌入结果读回自然数；FinTower 所用的一步锥相干形状。

toℕ-embedF-inject₁ : ∀ {m} (f : Fin (n-at m) → Fin (n-at m))
                    (x : Fin (n-at m))
                    → toℕ (embedF f (inject₁ x)) ≡ toℕ (f x)
toℕ-embedF-inject₁ {m} f x
  rewrite embedF-inject₁ f x = toℕ-inject₁ {n = n-at m} (f x)

------------------------------------------------------------------------
-- The new top is fixed by embedF. Stated for an arbitrary element
-- together with its top reading, so the with-abstraction stays abstract
-- (no stuck clamp residual in the generated with function).
-- 新末位被 embedF 固定。对一般元素连同其末位读数陈述，使 with 抽象
-- 保持抽象（生成的 with 函数中不出现卡住的 clamp 残差）。

embedF-newtop : ∀ {m} (f : Fin (n-at m) → Fin (n-at m))
              (x' : Fin (n-at (suc m))) → toℕ x' ≡ n-at m
              → embedF f x' ≡ x'
embedF-newtop {m} f x' e
  with m≤n⇒m<n∨m≡n (≤-pred (toℕ<n x'))
... | inj₂ _   = refl
... | inj₁ lt  = ⊥-elim (>⇒≢ lt (sym e))
