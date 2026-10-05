------------------------------------------------------------------------
-- Boundaries: machine-checked NEGATIVE results for the carried FinCat
-- colimit (zero subst).
--
-- The reconstruction is guided by two negative facts that were learned
-- the hard way in WIP.agda. Until now they were only prose conclusions;
-- this module turns the OBJECT-LEVEL ones (class A — statements that can
-- be expressed and proved inside Agda) into checked negations, so the
-- architecture cannot silently regress:
--
--   (1) inject₁ is injective but NOT surjective: the new top of
--       Fin (n-at (suc m)) has no preimage in Fin (n-at m). Hence the
--       finite-stage embedding cannot be a child-total map covering the
--       whole limit.
--
--   (2) Every carried FMap has a surjective index map: childF asks for a
--       source preimage of EVERY target index. Therefore there is NO
--       FMap between consecutive trivial stages whose index map is
--       inject₁ — (1) makes the required preimage of the new top
--       impossible. This is the machine-checked form of "a global
--       projection FMap does not exist; legs must be the forward,
--       non-total PushSim, never a child-surjective FMap".
--
--   (3) The total clamp SATURATES: it sends two distinct naturals
--       (suc k and suc (suc k)) to the same Fin top. It is not injective,
--       so it cannot be used as the position embedding; out-of-range
--       positions must be left to the identity leg reading, never
--       clamped onto the last slot.
--
-- Every proof is a homogeneous contradiction on natural-number readings
-- (toℕ), closed by 1+n≰n / n≢1+n. There is no subst, no cast, no Maybe,
-- no Cubical absurd pattern.
--
-- The meta-theoretic boundaries (class B2: global UIP is independent and
-- needs a univalent/HIT counter-model not available here; class C: the
-- compiler's --cubical-compatible unification restrictions) cannot be
-- STATED as negations in this development and live in the design notes,
-- not here. The usable UIP boundary is the POSITIVE conditional theorem
-- DecUIP.dec⇒UIP (decidable equality ⇒ UIP), consumed via the explicit
-- uipI / uipJ parameters of TrivProj.SurjProj.
--
-- Boundaries：携带式 FinCat 余极限的机检否定结果（零 subst）。
--
-- 重构由两条在 WIP.agda 中以沉重代价得到的否定事实引导。此前它们只是
-- 文字结论；本模块把其中对象层（A 类——可在 Agda 内陈述并证明者）变为
-- 受检否定，使架构无法悄悄回退：
--
--   (1) inject₁ 单射但非满射：Fin (n-at (suc m)) 的新末位在
--       Fin (n-at m) 中无原像。故有限层嵌入不可能是覆盖整个极限的子节
--       点满映射。
--
--   (2) 每个携带式 FMap 的索引映射必满：childF 对每个目标索引都要求一个
--       源原像。因此相邻平凡层之间不存在索引映射为 inject₁ 的 FMap ——
--       (1) 使新末位所需原像不可能。这是"全局投影 FMap 不存在；腿必须
--       是前向、非满的 PushSim，绝不能是子节点满的 FMap"的机检形式。
--
--   (3) 全函数 clamp 会饱和：它把两个不同自然数（suc k 与 suc (suc k)）
--       送到同一 Fin 末位，故非单射，不能用作位置嵌入；越界位置必须交
--       给恒等腿读数，绝不 clamp 到末位。
--
-- 每个证明都是自然数读数（toℕ）上的同质矛盾，由 1+n≰n / n≢1+n 闭合。
-- 无 subst、无 cast、无 Maybe、无 Cubical 空模式。
--
-- 元理论边界（B2：全局 UIP 独立、需此处不具备的 univalence/HIT 反模型；
-- C：编译器 --cubical-compatible 归一化限制）无法在本开发中作为否定陈
-- 述，见于设计注释而非此处。可用的 UIP 边界是肯定的条件定理
-- DecUIP.dec⇒UIP（可判定等式 ⇒ UIP），经 TrivProj.SurjProj 的显式
-- uipI / uipJ 参数消费。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.Carried.Boundaries where

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (_×_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties
  using ( ≤-refl; <⇒≢; n<1+n; suc-injective
        ; m≤n⇒m≤1+n; m≥n⇒m⊓n≡n; ⊓-comm )
open import Data.Fin.Base using (Fin; zero; toℕ; inject₁; fromℕ)
open import Data.Fin.Properties
  using (toℕ<n; toℕ-inject₁; toℕ-fromℕ; toℕ-injective)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import ALMA.Base.MCorr using (Sys; FMap)
open Sys
open import ALMA.Cosmos.Carried.DetSys
open import ALMA.Cosmos.Carried.LimitSystem using (n-at)
open import ALMA.Cosmos.Carried.FinProj using (clamp; clamp-val)

------------------------------------------------------------------------
-- Surjectivity of a plain function.
--
-- 普通函数的满射性。
------------------------------------------------------------------------
Surjective : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Surjective f = ∀ y → Σ _ λ x → f x ≡ y

------------------------------------------------------------------------
-- (1) The new top has no preimage under inject₁.
--
-- Any inject₁ x reads toℕ x ≤ suc m, while the new top reads
-- n-at m = suc (suc m); equating them forces suc (suc m) ≤ suc m,
-- contradicted by 1+n≰n.
--
-- (1) 新末位在 inject₁ 下无原像。
-- 任何 inject₁ x 的读数 toℕ x ≤ suc m，而新末位读数
-- n-at m = suc (suc m)；令二者相等会迫使 suc (suc m) ≤ suc m，
-- 与 1+n≰n 矛盾。
------------------------------------------------------------------------
inject₁-top-⊥ : ∀ (m : ℕ) (x : Fin (n-at m))
  → inject₁ x ≡ fromℕ (n-at m) → ⊥
inject₁-top-⊥ m x eq = <⇒≢ (toℕ<n x) eq2
  where
    -- The claimed equality forces toℕ x ≡ n-at m, while x being a
    -- position of stage m gives toℕ x < n-at m; <⇒≢ is irreflexivity
    -- as a function of the equality (no rewrite, no dependent cast).
    --
    -- 所声称的等式迫使 toℕ x ≡ n-at m，而 x 是第 m 层位置给出
    -- toℕ x < n-at m；<⇒≢ 即以等式为参数的反自反性（无 rewrite、无
    -- 依赖 cast）。
    eq2 : toℕ x ≡ n-at m
    eq2 = trans (sym (toℕ-inject₁ x))
                (trans (cong toℕ eq) (toℕ-fromℕ (n-at m)))

-- inject₁ from stage m into stage suc m is not surjective.
--
-- 从第 m 层到第 suc m 层的 inject₁ 非满射。
inject₁-notSurj : ∀ (m : ℕ)
  → ¬ Surjective (inject₁ {n = n-at m})
inject₁-notSurj m surj with surj (fromℕ (n-at m))
... | x , eq = inject₁-top-⊥ m x eq

------------------------------------------------------------------------
-- (2) Every FMap has a surjective index map.
--
-- childF is total over the target index v and returns a source index x'
-- together with the graph witness u x' ≡ v; that is exactly a chosen
-- preimage of v. A pointed source (some x₀ with a label a₀) suffices.
--
-- (2) 每个 FMap 的索引映射都满。
-- childF 对目标索引 v 满，返回源索引 x' 与图见证 u x' ≡ v；这恰是 v 的
-- 一个选定原像。只需源端带点（某个 x₀ 及其标签 a₀）。
------------------------------------------------------------------------
FMap-u-surjective
  : ∀ {i j a b c d} {X : Sys i a b} {Y : Sys j c d}
  → (f : FMap X Y) (x₀ : I X) (a₀ : A X x₀)
  → Surjective (FMap.u f)
FMap-u-surjective f x₀ a₀ v = FMap.childF f x₀ a₀ v

-- There is no FMap between consecutive trivial stages whose index map
-- is inject₁: childF would have to supply a preimage of the new top,
-- which (1) says is impossible.
--
-- 相邻平凡层之间不存在索引映射为 inject₁ 的 FMap：childF 必须为新末位
-- 提供原像，而 (1) 表明这不可能。
module _ (m : ℕ)
         (tm : Fin (n-at m) → Fin (n-at m))
         (ts : Fin (n-at (suc m)) → Fin (n-at (suc m)))
         where
  private
    module Src = TrivDet {i = lzero} (Fin (n-at m)) tm
    module Tgt = TrivDet {i = lzero} (Fin (n-at (suc m))) ts

  no-inject₁-FMap
    : ¬ Σ (FMap Src.sys Tgt.sys)
        λ f → ∀ x → FMap.u f x ≡ inject₁ x
  no-inject₁-FMap (f , eu)
    with FMap.childF f zero (tt {lzero}) (fromℕ (n-at m))
  ... | x' , r = inject₁-top-⊥ m x' (trans (sym (eu x')) r)

------------------------------------------------------------------------
-- (3) clamp saturates and is therefore not injective.
--
-- Above the bound k, clamp {k} reads to the minimum k ⊓ x = k, so it
-- fixes every out-of-range input to the top fromℕ k. In particular the
-- two distinct naturals suc k and suc (suc k) collapse to the same
-- element. clamp can be a total finite PROJECTION (it has the section
-- toℕ in range), but it cannot be the position EMBEDDING.
--
-- (3) clamp 饱和，因而非单射。
-- 越过界 k 后，clamp {k} 的读数为最小值 k ⊓ x = k，故每个越界输入都被
-- 固定为末位 fromℕ k。特别地，两个不同自然数 suc k 与 suc (suc k) 坍缩
-- 为同一元素。clamp 可作全函数有限投影（范围内有截面 toℕ），但不能作
-- 位置嵌入。
------------------------------------------------------------------------
private
  -- clamp {k} fixes every x ≥ k to the top fromℕ k.
  --
  -- clamp {k} 把每个 x ≥ k 固定为末位 fromℕ k。
  clamp-is-top : ∀ (k x : ℕ) (ge : k ≤ x) → clamp {k = k} x ≡ fromℕ k
  clamp-is-top k x ge =
    toℕ-injective
      (trans (clamp-val x)
        (trans (⊓-comm k x)
          (trans (m≥n⇒m⊓n≡n {m = x} {n = k} ge)
                 (sym (toℕ-fromℕ k)))))

-- Two distinct naturals that clamp identifies.
--
-- 被 clamp 等同的两个不同自然数。
clamp-collapses : ∀ (k : ℕ)
  → Σ ℕ λ x → Σ ℕ λ y
    → (x ≡ y → ⊥) × (clamp {k = k} x ≡ clamp {k = k} y)
clamp-collapses k =
  suc k , suc (suc k) , (neq , eq)
  where
    -- n ≡ suc n is impossible: n<1+n gives n < suc n and <⇒≢ is
    -- irreflexivity as a function of the equality.
    --
    -- n ≡ suc n 不可能：n<1+n 给 n < suc n，<⇒≢ 即以等式为参数的反
    -- 自反性。
    neq-refl : ∀ n → n ≡ suc n → ⊥
    neq-refl n e' = <⇒≢ (n<1+n n) e'

    neq : suc k ≡ suc (suc k) → ⊥
    neq e = neq-refl k (suc-injective e)

    eq : clamp {k = k} (suc k) ≡ clamp {k = k} (suc (suc k))
    eq =
      trans
        (clamp-is-top k (suc k)
          (m≤n⇒m≤1+n ≤-refl))
        (sym (clamp-is-top k (suc (suc k))
          (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl))))
