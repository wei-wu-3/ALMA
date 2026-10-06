------------------------------------------------------------------------
-- Machine-checked negative results for the carried FinCat colimit
-- (zero subst). Three object-level boundaries that were previously
-- prose-only conclusions:
--
--   (1) inject₁ is injective but not surjective: the new top of
--       Fin (n-at (suc m)) has no preimage in Fin (n-at m).
--   (2) Every carried FMap has a surjective index map, since childF
--       asks for a source preimage of every target index; hence no
--       FMap between consecutive trivial stages has index map inject₁.
--   (3) The total clamp saturates: suc k and suc (suc k) map to the
--       same Fin top, so it is not injective.
--
-- Every proof is a homogeneous contradiction on ℕ readings (toℕ),
-- closed by 1+n≰n / n≢1+n. No subst, no cast, no Maybe, no Cubical
-- absurd pattern.
--
-- The meta-theoretic boundaries (class B2: global UIP is independent;
-- class C: --cubical-compatible unification restrictions) cannot be
-- stated as negations here and live in the design notes. The usable
-- UIP boundary is the positive conditional DecUIP.dec⇒UIP, consumed
-- via the explicit uipI / uipJ parameters of TrivProj.SurjProj.
--
-- 携带式 FinCat 余极限的机检否定结果（零 subst）。三条对象层边界：
--
--   (1) inject₁ 单射但非满射：Fin (n-at (suc m)) 的新末位在
--       Fin (n-at m) 中无原像。
--   (2) 每个携带式 FMap 的索引映射必满，因 childF 对每个目标索引
--       都要求源原像；故相邻平凡层之间不存在索引映射为 inject₁ 的
--       FMap。
--   (3) 全函数 clamp 饱和：suc k 与 suc (suc k) 送到同一 Fin 末位，
--       故非单射。
--
-- 每个证明都是 toℕ 上的同质矛盾，由 1+n≰n / n≢1+n 闭合。无 subst、
-- 无 cast、无 Maybe、无 Cubical 空模式。
--
-- 元理论边界（B2：全局 UIP 独立；C：--cubical-compatible 归一化
-- 限制）无法在此作为否定陈述，见于设计注释。可用的 UIP 边界是肯定
-- 的条件定理 DecUIP.dec⇒UIP，经 TrivProj.SurjProj 的显式
-- uipI / uipJ 参数消费。
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Cosmos.Carried.Boundaries where

open import Agda.Primitive using (Level; lzero; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties
  using (≤-refl; <⇒≢; n<1+n; suc-injective; m≤n⇒m≤1+n; m≥n⇒m⊓n≡n; ⊓-comm)
open import Data.Fin.Base using (Fin; zero; toℕ; inject₁; fromℕ)
open import Data.Fin.Properties
  using (toℕ<n; toℕ-inject₁; toℕ-fromℕ; toℕ-injective)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans; sym)
open import Relation.Nullary.Negation using (¬_)

open import ALMA.Base.MCorr using (Sys; FMap)
open Sys
open import ALMA.Cosmos.Carried.DetSys
open import ALMA.Cosmos.Carried.LimitSystem using (n-at)
open import ALMA.Cosmos.Carried.FinProj using (clamp; clamp-val)

------------------------------------------------------------------------
-- Surjectivity of a plain function
-- 普通函数的满射性

Surjective : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
Surjective f = ∀ y → Σ _ λ x → f x ≡ y

------------------------------------------------------------------------
-- (1) The new top has no preimage under inject₁
-- The claimed equality forces toℕ x ≡ n-at m, while x being a position
-- of stage m gives toℕ x < n-at m; <⇒≢ is irreflexivity as a function
-- of the equality.
-- (1) 新末位在 inject₁ 下无原像
-- 所声称的等式迫使 toℕ x ≡ n-at m，而 x 是第 m 层位置给出
-- toℕ x < n-at m；<⇒≢ 即以等式为参数的反自反性。

inject₁-top-⊥ : ∀ (m : ℕ) (x : Fin (n-at m))
  → inject₁ x ≡ fromℕ (n-at m) → ⊥
inject₁-top-⊥ m x eq = <⇒≢ (toℕ<n x) eq2
  where
    eq2 : toℕ x ≡ n-at m
    eq2 = trans (sym (toℕ-inject₁ x))
                (trans (cong toℕ eq) (toℕ-fromℕ (n-at m)))

inject₁-notSurj : ∀ (m : ℕ)
  → ¬ Surjective (inject₁ {n = n-at m})
inject₁-notSurj m surj with surj (fromℕ (n-at m))
... | x , eq = inject₁-top-⊥ m x eq

------------------------------------------------------------------------
-- (2) Every FMap has a surjective index map
-- childF returns a source index x' together with the graph witness
-- u x' ≡ v, i.e. a chosen preimage of v; a pointed source suffices.
-- (2) 每个 FMap 的索引映射都满
-- childF 返回源索引 x' 与图见证 u x' ≡ v，即 v 的一个选定原像；
-- 只需源端带点。

FMap-u-surjective
  : ∀ {i j a b c d} {X : Sys i a b} {Y : Sys j c d}
  → (f : FMap X Y) (x₀ : I X) (a₀ : A X x₀)
  → Surjective (FMap.u f)
FMap-u-surjective f x₀ a₀ v = FMap.childF f x₀ a₀ v

-- No FMap between consecutive trivial stages has index map inject₁:
-- childF would supply a preimage of the new top, impossible by (1).
-- 相邻平凡层之间不存在索引映射为 inject₁ 的 FMap：childF 必须为新
-- 末位提供原像，而 (1) 表明这不可能。
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
-- (3) clamp saturates and is therefore not injective
-- clamp {k} fixes every x ≥ k to the top fromℕ k.
-- (3) clamp 饱和，因而非单射
-- clamp {k} 把每个 x ≥ k 固定为末位 fromℕ k。

private
  clamp-is-top : ∀ (k x : ℕ) (ge : k ≤ x) → clamp {k = k} x ≡ fromℕ k
  clamp-is-top k x ge =
    toℕ-injective
      (trans (clamp-val x)
        (trans (⊓-comm k x)
          (trans (m≥n⇒m⊓n≡n {m = x} {n = k} ge)
                 (sym (toℕ-fromℕ k)))))

-- Two distinct naturals that clamp identifies.
-- 被 clamp 等同的两个不同自然数。
clamp-collapses : ∀ (k : ℕ)
  → Σ ℕ λ x → Σ ℕ λ y
    → (x ≡ y → ⊥) × (clamp {k = k} x ≡ clamp {k = k} y)
clamp-collapses k =
  suc k , suc (suc k) , (neq , eq)
  where
    -- n ≡ suc n is impossible: n<1+n gives n < suc n, and <⇒≢ is
    -- irreflexivity as a function of the equality.
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
