------------------------------------------------------------------------
-- Hedberg's theorem: decidable equality implies UIP (self-contained).
--
-- The carried surjective projection (SurjProj) asks for UIP on its
-- discrete index types. The standard library's nested module
-- Decidable⇒UIP is not re-exported by this installation's
-- Axiom.UniquenessOfIdentityProofs interface, so we reconstruct the
-- one-line Hedberg argument here from top-level primitives only:
-- recompute / recompute-constant (the decision procedure yields a
-- constant normaliser of equality proofs) and trans-symˡ.
--
-- This is constructive (no axiom K), --safe / --cubical-compatible; it
-- is the legitimate UIP available for types with decidable equality
-- (ℕ, Fin n). A plain function is exported (not a nested parameterised
-- module) to sidestep the re-export issue.
--
-- Hedberg 定理：可判定等式蕴含 UIP（自包含）。
-- 携带式满射投影（SurjProj）要求离散索引类型具备 UIP。本安装的
-- Axiom.UniquenessOfIdentityProofs 接口未再导出嵌套模块 Decidable⇒UIP，
-- 故这里仅用顶层原语重建这一行 Hedberg 论证：recompute /
-- recompile-constant（判定过程给出等式证明的常数规范化子）与
-- trans-symˡ。
--
-- 这是构造性的（不用公理 K），--safe / --cubical-compatible；它是具备
-- 可判定等式的类型（ℕ、Fin n）可合法获得的 UIP。这里导出普通函数（而非
-- 嵌套参数化模块），以绕开再导出问题。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --double-check #-}
module ALMA.Cosmos.Carried.DecUIP where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Core using (sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (trans-symˡ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable.Core using (recompute; recompute-constant)
open import Axiom.UniquenessOfIdentityProofs using (UIP)

-- Decidable equality on A gives UIP for A.
--
-- A 上的可判定等式给出 A 的 UIP。
dec⇒UIP : ∀ {a : Level} {A : Set a} → DecidableEquality A → UIP A
dec⇒UIP {A = A} _≟_ = irrelev
  where
    -- The decision procedure normalises every equality proof to a
    -- canonical one; this normaliser is constant in its input.
    --
    -- 判定过程把每条等式证明规范化为一个规范证明；该规范化子对输入为
    -- 常数。
    norm : ∀ {x y : A} → x ≡ y → x ≡ y
    norm {x = x} {y = y} p = recompute (x ≟ y) p

    norm-const : ∀ {x y : A} (p q : x ≡ y) → norm p ≡ norm q
    norm-const {x = x} {y = y} = recompute-constant (x ≟ y)

    -- Every proof equals the canonical normalised proof.
    --
    -- 每条证明都等于规范的规范化证明。
    canon : ∀ {x y : A} (p : x ≡ y)
          → trans (sym (norm refl)) (norm p) ≡ p
    canon refl = trans-symˡ (norm refl)

    irrelev : UIP A
    irrelev p q =
      trans (sym (canon p))
        (trans (cong (trans (sym (norm refl))) (norm-const p q))
               (canon q))
