------------------------------------------------------------------------
-- scale invariance
-- Mathematics: LayeredEqGen has two fields fst (the layer) and snd
-- (the recursion). The LayeredEq specialisation fixes the observation
-- family to be constant; at this position the observation map obs-map
-- is the identity function. ScaleInvariant further trivialises the
-- layer to ⊤, collapsing the layer field. The resulting relation is
-- the coinductive form of scale invariance / transformation invariance
-- / renormalisation-group fixed points
--
-- 尺度不变性
-- 数学内容：LayeredEqGen 有两个字段 fst（当前层）与 snd（递归）。
-- LayeredEq 特化把观察族固定为常数；在该位置观察映射 obs-map
-- 为恒等函数。ScaleInvariant 进一步把 layer 平凡化为 ⊤，使 layer
-- 字段坍缩。所得关系是尺度不变性 / 变换不变性 / 重整化群不动点的
-- 余归纳形式
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.ScaleInvariant where

open import Agda.Primitive using (Level; _⊔_; lzero)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality.Core using (sym; cong; trans)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import ALMA.Base.IndexedMType using (fst; snd)
open import ALMA.Base.Equivalence.Core using (LayeredEq)

------------------------------------------------------------------------
-- degeneration: trivialise layer
-- ScaleInvariant is LayeredEq at the trivial layer ⊤
-- Equivalently: LayeredEqGen at constant observation and layer ⊤
--
-- 退化：把 layer 平凡化
-- ScaleInvariant 是平凡层 ⊤ 处的 LayeredEq
-- 等价地：LayeredEqGen 在常数观察族与 layer = ⊤ 处的特化
------------------------------------------------------------------------
ScaleInvariant
    : {a b : Level} {X : Set a} {Obs : Set b}
      (step : X → Obs → X) (x y : X) → Set b
ScaleInvariant step x y = LayeredEq {c = lzero} _ step (λ _ _ → ⊤) x y

------------------------------------------------------------------------
-- scale invariance and renormalisation-group fixed points
-- Mathematics: a scale transformation scale acts on X and commutes
-- with the evolution step via comm. The commutation law yields that a
-- state x is ScaleInvariant to its scaled image scale x p. The forward
-- direction rewrites the composite step via comm and recurses; no
-- other input is needed
-- An RG fixed point is a state with scale x p ≡ x for all p; comm
-- preserves the fixed-point property along step, so a fixed point
-- satisfies ScaleInvariant x x
--
-- 尺度不变性与重整化群不动点
-- 数学内容：尺度变换 scale 作用于 X，并经 comm 与演化 step 交换。
-- 交换律于是给出状态 x 与尺度像 scale x p 在 ScaleInvariant 意义下
-- 等价。正向经 comm 重写复合 step 并递归；不需要其他输入
-- RG 不动点是对所有 p 满足 scale x p ≡ x 的状态；comm 保证不动点
-- 性质沿 step 保持，故不动点满足 ScaleInvariant x x
------------------------------------------------------------------------
module ScaleInvariance
    {a b s} {X : Set a} {Obs : Set b} {S : Set s}
    (step  : X → Obs → X)
    (scale : X → S → X)
    (comm  : ∀ x ob p → step (scale x p) ob ≡ scale (step x ob) p)
  where

  scale-invariant : ∀ x p → ScaleInvariant step x (scale x p)
  scale-invariant x p .fst = tt
  scale-invariant x p .snd ob
    rewrite comm x ob p = scale-invariant (step x ob) p

  IsFixedPoint : X → Set (a ⊔ s)
  IsFixedPoint x = ∀ p → scale x p ≡ x

  fixed-point-preserved
    : ∀ x → IsFixedPoint x → ∀ ob → IsFixedPoint (step x ob)
  fixed-point-preserved x fp ob p =
    trans (sym (comm x ob p)) (cong (λ z → step z ob) (fp p))

  fixed-point-invariant
    : ∀ x → IsFixedPoint x → ScaleInvariant step x x
  fixed-point-invariant x fp .fst = tt
  fixed-point-invariant x fp .snd ob =
    fixed-point-invariant (step x ob) (fixed-point-preserved x fp ob)
