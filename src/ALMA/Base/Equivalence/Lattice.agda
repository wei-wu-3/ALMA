------------------------------------------------------------------------
-- the degeneration lattice of LayeredEqGen
--                    keep next
--                        ↑
--       ScaleInvariant   |   LayeredEqGen
--                        |
--   drop layer ←---------+---------→ keep layer
--                        |
--                        |   DiscreteEq
--                        ↓
--                    drop next
-- LayeredEqGen has two fields: fst (the layer) and snd (the recursion).
-- Keeping or dropping them spans a two-axis parameter space:
-- The records are related by projections, not inclusions: no
-- canonical map back exists in general
--
-- LayeredEqGen 的退化格
--                    保留 next
--                        ↑
--       ScaleInvariant   |   LayeredEqGen
--                        |
--   去掉 layer ←---------+---------→ 保留 layer
--                        |
--                        |   DiscreteEq
--                        ↓
--                    去掉 next
-- LayeredEqGen 有两个字段：fst（当前层）与 snd（递归）。保留或去掉它们
-- 张成一个两轴参数空间。记录之间由投影联系，而非包含：一般不存在反向的典范映射
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}

module ALMA.Base.Equivalence.Lattice where

open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Product.Base using (_×_; _,_)

open import ALMA.Base.IndexedMType using (fst; snd)
open import ALMA.Base.Equivalence.Core using (LayeredEqGen)
open import ALMA.Base.Equivalence.DiscreteEq using (DiscreteEq)
open import ALMA.Base.Equivalence.ScaleInvariant using (ScaleInvariant)

------------------------------------------------------------------------
-- toScale     replaces layer with the trivial layer ⊤, keeps the recursion
-- toDiscrete  drops the recursion, keeps the layer
-- obs-map is fixed to the identity: when the observation family is
-- constant, the map between observations is the identity
--
-- toScale     把 layer 替换为平凡层 ⊤，保留递归
-- toDiscrete  去掉递归，保留 layer
-- obs-map 固定为恒等：当观察族为常数时，观察之间的映射是恒等
module Projections
    {a b c} {X : Set a} {Obs : Set b}
    (step : X → Obs → X)
    (layer : X → X → Set c)
  where

  -- obs-map is constantly the identity because the observation family
  -- (λ _ → Obs) is constant
  --
  -- obs-map 恒为恒等，因为观察族 (λ _ → Obs) 是常数
  obs-map : (x y : X) → layer x y → Obs → Obs
  obs-map _ _ _ o = o

  toScale : ∀ {x y} → LayeredEqGen (λ _ → Obs) (λ x s → step x s)
                                   layer obs-map x y
          → ScaleInvariant step x y
  toScale p .fst = tt
  toScale p .snd s = toScale (p .snd s)

  toDiscrete : ∀ {x y} → LayeredEqGen (λ _ → Obs) (λ x s → step x s)
                                      layer obs-map x y
             → DiscreteEq layer x y
  toDiscrete p = p .fst

------------------------------------------------------------------------
-- toScale keeps the recursion; toDiscrete keeps the layer. Since these
-- are the only two fields of LayeredEqGen, the pair retains the full
-- field content. The converse is not definable in general:
-- DiscreteEq carries only the current layer, with no evidence that
-- layer is preserved by step
--
-- toScale 保留递归；toDiscrete 保留 layer。二者是 LayeredEqGen
-- 仅有的两个字段，因此该对保留全部字段内容。反向构造一般不成立：
-- DiscreteEq 只携带当前层的 layer 证据，不提供「layer 在 step 下保持」的证据
module Pair
    {a b c} {X : Set a} {Obs : Set b}
    (step : X → Obs → X)
    (layer : X → X → Set c)
  where

  open Projections step layer

  toPair : ∀ {x y} → LayeredEqGen (λ _ → Obs) (λ x s → step x s)
                                  layer obs-map x y
         → ScaleInvariant step x y × DiscreteEq layer x y
  toPair p = toScale p , toDiscrete p
