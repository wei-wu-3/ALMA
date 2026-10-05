------------------------------------------------------------------------
-- FinTower: zero-subst colimit of a tower of finite endofunctions
--
-- A tower is a family f m : Fin (n-at m) → Fin (n-at m) together with the
-- one-step coherence that reading one stage up through inject₁ agrees:
--
--   toℕ (f (suc m) (inject₁ x)) ≡ toℕ (f m x).
--
-- This is exactly the Set-level content formerly encoded in
-- FinCatInfinityColimit by the partial extendFin / defaultFin machine and
-- the two-way ≤-total lemma extendFin-layer-independent (which carried
-- six subst). Here the whole colimit is just a FinCone over ℕ:
--
--   at m x = toℕ (f m x),   compat = the supplied one-step coherence,
--
-- and FinCone derives at-cl / g∞ / extends / unique with ZERO subst. The
-- canonical reading g∞ k = toℕ (f k (natToFin k)) is the F₀ of the tower
-- colimit, and unique is its Set-level universal property.
--
-- The fibre of the FinCat tower is the lifted unit (trivial deterministic
-- case), so the Cosmos-level bisimulation uniqueness is carried separately
-- by LimitSystem.det-unique; this module fixes only the position axis.
--
-- FinTower：有限自函数塔的零 subst 余极限
--
-- 一个塔即一族 f m : Fin (n-at m) → Fin (n-at m)，附带一步相干性：经
-- inject₁ 上读一层一致：
--
--   toℕ (f (suc m) (inject₁ x)) ≡ toℕ (f m x)。
--
-- 这正是先前 FinCatInfinityColimit 中用偏函数 extendFin / defaultFin
-- 机器与双向 ≤-total 引理 extendFin-layer-independent（含六处 subst）
-- 编码的 Set 层内容。这里整个余极限就是 ℕ 上的一个 FinCone：
--
--   at m x = toℕ (f m x)，compat = 所给的一步相干性，
--
-- 而 FinCone 零 subst 地派生出 at-cl / g∞ / extends / unique。典范读数
-- g∞ k = toℕ (f k (natToFin k)) 即塔余极限的 F₀，unique 即其 Set 层泛
-- 性质。
--
-- FinCat 塔的纤维是提升的单位（平凡确定性情形），故 Cosmos 层互模拟
-- 唯一性由 LimitSystem.det-unique 另行携带；本模块只固定位置轴。
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible --guardedness --exact-split --double-check #-}
module ALMA.Cosmos.Carried.FinTower where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (ℕ; suc)
open import Data.Fin.Base using (Fin; toℕ; inject₁)

open import ALMA.Cosmos.Carried.LimitSystem using (n-at; natToFin)
open import ALMA.Cosmos.Carried.FinColimit using (FinCone)

------------------------------------------------------------------------
-- The cone of a tower of finite endofunctions.
--
-- 有限自函数塔的锥。
------------------------------------------------------------------------
finTowerCone
  : (f : ∀ m → Fin (n-at m) → Fin (n-at m))
  → (embed-compat : ∀ m (x : Fin (n-at m))
       → toℕ (f (suc m) (inject₁ x)) ≡ toℕ (f m x))
  → FinCone ℕ
finTowerCone f embed-compat = record
  { at     = λ m x → toℕ (f m x)
  ; compat = embed-compat
  }

------------------------------------------------------------------------
-- Convenience wrapper: opens the full cone surface (at-cl, g∞, extends,
-- unique) for a given tower, so the Cosmos-level colimit only has to
-- supply the one-step coherence.
--
-- 便捷包装：为给定塔打开完整锥表面（at-cl、g∞、extends、unique），故
-- Cosmos 层余极限只需提供一步相干性。
------------------------------------------------------------------------
module FinTower
  (f : ∀ m → Fin (n-at m) → Fin (n-at m))
  (embed-compat : ∀ m (x : Fin (n-at m))
       → toℕ (f (suc m) (inject₁ x)) ≡ toℕ (f m x))
  where

  cone : FinCone ℕ
  cone = finTowerCone f embed-compat

  open FinCone cone public
    using (at; compat; compat-emb; at-cl; g∞; extends; unique)
